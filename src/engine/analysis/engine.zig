const std = @import("std");
const log = std.log.scoped(.analysis_engine);
const cfg_mod = @import("../../cfg.zig");
const ids = @import("../../ids.zig");
const Cfg = cfg_mod.Cfg;
const CfgNode = cfg_mod.CfgNode;
const EdgeKind = cfg_mod.EdgeKind;
const CfgBuilder = cfg_mod.CfgBuilder;
const cached_artifacts_mod = @import("../../cached_artifacts.zig");
const ast_walk = @import("../../ast_walk.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const AbstractValue = @import("../value.zig").AbstractValue;
const Source = @import("../../source.zig").Source;
const BuildMetadata = @import("../../build_metadata.zig").BuildMetadata;
const assertions = @import("../../assertions.zig");
const TypeContext = @import("../../type_context.zig").TypeContext;
const Config = @import("../../config.zig").Config;
const base = @import("../base.zig");
const EngineError = base.EngineError;
const default_max_inline_depth = base.default_max_inline_depth;
const default_max_worklist_steps = base.default_max_worklist_steps;
const Constraint = @import("../constraints.zig").Constraint;
const CompareOp = @import("../constraints.zig").CompareOp;
const SummaryCache = @import("../summary.zig").SummaryCache;
const ProgramPoint = @import("../state.zig").ProgramPoint;
const ProgramState = @import("../state.zig").ProgramState;
const ErrorState = @import("../state.zig").ErrorState;
const WideningKey = @import("../state.zig").WideningKey;
const ResourceState = @import("../store.zig").ResourceState;
const BindingReplacement = @import("../store.zig").BindingReplacement;
const VarResolver = @import("../var_resolver.zig").VarResolver;
const ExplodedGraph = @import("../graph.zig").ExplodedGraph;
const AstNodeId = ids.AstNodeId;
const CfgNodeId = ids.CfgNodeId;
const CachedArtifacts = cached_artifacts_mod.CachedArtifacts;

const FunctionCfgEntry = struct {
    cfg: *Cfg,
    owned: bool,
};

/// Worklist-based analysis engine.
/// Traverses the CFG and builds an exploded graph with deduplication.
/// Evaluates abstract values for literals and assignments.
/// Applies branch constraints and prunes infeasible paths.
/// Supports interprocedural analysis via function inlining and summaries.
pub const AnalysisEngine = struct {
    allocator: std.mem.Allocator,
    /// The exploded graph being built
    graph: ExplodedGraph,
    /// Worklist of (exploded node index, edge kind from predecessor, optional constraint) pairs to process.
    ///
    /// Items are pushed with `append` and popped with `pop`, i.e. LIFO order, producing a
    /// depth-first traversal of the exploded graph. With widening disabled, state
    /// deduplication in `ExplodedGraph` makes the final fixed point independent of
    /// traversal order; with widening enabled (the default), order can affect precision
    /// because `AbstractValue.widen` is not commutative. DFS is kept regardless: `pop`
    /// is O(1) and recent state stays warm in cache. See `docs/IMPLEMENTATION.md` §
    /// "Worklist algorithm" for the full rationale and the BFS tradeoff.
    worklist: std.ArrayList(WorklistItem),
    /// Count of pruned paths (for testing/debugging)
    pruned_path_count: u32,
    /// Maximum inline depth for interprocedural analysis
    max_inline_depth: u32,
    /// Maximum number of worklist steps before aborting analysis
    max_worklist_steps: usize,
    /// Source file for resolving function calls (optional)
    source: ?*Source,
    /// Cache of built CFGs for functions (by AST node index).
    /// Stores pointers to heap-allocated CFGs for stable addresses that survive
    /// hashmap rehashing.
    function_cfgs: std.AutoHashMap(AstNodeId, FunctionCfgEntry),
    /// Map from function name to AST node index
    function_names: std.StringHashMap(AstNodeId),
    /// Cache of scope-aware variable resolvers per function
    var_resolvers: std.AutoHashMap(AstNodeId, *VarResolver),
    /// Cache of assertion scopes per function
    assertion_scopes: std.AutoHashMap(AstNodeId, assertions.AssertionScope),
    /// Count of inlined calls (for testing/debugging)
    inlined_call_count: u32,
    /// Cache of function summaries for interprocedural analysis
    summary_cache: SummaryCache,
    /// Whether to use summaries instead of inlining when available
    use_summaries: bool,
    /// Count of summary applications (for testing/debugging)
    summary_use_count: u32,
    /// Build metadata (target configuration, etc.) - shared pointer
    build_metadata: ?*const BuildMetadata,
    /// Name of the checker using this engine (for logging).
    /// This is an unowned slice; callers must ensure the underlying data
    /// remains valid for at least as long as this AnalysisEngine instance.
    checker_name: ?[]const u8,
    /// Which per-run budget stopped the most recent `run`, or null when that
    /// run reached a fixed point. Both budgets abort the run with the same
    /// error, so consumers that report an incomplete analysis need this to
    /// name the limit that actually stopped it.
    limit_kind: ?LimitKind = null,
    /// Type context for type-aware analysis (optional, not owned).
    type_context: ?*TypeContext,
    /// Config for resource models (optional, not owned).
    config: ?*const Config,
    /// Whether widening is enabled.
    use_widening: bool,
    /// Cached CFG artifacts for this source (optional, not owned).
    cached_artifacts: ?*CachedArtifacts,
    /// Owned parent map for source-less or foreign-AST scope checks.
    owned_parent_map: ?[]u32,
    /// Scratch buffer for FQN construction
    fqn_buffer: [256]u8 = undefined,
    pub const LimitKind = enum { worklist_steps, states_per_point };

    pub const ResourceCalls = @import("resource_calls.zig").Mixin(@This());
    pub const Literals = @import("literals.zig").Mixin(@This());
    pub const VarResolution = @import("var_resolution.zig").Mixin(@This());
    pub const Ownership = @import("ownership.zig").Mixin(@This());
    pub const Payloads = @import("payloads.zig").Mixin(@This());
    pub const DeferScan = @import("defer_scan.zig").Mixin(@This());
    pub const ArenaProvenance = @import("arena_provenance.zig").Mixin(@This());
    pub const BranchConstraints = @import("branch_constraints.zig").Mixin(@This());
    pub const Summaries = @import("summaries.zig").Mixin(@This());

    const WorklistItem = struct {
        /// Index of the exploded graph node to process
        node_index: u32,
        /// The kind of edge that led to this node (for path-sensitive analysis)
        edge_kind: EdgeKind,
        /// Optional constraint to apply (from branch condition)
        pending_constraint: ?Constraint,
        /// CFG to use for this worklist item (for interprocedural analysis)
        cfg: *const Cfg,
    };

    pub fn init(allocator: std.mem.Allocator, cfg: *const Cfg) AnalysisEngine {
        return .{
            .allocator = allocator,
            .graph = ExplodedGraph.init(allocator, cfg),
            .worklist = .empty,
            .pruned_path_count = 0,
            .max_inline_depth = default_max_inline_depth,
            .max_worklist_steps = default_max_worklist_steps,
            .source = null,
            .function_cfgs = std.AutoHashMap(AstNodeId, FunctionCfgEntry).init(allocator),
            .function_names = std.StringHashMap(AstNodeId).init(allocator),
            .var_resolvers = std.AutoHashMap(AstNodeId, *VarResolver).init(allocator),
            .assertion_scopes = std.AutoHashMap(AstNodeId, assertions.AssertionScope).init(allocator),
            .inlined_call_count = 0,
            .summary_cache = SummaryCache.init(allocator),
            .use_summaries = true,
            .summary_use_count = 0,
            .build_metadata = null,
            .checker_name = null,
            .limit_kind = null,
            .type_context = null,
            .config = null,
            .use_widening = false,
            .cached_artifacts = null,
            .owned_parent_map = null,
        };
    }

    /// Initialize with interprocedural analysis support.
    pub fn initWithSource(allocator: std.mem.Allocator, cfg: *const Cfg, source: *Source) AnalysisEngine {
        var engine = init(allocator, cfg);
        engine.source = source;
        return engine;
    }

    pub fn deinit(self: *AnalysisEngine) void {
        self.graph.deinit();
        self.worklist.deinit(self.allocator);
        // Deinit and free all cached CFGs
        var iter = self.function_cfgs.valueIterator();
        while (iter.next()) |entry| {
            if (!entry.owned) continue;
            entry.cfg.deinit();
            self.allocator.destroy(entry.cfg);
        }
        self.function_cfgs.deinit();
        self.function_names.deinit();
        var resolver_iter = self.var_resolvers.valueIterator();
        while (resolver_iter.next()) |resolver_ptr| {
            resolver_ptr.*.deinit();
            self.allocator.destroy(resolver_ptr.*);
        }
        self.var_resolvers.deinit();
        var scope_iter = self.assertion_scopes.valueIterator();
        while (scope_iter.next()) |scope| {
            scope.deinit(self.allocator);
        }
        self.assertion_scopes.deinit();
        if (self.owned_parent_map) |map| {
            self.allocator.free(map);
        }
        self.summary_cache.deinit();
    }

    pub fn getParentMap(self: *AnalysisEngine, tree: *const std.zig.Ast) ![]const u32 {
        if (self.source) |src| {
            const source_tree: ?*const std.zig.Ast =
                src.borrowed_ast orelse if (src.cached_ast) |*cached| cached else null;
            if (source_tree == tree) return src.engineParentMap();
        }
        if (self.owned_parent_map) |map| return map;

        const parent_map = try ast_walk.buildDeclarationParentMap(self.allocator, tree);
        self.owned_parent_map = parent_map;
        return parent_map;
    }

    /// Set the maximum inline depth for interprocedural analysis.
    pub fn setMaxInlineDepth(self: *AnalysisEngine, depth: u32) void {
        self.max_inline_depth = depth;
    }

    /// Set the maximum number of worklist steps before aborting analysis.
    pub fn setMaxWorklistSteps(self: *AnalysisEngine, steps: usize) void {
        self.max_worklist_steps = steps;
    }

    /// Set the maximum number of states per program point before cap widening.
    pub fn setMaxStatesPerPoint(self: *AnalysisEngine, max: u32) void {
        self.graph.setMaxStatesPerPoint(max);
    }

    /// Enable or disable widening for convergence.
    pub fn setUseWidening(self: *AnalysisEngine, use_w: bool) void {
        self.use_widening = use_w;
    }

    /// Set the checker name for logging purposes.
    pub fn setCheckerName(self: *AnalysisEngine, name: []const u8) void {
        self.checker_name = name;
    }

    /// Set the type context for type-aware analysis.
    pub fn setTypeContext(self: *AnalysisEngine, type_ctx: *TypeContext) void {
        self.type_context = type_ctx;
    }

    /// Set the config for resource models.
    pub fn setConfig(self: *AnalysisEngine, config: *const Config) void {
        self.config = config;
    }

    pub fn setCachedArtifacts(self: *AnalysisEngine, artifacts: *CachedArtifacts) void {
        self.cached_artifacts = artifacts;
    }

    /// Enable or disable the use of function summaries.
    pub fn setUseSummaries(self: *AnalysisEngine, use_summaries: bool) void {
        self.use_summaries = use_summaries;
    }

    /// Get the count of inlined function calls.
    pub fn getInlinedCallCount(self: *const AnalysisEngine) u32 {
        return self.inlined_call_count;
    }

    /// Get the count of summary applications.
    pub fn getSummaryUseCount(self: *const AnalysisEngine) u32 {
        return self.summary_use_count;
    }

    /// Get the summary cache for inspection.
    pub fn getSummaryCache(self: *const AnalysisEngine) *const SummaryCache {
        return &self.summary_cache;
    }

    /// Set build metadata for the analysis engine.
    pub fn setBuildMetadata(self: *AnalysisEngine, metadata: *const BuildMetadata) void {
        self.build_metadata = metadata;
    }

    /// Get the build metadata if set.
    pub fn getBuildMetadata(self: *const AnalysisEngine) ?*const BuildMetadata {
        return self.build_metadata;
    }

    /// Run the analysis on the CFG, building the exploded graph.
    pub fn run(self: *AnalysisEngine) EngineError!void {
        // Both budgets can fire in one run, so the reported reason is always
        // the one that aborted the run rather than a leftover from an earlier
        // call on a reused engine.
        self.limit_kind = null;
        const cfg = self.graph.cfg;

        // Build function name index if source is available
        if (self.source) |src| {
            try self.buildFunctionIndex(src);
        }
        try VarResolution.prepare(self, cfg);

        // Resumed work can start inside a callee with callers not yet visited here.
        for (self.worklist.items) |item| {
            try VarResolution.prepare(self, item.cfg);
            if (self.graph.getNode(item.node_index)) |node| {
                for (node.state.call_stack.items) |frame| {
                    try VarResolution.prepare(self, frame.caller_cfg);
                }
            }
        }

        // Seed only when starting fresh; otherwise continue from the pre-seeded worklist.
        if (self.worklist.items.len == 0) {
            var initial_state = ProgramState.init(self.allocator);
            var owns_initial_state = true;
            defer if (owns_initial_state) initial_state.deinit();
            initial_state.build_metadata = self.build_metadata;
            const entry_point = ProgramPoint.initPre(cfg.entry, cfg);

            const result = try self.getOrCreateNode(entry_point, &initial_state, .{});
            owns_initial_state = result.caller_should_deinit;
            try self.worklist.append(self.allocator, .{ .node_index = result.index, .edge_kind = .normal, .pending_constraint = null, .cfg = cfg });
        }

        var worklist_steps: usize = 0;
        // LIFO (depth-first) by design: see the `worklist` field doc-comment.
        while (self.worklist.pop()) |item| {
            worklist_steps += 1;
            if (worklist_steps > self.max_worklist_steps) {
                const file_path = if (self.source) |src| src.getFilePath() else "unknown";
                const checker = self.checker_name orelse "unknown";
                const cfg_size = item.cfg.nodeCount();
                const inlined_cfgs = self.function_cfgs.count();
                log.warn("[{s}] analysis limit exceeded: {d} steps, {d} unique states, worklist {d}, cfg nodes {d}, inlined fns {d}, function {s} in {s}", .{
                    checker,
                    worklist_steps,
                    self.graph.nodes.items.len,
                    self.worklist.items.len,
                    cfg_size,
                    inlined_cfgs,
                    item.cfg.fn_name orelse "unknown",
                    file_path,
                });
                self.limit_kind = .worklist_steps;
                return error.AnalysisLimitExceeded;
            }
            try self.processNode(item.node_index, item.edge_kind, item.pending_constraint, item.cfg);
        }
    }

    fn getOrCreateNode(
        self: *AnalysisEngine,
        point: ProgramPoint,
        state: *ProgramState,
        options: ExplodedGraph.WideningOptions,
    ) EngineError!ExplodedGraph.GetOrCreateResult {
        return self.graph.getOrCreateNodeWithWidening(point, state, options) catch |err| {
            if (err == error.AnalysisLimitExceeded) {
                self.limit_kind = .states_per_point;
                log.warn("[{s}] analysis state limit exceeded: {d} states per point, function {s} in {s}, cfg node {d} ({s})", .{
                    self.checker_name orelse "unknown",
                    self.graph.max_states_per_point,
                    point.cfg.fn_name orelse "unknown",
                    if (self.source) |src| src.getFilePath() else "unknown",
                    ids.cfgIndex(point.node_index),
                    @tagName(point.kind),
                });
            }
            return err;
        };
    }

    /// Build an index of function names to AST node indices.
    fn buildFunctionIndex(self: *AnalysisEngine, src: *Source) EngineError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);
        const token_tags = tree.tokens.items(.tag);
        const main_tokens = tree.nodes.items(.main_token);

        for (0..tags.len) |i| {
            const tag = tags[i];
            if (tag == .fn_decl) {
                // Get the function name from the main token
                const main_token = main_tokens[i];
                // For fn_decl, main_token is the 'fn' keyword, name follows
                if (main_token + 1 < token_tags.len and token_tags[main_token + 1] == .identifier) {
                    const name_token = main_token + 1;
                    // Use tokenSlice to properly handle all identifier forms including @"escaped"
                    const name = tree.tokenSlice(name_token);
                    try self.function_names.put(name, ids.astId(@intCast(i)));
                }
            }
        }
    }

    /// Get or build a CFG for a function by its AST node index.
    pub fn getOrBuildFunctionCfg(self: *AnalysisEngine, fn_ast_node: AstNodeId) std.mem.Allocator.Error!?*const Cfg {
        // Check cache first - returns the pointer stored in the map
        if (self.function_cfgs.get(fn_ast_node)) |entry| {
            return entry.cfg;
        }

        if (self.cached_artifacts) |artifacts| {
            const fn_index = ids.astIndex(fn_ast_node);
            if (artifacts.getCfg(fn_index)) |cfg_ptr| {
                try self.function_cfgs.put(fn_ast_node, .{ .cfg = @constCast(cfg_ptr), .owned = false });
                return cfg_ptr;
            }
        }

        // Artifact CFGs must not retain an engine-local allocator context.
        const src = self.source orelse return null;
        const cfg_allocator = if (self.cached_artifacts) |artifacts| artifacts.allocator else self.allocator;
        var builder = CfgBuilder.init(cfg_allocator);
        builder.setTypeContext(self.type_context);
        const cfg_opt = builder.buildFromFn(src, fn_ast_node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidAst => return null,
        };
        var cfg = cfg_opt orelse return null;
        errdefer cfg.deinit();

        const cfg_ptr = try cfg_allocator.create(Cfg);
        errdefer cfg_allocator.destroy(cfg_ptr);
        cfg_ptr.* = cfg;

        if (self.cached_artifacts) |artifacts| {
            const fn_index = ids.astIndex(fn_ast_node);
            try self.function_cfgs.put(fn_ast_node, .{ .cfg = cfg_ptr, .owned = false });
            errdefer _ = self.function_cfgs.remove(fn_ast_node);
            try artifacts.addCfg(fn_index, cfg_ptr);
            return cfg_ptr;
        }

        try self.function_cfgs.put(fn_ast_node, .{ .cfg = cfg_ptr, .owned = true });
        return cfg_ptr;
    }

    /// Resolve a function call to a function AST node index.
    /// Returns null for external or unresolvable calls.
    fn resolveFunctionCall(self: *AnalysisEngine, call_ast_node: u32) ?AstNodeId {
        const src = self.source orelse return null;
        const tree = src.ast() catch return null;
        const tags = tree.nodes.items(.tag);
        const token_tags = tree.tokens.items(.tag);
        const main_tokens = tree.nodes.items(.main_token);

        if (call_ast_node >= tags.len) return null;
        const tag = tags[call_ast_node];

        // For call nodes, use fullCall to extract the callee
        var call_buf: [1]std.zig.Ast.Node.Index = undefined;
        const full_call = switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => tree.fullCall(&call_buf, @enumFromInt(call_ast_node)),
            else => return null,
        } orelse return null;

        // Extract callee node index
        const callee_node: u32 = @intFromEnum(full_call.ast.fn_expr);
        if (callee_node >= tags.len) return null;
        const callee_tag = tags[callee_node];

        // Only handle simple identifier calls for now
        if (callee_tag == .identifier) {
            const callee_token = main_tokens[callee_node];
            if (callee_token < token_tags.len and token_tags[callee_token] == .identifier) {
                // Use tokenSlice to properly handle all identifier forms including @"escaped"
                const name = tree.tokenSlice(callee_token);

                // Look up in function index
                return self.function_names.get(name);
            }
        }

        return null;
    }

    pub fn resolveVarIdFromExpr(self: *AnalysisEngine, expr_node: u32, current_cfg: *const Cfg) ?ids.VarId {
        return VarResolution.resolveVarIdFromExpr(self, expr_node, current_cfg);
    }

    pub fn resolveDeclInfoFromIdentifier(
        self: *AnalysisEngine,
        identifier_node: u32,
        current_cfg: *const Cfg,
    ) ?VarResolver.DeclInfo {
        return VarResolution.resolveDeclInfoFromIdentifier(self, identifier_node, current_cfg);
    }

    fn processNode(self: *AnalysisEngine, node_index: u32, edge_kind: EdgeKind, pending_constraint: ?Constraint, current_cfg: *const Cfg) EngineError!void {
        _ = edge_kind;

        // End the graph borrow before any operation can relocate its node array.
        const point, var state_copy = blk: {
            const node = self.graph.getNode(node_index) orelse return;
            break :blk .{ node.point, try node.state.clone(self.allocator) };
        };
        var owns_state_copy = true;
        defer if (owns_state_copy) state_copy.deinit();

        switch (point.kind) {
            .pre => {
                const cfg_node = current_cfg.getNode(point.node_index);

                // Check if this is a call node that should be inlined
                if (cfg_node) |node| {
                    if (node.ir_node.tag == .call) {
                        // Track escapes BEFORE inlining, since inlining will skip normal processing
                        if (node.ir_node.ast_node) |ast_node| {
                            try Ownership.trackEscapesFromCall(self, &state_copy, ast_node, current_cfg);
                            try Ownership.recordOwnershipFromCall(self, &state_copy, ast_node, current_cfg);
                        }

                        const inline_result = try self.handleCallNode(node_index, node, &state_copy, current_cfg);
                        if (inline_result.inlined) {
                            // Call was inlined, don't process normally
                            return;
                        }
                        // Fall through to normal processing for external/unresolvable calls
                    }
                }

                const post_point = ProgramPoint.initPost(point.node_index, current_cfg);
                owns_state_copy = false;
                var new_state = try self.transferFunction(point, state_copy, current_cfg);
                var owns_new_state = true;
                defer if (owns_new_state) new_state.deinit();

                // Apply any pending constraint from a branch edge
                if (pending_constraint) |constraint| {
                    try new_state.addConstraint(constraint);

                    // Check if the state is still satisfiable after adding the constraint
                    if (!new_state.isSatisfiable()) {
                        self.pruned_path_count += 1;
                        return; // Prune this path
                    }
                }

                const result = try self.getOrCreateNode(post_point, &new_state, .{});
                owns_new_state = result.caller_should_deinit;
                try self.graph.addEdge(node_index, result.index);

                if (result.is_new or result.state_updated) {
                    try self.worklist.append(self.allocator, .{ .node_index = result.index, .edge_kind = .normal, .pending_constraint = null, .cfg = current_cfg });
                }
            },
            .post => {
                const cfg_node = current_cfg.getNode(point.node_index);

                // Check if we're at a function exit and need to return to caller
                if (cfg_node) |node| {
                    if (node.ir_node.tag == .fn_exit and state_copy.isInlined()) {
                        try self.handleFunctionReturn(node_index, &state_copy);
                        return;
                    }
                }

                // Check if this point decides its edges on a condition - if
                // so, we need to extract constraints. A `while` header is a
                // branch the builder drew as a loop, and its two edges are
                // decided the same way: reading only `.branch` here is what
                // left the loop's own guard deciding nothing, so the widening
                // at that header could hand the body a counter its condition
                // rules out and the pass after the first one was analysed
                // although the loop never took it.
                var branch_constraint_buf: [4]?Constraint = .{ null, null, null, null };
                const branch_constraint_count: usize = if (cfg_node) |node| blk: {
                    if (node.ir_node.tag == .branch or node.ir_node.tag == .loop_header) {
                        break :blk BranchConstraints.extractBranchConstraints(self, node, current_cfg, &branch_constraint_buf);
                    }
                    break :blk 0;
                } else 0;

                // The one edge a header's own condition can close is the way
                // out of the loop, and there is a header whose condition names
                // no constraint to close it with: the integer domain is stated
                // over signed values and unsigned ones narrower than a machine
                // word, so a `usize` counter decides nothing here and a pass
                // the guard rules out is walked beside every pass it admits.
                // The environment is stated in a wider domain and does hold
                // that counter, so the guard is read off it here and the edge
                // closed where the condition settles it.
                const loop_exit_closed: bool = if (branch_constraint_count == 0) blk: {
                    if (cfg_node) |node| {
                        if (node.ir_node.tag == .loop_header) {
                            break :blk self.loopGuardHolds(&state_copy, node, current_cfg) orelse false;
                        }
                    }
                    break :blk false;
                } else false;

                // The `catch` expression this point leaves decides its arm on
                // the way out, so the decision is read once per point.
                const catch_ast_node = catchArmNode(cfg_node);

                for (current_cfg.edges.items) |edge| {
                    if (edge.from == point.node_index) {
                        const succ_point = ProgramPoint.initPre(edge.to, current_cfg);
                        var succ_state = try state_copy.clone(self.allocator);
                        var owns_succ_state = true;
                        defer if (owns_succ_state) succ_state.deinit();

                        // Handle error state transitions based on edge kind
                        switch (edge.kind) {
                            .try_error => {
                                succ_state.setErrorState(.error_active);
                            },
                            .try_success => {
                                // Continue on normal path
                            },
                            .catch_error => {
                                // Entering catch block - error is being handled
                                succ_state.setErrorState(.error_handled);
                                // The handler is the arm's value here, not the
                                // guarded call's.
                                if (catch_ast_node) |catch_ast| {
                                    try succ_state.pushCatchArm(catch_ast, .failure);
                                }
                            },
                            .catch_success => {
                                // Exiting catch block - return to normal
                                succ_state.setErrorState(.normal);
                                // The guarded call produced the value here.
                                if (catch_ast_node) |catch_ast| {
                                    try succ_state.pushCatchArm(catch_ast, .success);
                                }
                            },
                            .errdefer_edge => {
                                // Errdefer only executes on error path
                                if (!succ_state.isErrorPath()) continue;
                            },
                            else => {},
                        }

                        if (cfg_node) |node| {
                            try Payloads.applyPayloadBindings(self, node, edge.kind, &succ_state, current_cfg);
                        }

                        // Apply all branch constraints based on the edge kind
                        var path_pruned = false;
                        if (branch_constraint_count > 0) {
                            for (branch_constraint_buf[0..branch_constraint_count]) |maybe_constraint| {
                                if (maybe_constraint) |bc| {
                                    // The other way out of a loop header is the
                                    // edge that leaves the loop, and it is taken
                                    // exactly when the condition that header
                                    // reads does not hold.
                                    const constraint_to_apply = if (edge.kind == .branch_true)
                                        bc
                                    else if (edge.kind == .branch_false or edge.kind == .loop_exit)
                                        bc.negate()
                                    else
                                        continue;

                                    try succ_state.addConstraint(constraint_to_apply);
                                    if (!succ_state.isSatisfiable()) {
                                        self.pruned_path_count += 1;
                                        path_pruned = true;
                                        break;
                                    }
                                }
                            }
                        }
                        if (path_pruned) continue;

                        // A guard the environment already settles closes the
                        // way out of its header outright, and there is no
                        // state down that edge to ask: the pass the guard
                        // rules out is one nothing in it ever runs, so a store
                        // the continuation only reaches on a real pass has not
                        // moved what it would have moved, and whatever it was
                        // holding is left standing as an orphan nobody did
                        // anything wrong with.
                        if (loop_exit_closed and edge.kind == .loop_exit) {
                            self.pruned_path_count += 1;
                            continue;
                        }

                        // Determine if widening should be applied at this point.
                        // Widening forces convergence, so it belongs on the loop
                        // header pre-state reached by a back edge - the only point
                        // a state can be replaced after it was processed. Every
                        // other join, including one that sits in front of a loop,
                        // is entered a bounded number of times and keeps one node
                        // per distinct state. Widening those destroyed exactly the
                        // facts the checkers read there: a held resource became
                        // `unknown` and was never reported as a leak, and two
                        // concrete integer paths collapsed into a single `unknown`
                        // that no longer showed a possible zero divisor. The
                        // per-point state cap remains the bound for those joins.
                        const widening_options = blk: {
                            if (self.use_widening and edge.kind == .loop_back) {
                                if (current_cfg.getNode(edge.to)) |succ_cfg_node| {
                                    if (succ_cfg_node.ir_node.tag == .loop_header) {
                                        // succ_point is already a pre-state (from ProgramPoint.initPre above)
                                        const widening_key = WideningKey.init(succ_point, &succ_state);
                                        break :blk ExplodedGraph.WideningOptions{
                                            .apply_widening = true,
                                            .widening_key = widening_key,
                                        };
                                    }
                                }
                            }
                            break :blk ExplodedGraph.WideningOptions{};
                        };

                        const result = try self.getOrCreateNode(succ_point, &succ_state, widening_options);
                        owns_succ_state = result.caller_should_deinit;
                        try self.graph.addEdge(node_index, result.index);

                        if (result.is_new or result.state_updated) {
                            try self.worklist.append(self.allocator, .{ .node_index = result.index, .edge_kind = edge.kind, .pending_constraint = null, .cfg = current_cfg });
                        }
                    }
                }
            },
        }
    }

    const InlineResult = struct {
        inlined: bool,
        summary_applied: bool,
    };

    /// Handle a call node, potentially using a summary or inlining the callee.
    fn handleCallNode(
        self: *AnalysisEngine,
        exploded_node_index: u32,
        cfg_node: *const CfgNode,
        state: *const ProgramState,
        caller_cfg: *const Cfg,
    ) EngineError!InlineResult {
        // Try to resolve the call target
        const call_ast_node = cfg_node.ir_node.ast_node orelse return .{ .inlined = false, .summary_applied = false };
        const callee_fn_node = self.resolveFunctionCall(call_ast_node) orelse return .{ .inlined = false, .summary_applied = false };

        // Skip inlining when the callee is already on the call stack (direct
        // or indirect recursion). Inlining a recursive call adds depth without
        // new precision: each call site spawns its own (call_node, caller_cfg)
        // context, so a self-recursive walker over a wide switch multiplies
        // the engine's state space by N at every level. Treat recursive calls
        // as opaque; the engine still tracks side effects via the call IR
        // node's ownership / escape / use-after-free hooks.
        if (caller_cfg.fn_ast_node) |caller_fn| {
            if (caller_fn == callee_fn_node) {
                return .{ .inlined = false, .summary_applied = false };
            }
        }
        for (state.call_stack.items) |frame| {
            if (frame.caller_cfg.fn_ast_node) |ancestor_fn| {
                if (ancestor_fn == callee_fn_node) {
                    return .{ .inlined = false, .summary_applied = false };
                }
            }
        }

        // Try to use a cached summary if summaries are enabled
        // Only use summaries for pure functions (no side effects) to avoid losing
        // callee effects when skipping inlining
        if (self.use_summaries) {
            if (try Summaries.getOrComputeSummary(self, callee_fn_node)) |summary| {
                // Only apply summaries for pure functions to preserve side effect semantics
                if (!summary.has_side_effects and summary.isApplicable(state)) {
                    // Find the return point (successor of the call node in the caller)
                    var return_node: ?CfgNodeId = null;
                    for (caller_cfg.edges.items) |edge| {
                        if (edge.from == cfg_node.index) {
                            return_node = edge.to;
                            break;
                        }
                    }
                    const ret_node = return_node orelse return .{ .inlined = false, .summary_applied = false };

                    // Apply the summary to the state
                    var summary_state = try state.clone(self.allocator);
                    var owns_summary_state = true;
                    defer if (owns_summary_state) summary_state.deinit();
                    const is_satisfiable = try summary.applyToState(&summary_state);

                    // Contradictory postconditions fall through to inlining below.
                    if (is_satisfiable) {
                        self.summary_use_count += 1;

                        const post_call_point = ProgramPoint.initPre(ret_node, caller_cfg);
                        if (summary.may_return_error and !summary.always_returns_error) {
                            // Clone before either graph insertion can take ownership.
                            var error_state = try summary_state.clone(self.allocator);
                            var owns_error_state = true;
                            defer if (owns_error_state) error_state.deinit();
                            error_state.setErrorState(.error_active);

                            const error_result = try self.getOrCreateNode(post_call_point, &error_state, .{});
                            owns_error_state = error_result.caller_should_deinit;
                            try self.graph.addEdge(exploded_node_index, error_result.index);
                            if (error_result.is_new or error_result.state_updated) {
                                try self.worklist.append(self.allocator, .{
                                    .node_index = error_result.index,
                                    .edge_kind = .normal,
                                    .pending_constraint = null,
                                    .cfg = caller_cfg,
                                });
                            }
                        }

                        const result = try self.getOrCreateNode(post_call_point, &summary_state, .{});
                        owns_summary_state = result.caller_should_deinit;
                        try self.graph.addEdge(exploded_node_index, result.index);
                        if (result.is_new or result.state_updated) {
                            try self.worklist.append(self.allocator, .{
                                .node_index = result.index,
                                .edge_kind = .normal,
                                .pending_constraint = null,
                                .cfg = caller_cfg,
                            });
                        }

                        return .{ .inlined = true, .summary_applied = true };
                    }
                }
            }
        }

        // Fall back to inlining if no applicable summary or summaries are disabled
        // Check if we've exceeded the inline depth limit
        if (state.getInlineDepth() >= self.max_inline_depth) {
            return .{ .inlined = false, .summary_applied = false };
        }

        // Get or build the callee's CFG
        const callee_cfg = (try self.getOrBuildFunctionCfg(callee_fn_node)) orelse return .{ .inlined = false, .summary_applied = false };

        // Find the return point (successor of the call node in the caller)
        var return_node: ?CfgNodeId = null;
        for (caller_cfg.edges.items) |edge| {
            if (edge.from == cfg_node.index) {
                return_node = edge.to;
                break;
            }
        }
        const ret_node = return_node orelse return .{ .inlined = false, .summary_applied = false };

        try VarResolution.prepare(self, callee_cfg);

        // Create a new state for the inlined call
        var inline_state = try state.clone(self.allocator);
        var owns_inline_state = true;
        defer if (owns_inline_state) inline_state.deinit();
        inline_state.incrementInlineDepth();

        // Push the call site onto the stack
        try inline_state.pushCallSite(.{
            .call_node = cfg_node.index,
            .caller_cfg = caller_cfg,
            .return_node = ret_node,
        });

        // Create entry point for the callee
        const callee_entry_point = ProgramPoint.initPre(callee_cfg.entry, callee_cfg);
        const result = try self.getOrCreateNode(callee_entry_point, &inline_state, .{});
        owns_inline_state = result.caller_should_deinit;
        if (result.is_new or result.state_updated) {
            try self.worklist.append(self.allocator, .{
                .node_index = result.index,
                .edge_kind = .normal,
                .pending_constraint = null,
                .cfg = callee_cfg,
            });
        }

        try self.graph.addEdge(exploded_node_index, result.index);
        self.inlined_call_count += 1;

        return .{ .inlined = true, .summary_applied = false };
    }

    /// Handle returning from an inlined function.
    fn handleFunctionReturn(
        self: *AnalysisEngine,
        exploded_node_index: u32,
        state: *ProgramState,
    ) EngineError!void {
        // Pop the call site from the stack
        const call_site = state.popCallSite() orelse return;
        state.decrementInlineDepth();

        // Create a state for continuing after the call
        var return_state = try state.clone(self.allocator);
        var owns_return_state = true;
        defer if (owns_return_state) return_state.deinit();

        // Create the return point in the caller
        const return_point = ProgramPoint.initPre(call_site.return_node, call_site.caller_cfg);
        const result = try self.getOrCreateNode(return_point, &return_state, .{});
        owns_return_state = result.caller_should_deinit;
        if (result.is_new or result.state_updated) {
            try self.worklist.append(self.allocator, .{
                .node_index = result.index,
                .edge_kind = .normal,
                .pending_constraint = null,
                .cfg = call_site.caller_cfg,
            });
        }

        try self.graph.addEdge(exploded_node_index, result.index);
    }

    /// Transfer function: compute the new state after executing a CFG node.
    /// Evaluates literals and assignments, updating the environment.
    /// For call nodes that couldn't be inlined, treats them as having unknown effects.
    /// Consumes state on both success and failure.
    fn transferFunction(self: *AnalysisEngine, point: ProgramPoint, state: ProgramState, current_cfg: *const Cfg) EngineError!ProgramState {
        var new_state = state;
        errdefer new_state.deinit();
        const cfg_node = current_cfg.getNode(point.node_index) orelse return new_state;
        const ir_node = cfg_node.ir_node;

        switch (ir_node.tag) {
            .var_decl => {
                if (ir_node.ast_node) |ast_node| {
                    const var_id = VarResolution.resolveVarIdFromVarDecl(self, ast_node) orelse ids.varId(ast_node);
                    new_state.resetRegion(var_id);
                    // Try to evaluate literal value from init expression, fall back to unknown
                    const init_value = if (VarResolution.resolveVarDeclInitNode(self, ast_node)) |init_node|
                        Literals.evaluateLiteral(self, init_node)
                    else
                        null;
                    try new_state.setVar(var_id, init_value orelse .unknown);
                    if (VarResolution.resolveVarDeclInitNode(self, ast_node)) |init_node| {
                        // The initializer's operands are read before the call
                        // can consume them, so their use-after-free check has
                        // to come first: a realloc that succeeds frees the very
                        // slice it was handed, and reading it afterwards would
                        // report a use of a block this frame no longer owns.
                        try Ownership.checkUseAfterFreeInExpr(self, &new_state, init_node, current_cfg);
                        if (self.catchBindingValueExpr(&new_state, init_node)) |origin| {
                            if (ResourceCalls.resolveResourceCall(self, origin)) |call_info| {
                                switch (call_info.kind) {
                                    .alloc => try self.trackAllocatedRegion(&new_state, var_id, call_info.call_node, current_cfg),
                                    .realloc => {
                                        // The resize is the origin only on the
                                        // arm where it ran, and the block it
                                        // was handed is the replacement's from
                                        // there: a fallback that kept the
                                        // original reaches this binding holding
                                        // the original and consumes nothing.
                                        // A declaration opens a fresh binding
                                        // rather than replacing one, so the name
                                        // the call was handed the block through
                                        // is still the name holding it.
                                        try self.consumeReallocSource(&new_state, call_info, var_id, null, current_cfg);
                                        try self.trackAllocatedRegion(&new_state, var_id, call_info.call_node, current_cfg);
                                    },
                                    .open => try trackOpenedHandle(&new_state, var_id),
                                    else => {},
                                }
                            } else if (VarResolution.resolveVarIdFromExpr(self, origin, current_cfg)) |alias_target| {
                                if (alias_target != var_id) {
                                    try new_state.trackAlias(var_id, alias_target);
                                }
                            } else if (ResourceCalls.isDefinitelyNonAlloc(self, origin)) {
                                try new_state.trackNonAllocation(var_id);
                            }
                        }
                        try Ownership.recordOwnershipFromExpr(self, &new_state, init_node, var_id, current_cfg);
                    }
                }
            },
            .assign => {
                // For assignments, use the LHS identifier node as the key
                // operand_node contains the LHS, operand2_node contains the RHS
                if (ir_node.operand_node) |lhs_node| {
                    // A left-hand side that names no binding is not a store
                    // into this frame's environment, so it goes to
                    // `applyStoreIntoDestination`, which is what settles the
                    // aggregate, field and dereference cases.
                    if (try self.applyIdentifierStore(&new_state, lhs_node, ir_node.operand2_node, .replace, current_cfg)) {
                        // The store named a binding and wrote it.
                    } else if (ir_node.operand2_node) |rhs_node| {
                        try self.applyStoreIntoDestination(&new_state, lhs_node, rhs_node, .replace, current_cfg);
                    }
                }
            },
            .call => {
                // External or unresolvable calls: treat as unknown effects.
                // This means we conservatively assume the call could modify any state.
                // For now, we don't invalidate any specific variables since we don't
                // have precise aliasing information. Future enhancement: track which
                // variables could be modified by external calls.
                //
                // The call node itself doesn't change the abstract state significantly,
                // but the return value (if captured) would be unknown.
                if (ir_node.ast_node) |ast_node| {
                    if (ResourceCalls.resolveResourceCall(self, ast_node)) |call_info| {
                        switch (call_info.kind) {
                            .free => {
                                if (call_info.target_expr) |arg_node| {
                                    if (VarResolution.resolveVarIdFromExpr(self, arg_node, current_cfg)) |var_id| {
                                        const call_token = Ownership.resolveCallToken(self, call_info.call_node);
                                        try new_state.trackFree(var_id, call_token);
                                    }
                                }
                            },
                            .free_owned => {
                                if (call_info.target_expr) |arg_node| {
                                    if (VarResolution.resolveVarIdFromExpr(self, arg_node, current_cfg)) |var_id| {
                                        const call_token = Ownership.resolveCallToken(self, call_info.call_node);
                                        try new_state.trackFreeOwned(var_id, call_token);
                                    }
                                }
                            },
                            .close => {
                                if (call_info.target_expr) |arg_node| {
                                    if (VarResolution.resolveVarIdFromExpr(self, arg_node, current_cfg)) |var_id| {
                                        const call_token = Ownership.resolveCallToken(self, call_info.call_node);
                                        try new_state.trackClose(var_id, call_token);
                                    }
                                }
                            },
                            .realloc => {
                                // The source slice is read as an argument while
                                // the block is still live, so its check belongs
                                // here and ahead of anything that marks the
                                // block gone. Nothing is consumed: this call
                                // throws its replacement away, so the block the
                                // frame still names is the one it would have to
                                // release, and keeping it is what leaves the
                                // lost replacement reported instead of silently
                                // dropped.
                                try Ownership.checkUseAfterFreeInCall(self, &new_state, ast_node, current_cfg);
                            },
                            else => {},
                        }
                        switch (call_info.kind) {
                            // A release reads nothing, and the realloc above
                            // already read its source while it was still live.
                            .free, .free_owned, .close, .realloc => {},
                            else => try Ownership.checkUseAfterFreeInCall(self, &new_state, ast_node, current_cfg),
                        }
                    } else {
                        try Ownership.checkUseAfterFreeInCall(self, &new_state, ast_node, current_cfg);
                    }
                    try Ownership.trackEscapesFromCall(self, &new_state, ast_node, current_cfg);
                    try Ownership.recordOwnershipFromCall(self, &new_state, ast_node, current_cfg);

                    // Check for assertion calls like testing.expect(x != null)
                    // and add non-null constraints for the asserted variables
                    if (try BranchConstraints.extractAssertionConstraint(self, ast_node, current_cfg)) |constraint| {
                        try new_state.addConstraint(constraint);
                    }
                }
            },
            .defer_stmt => {
                if (ir_node.ast_node) |ast_node| {
                    try DeferScan.applyDeferredReleases(self, &new_state, ast_node, current_cfg);
                }
            },
            .errdefer_stmt => {
                if (ir_node.ast_node) |ast_node| {
                    try DeferScan.applyErrdeferredReleases(self, &new_state, ast_node, current_cfg);
                }
            },
            .ret => {
                if (ir_node.ast_node) |ast_node| {
                    var tree_opt: ?*const std.zig.Ast = null;
                    if (self.source) |src| {
                        if (src.ast() catch null) |tree| {
                            tree_opt = tree;
                            const data = tree.nodes.items(.data);
                            const tags = tree.nodes.items(.tag);
                            if (ast_node < data.len) {
                                if (data[ast_node].opt_node.unwrap()) |ret_expr| {
                                    const ret_expr_idx = @intFromEnum(ret_expr);
                                    try Ownership.checkUseAfterFreeInExpr(self, &new_state, ret_expr_idx, current_cfg);

                                    // Fast path: expression that is definitely an error value
                                    if (isDefinitelyErrorExpr(tree, ret_expr_idx)) {
                                        new_state.setErrorState(.error_active);
                                    } else if (try self.returnsCatchPayload(tree, current_cfg, ast_node, ret_expr_idx)) {
                                        // `catch |err| return err;` hands the
                                        // caught error straight back to the
                                        // caller, so this path leaves the
                                        // function the way a failed `try`
                                        // does and every `errdefer` still in
                                        // scope runs on it.
                                        new_state.setErrorState(.error_active);
                                    } else if (ret_expr_idx < tags.len and tags[ret_expr_idx] == .identifier) {
                                        if (VarResolution.resolveDeclInfoFromIdentifier(self, ret_expr_idx, current_cfg)) |decl_info| {
                                            if (decl_info.is_top_level) {
                                                if (self.type_context) |type_ctx| {
                                                    if (type_ctx.getNodeType(decl_info.decl_node)) |ti| {
                                                        if (ti.kind == .error_union) {
                                                            new_state.setErrorState(.error_active);
                                                        }
                                                    }
                                                }
                                            } else {
                                                const error_info = declErrorUnionInfo(tree, decl_info.decl_node);
                                                if (error_info.status) |is_error_union| {
                                                    if (is_error_union) {
                                                        new_state.setErrorState(.error_active);
                                                    }
                                                } else if (self.type_context) |type_ctx| {
                                                    if (error_info.init_node) |init_node| {
                                                        if (type_ctx.getExpressionTypeStrict(init_node)) |ti| {
                                                            if (ti.kind == .error_union) {
                                                                new_state.setErrorState(.error_active);
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } else if (self.type_context) |type_ctx| {
                                        // Type-based check: return expression is an error union
                                        // This handles cases like `return someFn();`
                                        if (type_ctx.getExpressionTypeStrict(ret_expr_idx)) |ti| {
                                            if (ti.kind == .error_union) {
                                                new_state.setErrorState(.error_active);
                                            }
                                        }
                                    }

                                    // `return replacement.len` hands the caller a
                                    // length, not the block: escaping the base
                                    // expression hid the leak a realloc leaves
                                    // behind, because nothing about the scalar
                                    // return lets the caller release it.
                                    const return_carries_reference = if (current_cfg.fn_ast_node) |fn_node|
                                        !Ownership.returnTypeCarriesNoReference(tree, ids.astIndex(fn_node))
                                    else
                                        true;
                                    if (return_carries_reference) {
                                        if (VarResolution.resolveVarIdFromExpr(self, ret_expr_idx, current_cfg)) |var_id| {
                                            try new_state.trackEscapeOwned(var_id);
                                            new_state.trackEscape(var_id);
                                        }
                                    }
                                    // `return allocator.realloc(buf, n)` hands the
                                    // block to the caller on success; on the error
                                    // path the original still belongs to its
                                    // errdefer, so nothing is consumed there.
                                    //
                                    // A `catch` fallback is the same answer
                                    // reached from the other side. That arm ran
                                    // because the resize failed, so the
                                    // original is still live and no failure
                                    // arm can consume it; only the success arm
                                    // produced a replacement to hand over. The
                                    // state says which arm produced the value,
                                    // so the resource call is read off that
                                    // arm rather than off the primary the
                                    // whole `catch` expression happens to name.
                                    if (!new_state.isErrorPath()) {
                                        if (self.catchBindingValueExpr(&new_state, ret_expr_idx)) |origin| {
                                            if (self.holdsReallocSource(&new_state, origin, current_cfg)) {
                                                _ = try Ownership.consumeReallocSourceInExpr(self, &new_state, origin, current_cfg);
                                            }
                                        }
                                    }
                                    try Ownership.markEscapedAtReturn(self, &new_state, ret_expr_idx, current_cfg);
                                }
                            }
                        }
                    }
                    if (new_state.isErrorPath()) {
                        if (tree_opt) |tree| {
                            const parent_map = try self.getParentMap(tree);
                            try new_state.applyErrdeferredReleases(ast_node, parent_map);
                        }
                    }
                }
            },
            .try_expr, .catch_expr => {
                if (ir_node.ast_node) |ast_node| {
                    try Ownership.checkUseAfterFreeInExpr(self, &new_state, ast_node, current_cfg);
                    try Ownership.trackEscapesInExpr(self, &new_state, ast_node, current_cfg);

                    // Check for assertion calls wrapped in try (try testing.expect(...))
                    if (try BranchConstraints.extractTryAssertionConstraint(self, ast_node, current_cfg)) |constraint| {
                        try new_state.addConstraint(constraint);
                    }
                }
            },
            .expr => {
                if (ir_node.ast_node) |ast_node| {
                    // A store the builder lowered as a plain expression - the
                    // step of a `while`, or a compound store written anywhere
                    // at all - carries a write of its own, so the value it
                    // leaves behind is written before the node is read for
                    // the rest of what it means.
                    const store_read = try self.applyExprStore(&new_state, ast_node, current_cfg);
                    // A store reads its own operands before the write lands, so
                    // reading the node whole would read them a second time and
                    // after the write: `pointee.* = value` would then be a read
                    // of blocks this store has already handed over. A node that
                    // carries no store is read here, because nothing else reads
                    // it.
                    if (!store_read) {
                        try Ownership.checkUseAfterFreeInExpr(self, &new_state, ast_node, current_cfg);
                    }
                    try Ownership.trackEscapesInExpr(self, &new_state, ast_node, current_cfg);
                }
            },
            .fn_exit => {
                if (current_cfg.fn_ast_node) |fn_node| {
                    try Ownership.escapeReturnedVars(self, &new_state, fn_node, current_cfg);
                }
                // Only record leaks at the exit of the top-level function, not inlined functions
                if (new_state.getInlineDepth() == 0 and !new_state.isErrorPath()) {
                    try new_state.trackLeaks();
                }
            },
            else => {},
        }

        return new_state;
    }

    /// What a store writes into the binding its left-hand side names.
    ///
    /// `replace` is a plain `=` and hands the binding a different value, so
    /// whatever resource it held went out with the old one. Every other
    /// operator updates the binding where it stands and keeps what it owns.
    const StoreOp = enum {
        replace,
        add,
        sub,
        mul,
        /// An operator this lattice has no arithmetic for. The write still
        /// happens, because leaving the old facts standing would let a
        /// condition downstream decide on a value the binding no longer has.
        unmodelled,
    };

    /// The operator an assignment AST node carries, or null for a node that
    /// stores nothing at all.
    fn storeOp(tag: std.zig.Ast.Node.Tag) ?StoreOp {
        if (!call_resolver.isAssignTag(tag)) return null;
        return switch (tag) {
            .assign => .replace,
            .assign_add => .add,
            .assign_sub => .sub,
            .assign_mul => .mul,
            else => .unmodelled,
        };
    }

    /// The interval a stored value covers, or null when it is not a number.
    fn integerBounds(value: AbstractValue) ?AbstractValue.IntRange {
        return switch (value) {
            .concrete_int => |v| AbstractValue.IntRange.single(v),
            .int_range => |r| r,
            else => null,
        };
    }

    const ArithmeticBounds = struct { low: i128, high: i128 };

    /// The interval a compound operation over two intervals reaches, kept in
    /// the widened `i128` that every sum and product of two `i64` bounds fits
    /// in.
    fn arithmeticBounds(lhs: AbstractValue.IntRange, rhs: AbstractValue.IntRange, op: StoreOp) ArithmeticBounds {
        const a: i128 = @as(i128, lhs.min);
        const b: i128 = @as(i128, lhs.max);
        const c: i128 = @as(i128, rhs.min);
        const d: i128 = @as(i128, rhs.max);
        return switch (op) {
            .add => .{ .low = a + c, .high = b + d },
            .sub => .{ .low = a - d, .high = b - c },
            .mul => blk: {
                const p0 = a * c;
                const p1 = a * d;
                const p2 = b * c;
                const p3 = b * d;
                break :blk .{
                    .low = @min(@min(p0, p1), @min(p2, p3)),
                    .high = @max(@max(p0, p1), @max(p2, p3)),
                };
            },
            .replace, .unmodelled => unreachable,
        };
    }

    /// The value a compound store leaves behind, or `.unknown` when the
    /// operator or either operand says nothing this lattice can carry.
    ///
    /// Two known numbers go through the checked operation their operator
    /// names, because that is what the source does. Anything else that is a
    /// number on both sides reuses the range path: a single value is already
    /// the range of one, so a number over a range is a range too.
    fn compoundValue(previous: AbstractValue, operand: AbstractValue, op: StoreOp) AbstractValue {
        switch (op) {
            .replace, .unmodelled => return .unknown,
            .add, .sub, .mul => {},
        }
        if (previous.toConcreteInt()) |a| {
            if (operand.toConcreteInt()) |b| {
                const result = switch (op) {
                    .add => std.math.add(i64, a, b) catch return .unknown,
                    .sub => std.math.sub(i64, a, b) catch return .unknown,
                    .mul => std.math.mul(i64, a, b) catch return .unknown,
                    .replace, .unmodelled => unreachable,
                };
                return .{ .concrete_int = result };
            }
        }
        const bounds = arithmeticBounds(
            integerBounds(previous) orelse return .unknown,
            integerBounds(operand) orelse return .unknown,
            op,
        );
        if (bounds.low < std.math.minInt(i64) or bounds.high > std.math.maxInt(i64)) return .unknown;
        return .{ .int_range = .{
            .min = @intCast(bounds.low),
            .max = @intCast(bounds.high),
        } };
    }

    /// The value a store's right-hand side hands over, or null when nothing
    /// about it is known: a literal answers itself, and anything else answers
    /// only by naming a binding this path already holds a value for.
    fn operandValue(
        self: *AnalysisEngine,
        state: *const ProgramState,
        node: u32,
        current_cfg: *const Cfg,
    ) ?AbstractValue {
        if (Literals.evaluateLiteral(self, node)) |literal| return literal;
        const var_id = VarResolution.resolveVarIdFromExpr(self, node, current_cfg) orelse return null;
        return state.getVar(var_id);
    }

    /// The comparison an integer operator stands for, or null for a tag that
    /// spells none of them.
    ///
    /// `==` and `!=` are left out: a loop guard decides how often a pass runs,
    /// and the two equality forms name a value to match rather than a bound to
    /// stay under. The constraint domain still carries them for the narrower
    /// types it reads, so nothing is lost by not answering for them here.
    fn boundComparison(tag: std.zig.Ast.Node.Tag) ?CompareOp {
        return switch (tag) {
            .less_than => .lt,
            .less_or_equal => .le,
            .greater_than => .gt,
            .greater_or_equal => .ge,
            else => null,
        };
    }

    /// The same comparison read the other way round, which is what `bound < n`
    /// asks about the value of `n`.
    fn reversedBoundComparison(op: CompareOp) CompareOp {
        return switch (op) {
            .lt => .gt,
            .le => .ge,
            .gt => .lt,
            .ge => .le,
            .eq => .eq,
            .ne => .ne,
        };
    }

    /// Whether `held op bound` holds, which is the one question reading a
    /// guard off a value ever asks.
    fn boundHolds(held: i64, op: CompareOp, bound: i64) bool {
        return switch (op) {
            .eq => held == bound,
            .ne => held != bound,
            .lt => held < bound,
            .le => held <= bound,
            .gt => held > bound,
            .ge => held >= bound,
        };
    }

    /// The node an expression is once the parentheses written around it are
    /// read through, or null when the walk does not land on the tree.
    ///
    /// The walk is bounded by the node count: a guard spelled with a nesting
    /// no parser produces is not an answer to wait for.
    fn throughParentheses(tree: *const std.zig.Ast, node: u32) ?u32 {
        const tags = tree.nodes.items(.tag);
        var current = node;
        var remaining = tags.len;
        while (remaining > 0 and current != 0 and current < tags.len) : (remaining -= 1) {
            if (tags[current] != .grouped_expression) return current;
            current = @intFromEnum(tree.nodes.items(.data)[current].node_and_token[0]);
        }
        return null;
    }

    /// The number a guard's counter stands for on this path, or null when the
    /// operand is not a binding this frame holds a number for.
    ///
    /// Only a plain identifier names one. The field, element and dereference
    /// forms resolve to whatever they are read through, and a guard written
    /// over one of those asks about a different value than the one the
    /// binding holds, so they answer nothing here.
    fn guardOperandValue(
        self: *AnalysisEngine,
        state: *const ProgramState,
        node: u32,
        current_cfg: *const Cfg,
    ) ?i64 {
        const src = self.source orelse return null;
        const tree = src.ast() catch return null;
        const tags = tree.nodes.items(.tag);
        const operand = throughParentheses(tree, node) orelse return null;
        if (tags[operand] != .identifier) return null;
        const var_id = VarResolution.resolveVarIdFromExpr(self, operand, current_cfg) orelse return null;
        return (state.getVar(var_id) orelse return null).toConcreteInt();
    }

    /// Whether the guard a loop header reads already holds for the value this
    /// path gives it, or null when the header's condition says nothing here.
    ///
    /// This is the guard the constraint domain cannot phrase. Its ranges and
    /// the strict bounds derived from them are defined over signed integers and
    /// unsigned ones narrower than a machine word, so the comparison behind a
    /// `usize` counter in `while (i < 1)` names no constraint at all and the
    /// header's two edges go undecided: a pass the guard rules out is walked
    /// beside every pass it admits. The environment is stated in a wider
    /// domain and does hold that counter - `applyIdentifierStore` and
    /// `compoundValue` keep an exact number for a counter this loop is
    /// stepping - so the comparison can be read off it without widening the
    /// integer domain anything else is phrased in terms of.
    ///
    /// Only a `while` has a condition to read: a `for` header steps to the next
    /// item instead of testing one, so `fullWhile` names nothing for it and
    /// this returns null. A guard over two counters, or one bound by something
    /// that is not spelled as a literal, has no single value to read here
    /// either and is left to the domain that already carries it.
    fn loopGuardHolds(
        self: *AnalysisEngine,
        state: *const ProgramState,
        cfg_node: *const CfgNode,
        current_cfg: *const Cfg,
    ) ?bool {
        const ast_node = cfg_node.ir_node.ast_node orelse return null;
        const src = self.source orelse return null;
        const tree = src.ast() catch return null;
        const tags = tree.nodes.items(.tag);
        if (ast_node >= tags.len) return null;
        const full_while = tree.fullWhile(@enumFromInt(ast_node)) orelse return null;
        const condition = @intFromEnum(full_while.ast.cond_expr);
        const node = throughParentheses(tree, condition) orelse return null;
        const operator = boundComparison(tags[node]) orelse return null;
        const operands = tree.nodes.items(.data)[node].node_and_node;
        const lhs = @intFromEnum(operands[0]);
        const rhs = @intFromEnum(operands[1]);
        // A bound spelled as a literal is the only one this reads: `i < n` is
        // a question about two values, and the environment only answers for
        // one of them at a time.
        if (Literals.evaluateLiteral(self, rhs)) |rhs_literal| {
            if (rhs_literal.toConcreteInt()) |bound| {
                const held = self.guardOperandValue(state, lhs, current_cfg) orelse return null;
                return boundHolds(held, operator, bound);
            }
        }
        if (Literals.evaluateLiteral(self, lhs)) |lhs_literal| {
            if (lhs_literal.toConcreteInt()) |bound| {
                const held = self.guardOperandValue(state, rhs, current_cfg) orelse return null;
                return boundHolds(held, reversedBoundComparison(operator), bound);
            }
        }
        return null;
    }

    /// `_ = ...;` keeps no value and cannot have written one.
    fn isDiscardBinding(tree: *const std.zig.Ast, ident_node: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (ident_node == 0 or ident_node >= tags.len or tags[ident_node] != .identifier) return false;
        const token = tree.nodes.items(.main_token)[ident_node];
        if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return false;
        return std.mem.eql(u8, tree.tokenSlice(token), "_");
    }

    /// Whether `region` still stands for a resource this frame holds.
    ///
    /// Read through the name that holds it, and counting only the states that
    /// mean the program still holds what they are recorded against, which is
    /// the pair `Store` reads every region through: what a binding loses is
    /// decided from the same answer here that `replaceRegionForBinding` decides
    /// it from there, over the same two states `Store.isHeldResource` counts.
    fn regionHoldsResource(state: *const ProgramState, region: ids.VarId) bool {
        const held = state.getRegionState(region) orelse return false;
        return held == .allocated or held == .open;
    }

    /// Write `rhs_node` into the binding `lhs_node` names, and report whether
    /// there was one to write.
    ///
    /// A store the builder gave a node of its own and one it lowered as a
    /// plain expression - the step of a `while`, or a compound store written
    /// anywhere at all - come through here, so what a condition reads after a
    /// step is the value the step leaves rather than the one before it ran.
    fn applyIdentifierStore(
        self: *AnalysisEngine,
        new_state: *ProgramState,
        lhs_node: u32,
        rhs_node: ?u32,
        op: StoreOp,
        current_cfg: *const Cfg,
    ) EngineError!bool {
        const src = self.source orelse return false;
        const tree = src.ast() catch return false;
        const tags = tree.nodes.items(.tag);
        if (lhs_node >= tags.len or tags[lhs_node] != .identifier) return false;
        // `resolveVarIdFromIdentifier` falls back to the token an identifier is
        // spelled with, so it answers for every name the resolver covers and for
        // every one it does not. It hands back nothing for a node that is not
        // spelled with an identifier at all, and there is no name to key a
        // region on there: a node index would drop a second namespace on top of
        // the token indices every other region is keyed by, and an identifier
        // node landing on another one's token would share its region. Such a
        // destination names no binding of this frame, which is what the caller
        // settles it through `applyStoreIntoDestination` for.
        const var_id = VarResolution.resolveVarIdFromIdentifier(self, lhs_node, current_cfg) orelse return false;

        // A discard slot is written and dropped in the same statement.
        // Everything it was handed is still accounted for below, so an
        // acquisition written straight into it is a leak like any other. What
        // it is not is a name: `_` cannot be declared, read or passed on, so a
        // store into it never leaves a second name behind for the value it
        // discarded. That is what a repeated scope turns on: when the binding
        // is declared again, `Store.resetRegion` hands the resource it is about
        // to re-acquire to whichever saved name still stands for it, and a name
        // that stands for nothing must not be one.
        //
        // A scope that binds the name `_` is the one case where something does
        // stand behind the slot. `const _ = x;`, a `|_|` capture and a payload
        // of its own all bind it, and `VarResolver` then resolves every
        // identifier spelled `_` in that scope to that one region: a store into
        // it is a store into a name, and what the name is holding is what says
        // so. That is the same question `Store.replaceRegionForBinding` answers
        // through `held` before it accounts for what a binding loses, so it is
        // the same question asked here. Only a slot standing for nothing is a
        // discard.
        const discarded = isDiscardBinding(tree, lhs_node) and !regionHoldsResource(new_state, var_id);

        switch (op) {
            .replace => {
                // Read the old value before replacing its binding. Selecting
                // a catch origin settles that arm, so read it exactly once.
                if (rhs_node) |rhs| {
                    try Ownership.checkUseAfterFreeInExpr(self, new_state, rhs, current_cfg);
                }
                const origin = if (rhs_node) |rhs|
                    self.catchBindingValueExpr(new_state, rhs)
                else
                    null;
                const rhs_value = if (origin) |value|
                    operandValue(self, new_state, value, current_cfg)
                else
                    null;
                const resource_call = if (origin) |value|
                    ResourceCalls.resolveResourceCall(self, value)
                else
                    null;
                const alias_target = if (origin) |value|
                    if (resource_call == null) VarResolution.resolveVarIdFromExpr(self, value, current_cfg) else null
                else
                    null;

                var replacement: BindingReplacement = .different;
                // The block a successful resize freed, read out while the name
                // it was handed through is still the one holding it. Writing
                // the result into the binding is what promotes whichever alias
                // outlived it over that name, so the same question asked after
                // the store answers with the binding that was replaced - which
                // holds the grown block, not the one the resize released.
                var resized_source: ?ids.VarId = null;
                if (resource_call) |call_info| {
                    if (call_info.kind == .realloc) {
                        if (call_info.target_expr) |source_expr| {
                            if (VarResolution.resolveVarIdFromExpr(self, source_expr, current_cfg)) |source_var| {
                                replacement = .{ .realloc_source = source_var };
                                resized_source = new_state.reallocSourceAfterReplacement(var_id, source_var);
                            }
                        }
                    }
                } else if (origin) |value| {
                    // A discard is written and dropped in the same statement:
                    // it neither keeps what it was handed nor takes anything
                    // away, so neither reading of the replacement is about it.
                    const names_the_binding = value < tags.len and
                        (tags[value] == .identifier or tags[value] == .unwrap_optional);
                    if (!discarded and names_the_binding) {
                        if (alias_target) |target| replacement = .{ .same_resource = target };
                    }
                }

                const releases = try new_state.replaceRegionForBinding(var_id, replacement);
                try new_state.setVar(var_id, rhs_value orelse .unknown);
                if (resource_call) |call_info| {
                    switch (call_info.kind) {
                        .alloc => try self.trackAllocatedRegion(new_state, var_id, call_info.call_node, current_cfg),
                        .realloc => {
                            try self.consumeReallocSource(new_state, call_info, var_id, resized_source, current_cfg);
                            try self.trackAllocatedRegion(new_state, var_id, call_info.call_node, current_cfg);
                        },
                        .open => try trackOpenedHandle(new_state, var_id),
                        else => {},
                    }
                } else if (alias_target) |target| {
                    if (!discarded and !new_state.sameResource(var_id, target)) {
                        try new_state.trackAlias(var_id, target);
                    }
                } else if (origin) |value| {
                    if (ResourceCalls.isDefinitelyNonAlloc(self, value)) {
                        try new_state.trackNonAllocation(var_id);
                    }
                }
                // Deferred code reads the new slot at exit. Its old resource
                // was accounted for above, not released by a queued marker.
                try new_state.restoreBindingReleases(var_id, releases);
                if (origin) |value| {
                    try Ownership.recordOwnershipFromExpr(self, new_state, value, var_id, current_cfg);
                }
                return true;
            },
            .add, .sub, .mul, .unmodelled => {
                // The right-hand side is read before the store lands, so a
                // step naming its own target sees the value this path holds
                // rather than the one about to replace it.
                const previous = new_state.getVar(var_id);
                const operand = if (rhs_node) |rhs|
                    operandValue(self, new_state, rhs, current_cfg)
                else
                    null;
                // The region is deliberately left where it is: the binding is
                // being updated where it stands, not handed a different
                // resource in place of the one it already holds.
                const value = if (previous != null and operand != null)
                    compoundValue(previous.?, operand.?, op)
                else
                    .unknown;
                try new_state.setVar(var_id, value);
            },
        }

        return true;
    }

    /// Settle a store whose left-hand side names no binding of this frame.
    ///
    /// The destination is a pointee, a field or an element, so what the store
    /// moves is what the aggregate, field and dereference cases decide. A store
    /// into a binding never reaches here: that one names the frame's own
    /// environment and hands its value straight to the binding.
    ///
    /// Both operands are read before the ownership moves, the destination
    /// first: the destination is read to write through it and the value is
    /// read to be stored, and a realloc that succeeds frees the very slice it
    /// was handed, so a read that came afterwards would name a block this
    /// frame no longer owns.
    ///
    /// `op` is the operator the store was written with, which is what decides
    /// whether anything moves at all: a compound store updates the
    /// destination where it stands and hands nothing over.
    fn applyStoreIntoDestination(
        self: *AnalysisEngine,
        new_state: *ProgramState,
        lhs_node: u32,
        rhs_node: u32,
        op: StoreOp,
        current_cfg: *const Cfg,
    ) EngineError!void {
        try Ownership.checkUseAfterFreeInExpr(self, new_state, lhs_node, current_cfg);
        try Ownership.checkUseAfterFreeInExpr(self, new_state, rhs_node, current_cfg);
        // A compound store reads its right-hand side and updates the
        // destination where it stands; it hands nothing over, so nothing on
        // that side becomes the destination's and the resource it names is
        // not one this store releases. A plain `=` is the only store that
        // moves a value, so only a plain `=` settles ownership or escapes a
        // value below. This is the same rule `applyIdentifierStore` applies
        // to a store that names a binding, and `self.live += bytes.len` is
        // what it exists for: the right-hand side there is a length, and a
        // length conveys no ownership of the block it was read from.
        if (op != .replace) return;
        // `aggregate[index] = payload` and `pointee.* = value` both move the
        // right side's contents into something else; neither makes them escape.
        // Settling them here first would otherwise discard the store's proof
        // and hide every leak it exists to report.
        const store_settles_payload = try Ownership.recordOwnershipFromAggregateStore(self, new_state, lhs_node, rhs_node, current_cfg);
        const deref_settles_rhs = try Ownership.recordOwnershipFromDerefAssign(self, new_state, lhs_node, rhs_node, current_cfg);
        if (!store_settles_payload and !deref_settles_rhs) {
            try Ownership.markEscapedInExpr(self, new_state, rhs_node, current_cfg);
        }
        try Ownership.recordOwnershipFromFieldAssign(self, new_state, lhs_node, rhs_node, current_cfg);
        if (self.catchBindingValueExpr(new_state, rhs_node)) |origin| {
            if (ResourceCalls.resolveResourceCall(self, origin)) |call_info| {
                switch (call_info.kind) {
                    .alloc, .open => {
                        if (self.source) |src| {
                            if (src.ast() catch null) |tree| {
                                const tags = tree.nodes.items(.tag);
                                const datas = tree.nodes.items(.data);
                                if (lhs_node < tags.len and tags[lhs_node] == .field_access) {
                                    if (VarResolution.resolveVarIdFromExpr(self, lhs_node, current_cfg)) |field_var| {
                                        switch (call_info.kind) {
                                            .alloc => try self.trackAllocatedRegion(new_state, field_var, call_info.call_node, current_cfg),
                                            .open => try new_state.trackOpen(field_var),
                                            else => {},
                                        }
                                        const field_access_data = datas[lhs_node].node_and_token;
                                        const base_node = @intFromEnum(field_access_data[0]);
                                        if (VarResolution.resolveVarIdFromExpr(self, base_node, current_cfg)) |container_var| {
                                            try new_state.trackOwnership(field_var, container_var);
                                            try Ownership.escapeOwnedFromFieldBase(self, new_state, tree, base_node, container_var, field_var);
                                        }
                                    }
                                }
                            }
                        }
                    },
                    else => {},
                }
            }
        }
    }

    /// The store a plain expression node carries, and whether it carried one.
    ///
    /// The builder gives a `=` a node of its own, but the same store written
    /// as a loop's continuation step, or as a compound store, arrives as the
    /// expression it is written as. Its operands are the two the dedicated
    /// node names, so both land on the one write.
    ///
    /// True means the node was a store, whose operands this read in the order
    /// the store reads them, so the caller reads no further: a read that came
    /// after the write would name blocks the write has already given away.
    ///
    /// A compound store is a read before it is a write, and nothing that walks
    /// an expression for use-after-free walks a store's operands, so both sides
    /// of the operator are read here, before the write lands: `pointee.* += 1`
    /// names no binding at all, and `count += bytes[0]` reads the block standing
    /// on its right-hand side. A plain `=` leaves the read to the store it
    /// lands in.
    fn applyExprStore(
        self: *AnalysisEngine,
        new_state: *ProgramState,
        ast_node: u32,
        current_cfg: *const Cfg,
    ) EngineError!bool {
        const src = self.source orelse return false;
        const tree = src.ast() catch return false;
        const tags = tree.nodes.items(.tag);
        if (ast_node >= tags.len) return false;
        const op = storeOp(tags[ast_node]) orelse return false;
        const operands = tree.nodes.items(.data)[ast_node].node_and_node;
        const lhs_node: u32 = @intFromEnum(operands[0]);
        const rhs_node: u32 = @intFromEnum(operands[1]);

        if (op != .replace) {
            try Ownership.checkUseAfterFreeInExpr(self, new_state, lhs_node, current_cfg);
            try Ownership.checkUseAfterFreeInExpr(self, new_state, rhs_node, current_cfg);
        }
        if (try self.applyIdentifierStore(new_state, lhs_node, rhs_node, op, current_cfg)) return true;
        try self.applyStoreIntoDestination(new_state, lhs_node, rhs_node, op, current_cfg);
        return true;
    }

    /// The `catch` expression a `catch_error`/`catch_success` edge leaves,
    /// which is the arm decision that edge carries. Only a `catch` expression
    /// splits its value across two such edges, and only there is the value a
    /// binding takes over from it in question.
    fn catchArmNode(cfg_node: ?*const CfgNode) ?u32 {
        const node = cfg_node orelse return null;
        if (node.ir_node.tag != .catch_expr) return null;
        return node.ir_node.ast_node;
    }

    /// The expression that actually produced a binding's value on this path,
    /// or null when the path supplied nothing to bind.
    ///
    /// A `catch` expression has two origins and the path says which one ran:
    /// leaving the expression is what decides it, and each arm's edge records
    /// it as `PendingCatchArms` does. On the success arm the binding holds
    /// what the guarded call produced. On the failure arm that call produced
    /// nothing and the handler ran instead, so the binding holds the
    /// handler's fallback - which may be an open of its own, a handle this
    /// frame already holds, or a `catch` of its own whose arm decides next.
    ///
    /// The arm decides the acquisition, and taking the primary's on the
    /// failure arm would name a call this path never made: the release
    /// written for the success arm would be charged against the wrong
    /// allocator, an allocation's provenance would be read off the wrong
    /// call, and a resize's source would be consumed on a path where the
    /// resize never happened. An arm that completed without a value hands
    /// the binding nothing at all, and there is nothing there for the release
    /// to settle.
    ///
    /// A `catch` this path carries no decision for is not that: the control
    /// flow never split its arms, so nothing was chosen between them and the
    /// expression is handed back whole. Every `catch` expression the builder
    /// evaluates gets its own node - an operand of a chained one included -
    /// so which call produced the value is read off the edges of each
    /// expression rather than guessed from the outermost one. Handing an
    /// unsplit expression back whole keeps the obligation: the binding still
    /// holds one handle, and the resolver reads what it can from the calls
    /// that could have produced it.
    fn catchBindingValueExpr(
        self: *AnalysisEngine,
        state: *ProgramState,
        expr_node: u32,
    ) ?u32 {
        const src = self.source orelse return expr_node;
        const tree = src.ast() catch return expr_node;
        return self.catchArmValueExpr(state, tree, expr_node);
    }

    /// The value this path took out of the `catch` expression at `expr_node`,
    /// which is the expression itself when it is not a `catch` at all.
    ///
    /// Every expression this reads hands the next one over as a strict child
    /// of itself: parentheses hold one expression, and an arm's value is
    /// written inside the expression it came out of. So the walk only ever
    /// moves further into the tree and it ends on its own, whatever depth the
    /// chain is written at.
    ///
    /// Stopping short of the end instead is not a weaker answer but a wrong
    /// one. What a short walk hands back is the expression below the last
    /// `catch` it did read, and the resource resolution that follows reads
    /// that as a `catch` this path carries no decision for - which is handed
    /// back whole, and whose guarded call is then taken for the binding. The
    /// release written for the arm that really ran would be charged to a call
    /// this path never made.
    ///
    /// The arms the walk reads are settled one at a time as it reads them:
    /// the value an arm produced is bound by the expression this answers, so
    /// no point below it is still holding that arm. Settling each one by name
    /// needs no buffer holding the whole list, so a chain longer than any
    /// fixed size settles every arm it read rather than only as many as a
    /// buffer fitted.
    fn catchArmValueExpr(
        self: *AnalysisEngine,
        state: *ProgramState,
        tree: *const std.zig.Ast,
        expr_node: u32,
    ) ?u32 {
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var expr = expr_node;
        while (true) {
            // Parentheses are not a separate expression. The control flow
            // splits the arms of a `catch` written inside them exactly as it
            // does one written bare, so the walk looks through the group
            // instead of stopping at it and naming the guarded call behind it.
            while (expr < tags.len and tags[expr] == .grouped_expression) {
                expr = @intFromEnum(datas[expr].node_and_token[0]);
            }
            if (expr >= tags.len or tags[expr] != .@"catch") return expr;
            const arm = state.getCatchArm(expr) orelse return expr;
            const read = [_]u32{expr};
            state.forgetCatchArms(read[0..]);
            if (arm == .failure) {
                const handler = @intFromEnum(datas[expr].node_and_node[1]);
                // `catch null` binds `null`, and a null is not a handle. The
                // literal has no node tag of its own - the parser files it
                // under `.identifier` - so only that spelling names a null here.
                if (Literals.isNullLiteral(self, handler)) return null;
                // A handler that returns before the binding exists never
                // reaches it with anything: the guarded call failed, so this
                // path produced the handler's exit and nothing else.
                if (TypeContext.catchFailureSuppliesNoValue(tree, handler, TypeContext.catch_failure_walk_frames)) return null;
            }
            const value = switch (arm) {
                .success => ResourceCalls.catchArmValueExpr(self, tree, expr, .success),
                .failure => ResourceCalls.catchArmValueExpr(self, tree, expr, .failure),
            } orelse return null;
            // The arm's own value can be a `catch` in turn - a handler written
            // as `a() catch (b() catch c())` - and that one decides in turn.
            expr = value;
        }
    }

    /// Bound on the walk from a `return` up to the `catch` that binds what
    /// it hands back: deep enough for the nesting a handler is written with,
    /// and no deeper. A chain past it answers false rather than naming a
    /// binding the return never reached.
    const catch_payload_walk_frames: u32 = 64;

    /// True when `return` hands back the error a `catch` around it bound.
    ///
    /// `catch |err| return err;` propagates the very error the guarded call
    /// produced, so this path leaves the function the way a failed `try`
    /// does. The edge into the handler marks the failure handled, and a
    /// fallback that falls through carries the same state, so the state alone
    /// cannot tell a rethrow from a handled return; the binding the `catch`
    /// actually introduced can. Reading the rethrow as an ordinary value left
    /// every `errdefer` in scope unapplied and reported the block they own as
    /// leaked on a path that releases it.
    ///
    /// The payload and the name the handler returns are two spellings of one
    /// binding, so they are matched as the binding rather than as tokens: a
    /// use of the payload resolves to the payload's own var id, and a
    /// declaration inside the handler that shadows that name resolves to
    /// its own. Comparing the tokens themselves never answers true, which is
    /// what left the rethrow below reading as an ordinary value return.
    fn returnsCatchPayload(
        self: *AnalysisEngine,
        tree: *const std.zig.Ast,
        current_cfg: *const Cfg,
        ret_node: u32,
        ret_expr: u32,
    ) EngineError!bool {
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);

        // Parentheses are not a separate expression. `catch |err| return
        // (err);` propagates the very payload `return err;` propagates, so
        // the binding is settled before it is tested for being a name: a
        // group holds no name of its own, and reading the gate off it answered
        // false and left the `errdefer` in scope unapplied.
        //
        // Every step is a parenthesis handing over the one expression it
        // holds, so the walk only ever moves further into the tree and ends.
        var binding = ret_expr;
        while (binding < tags.len and tags[binding] == .grouped_expression) {
            binding = @intFromEnum(datas[binding].node_and_token[0]);
        }
        if (binding >= tags.len or tags[binding] != .identifier) return false;

        // A shadowed name resolves to the declaration that shadows it, so this
        // settles the binding question the walk below cannot see from tokens.
        const returned_var = VarResolution.resolveVarIdFromIdentifier(self, binding, current_cfg) orelse return false;

        const parent_map = try self.getParentMap(tree);
        var node: u32 = ret_node;
        var frames: u32 = 0;
        while (frames < catch_payload_walk_frames) : (frames += 1) {
            if (node >= parent_map.len) return false;
            const parent = parent_map[node];
            if (parent == 0 or parent >= tags.len) return false;
            node = parent;
            if (tags[node] != .@"catch") continue;
            // The payload is scoped to the handler, so a `catch` this return
            // merely sits under binds nothing it can name.
            const handler = @intFromEnum(tree.nodes.items(.data)[node].node_and_node[1]);
            if (handler == 0 or !ast_walk.isAncestor(handler, ret_node, parent_map)) continue;
            const payload = catchPayloadToken(tree, node) orelse continue;
            if (ids.varId(payload) == returned_var) return true;
        }
        return false;
    }

    /// The name token a `catch` binds for its handler, or null when it binds
    /// none. The payload sits between the two pipes of `catch |err|`; a
    /// capture spelled `catch |*err|` lets the handler write through it and
    /// names the same binding.
    fn catchPayloadToken(tree: *const std.zig.Ast, catch_node: u32) ?u32 {
        const token_tags = tree.tokens.items(.tag);
        const catch_token = tree.nodes.items(.main_token)[catch_node];
        if (catch_token >= token_tags.len) return null;
        var token = catch_token + 1;
        if (token >= token_tags.len or token_tags[token] != .pipe) return null;
        token += 1;
        if (token < token_tags.len and token_tags[token] == .asterisk) token += 1;
        if (token >= token_tags.len or token_tags[token] != .identifier) return null;
        if (token + 1 >= token_tags.len or token_tags[token + 1] != .pipe) return null;
        return token;
    }

    /// Record an allocation and charge it to whoever owns the allocator.
    ///
    /// A local arena owns everything allocated through it, so the arena's own
    /// `deinit` releases these regions and returning the arena transfers them.
    /// An allocator that reaches the function through a caller-owned context is
    /// charged to the caller's release, but only when every call site in this
    /// file proves one; a plain allocator or an undisposed arena proves nothing
    /// and the allocation keeps being reported.
    fn trackAllocatedRegion(
        self: *AnalysisEngine,
        state: *ProgramState,
        region: ids.VarId,
        call_node: u32,
        current_cfg: *const Cfg,
    ) EngineError!void {
        try state.trackAllocation(region);
        const src = self.source orelse return;
        const tree = src.ast() catch return;
        const alloc_expr = ArenaProvenance.allocatorExpr(self, tree, call_node) orelse return;
        if (ArenaProvenance.localArenaOwner(self, tree, current_cfg, alloc_expr)) |arena| {
            try state.trackOwnership(region, arena);
            return;
        }
        if (ArenaProvenance.releasedByCallerArena(self, tree, current_cfg, alloc_expr)) {
            // The caller's arena owns this region beyond the callee's lifetime.
            state.trackEscape(region);
        }
    }

    /// Record an opened handle, and what the binding that took it now holds.
    ///
    /// The call on this path made the handle or the path would not be here,
    /// and a handle is never null: the fallback wrapped around the call stands
    /// only for the case where the call was never made at all. So a binding
    /// that took the acquisition's value here holds a non-null value, and an
    /// `if (handle)` whose false arm cannot be taken on this path is pruned
    /// rather than walked as if the handle might be missing.
    ///
    /// Only the value is settled, never the region. This says the handle is
    /// present; it does not say the handle is gone. A path that never made the
    /// acquisition never records the region in the first place, and a path
    /// where the guard's false arm is still reachable still holds the handle,
    /// still releases nothing on that arm, and is still reported as the orphan
    /// it is.
    fn trackOpenedHandle(state: *ProgramState, region: ids.VarId) EngineError!void {
        try state.trackOpen(region);
        try state.setVar(region, .non_null);
    }

    /// A successful realloc consumed the block it was given: the replacement
    /// owns that memory from then on.
    ///
    /// `replacement` is the region the result is bound to. `bytes =
    /// allocator.realloc(bytes, n)` names one region on both sides, and by
    /// then the assignment has already replaced what that region held, so
    /// there is nothing left to consume; consuming it would mark the
    /// replacement freed and hide the leak it leaves behind.
    ///
    /// `resized_source` is that block's name read off the call before the
    /// store rewrote the alias graph, where the two names are the same one.
    /// That write is what promotes the alias outliving it over the name being
    /// replaced, so the name the resize was handed the block through stops
    /// holding the block there, and reading the call again after the store
    /// hands back the replacement and leaves the original alive under the name
    /// that took it over. Where nothing rewrote the graph the call answers the
    /// same both times, so `null` reads it here as it always was read.
    fn consumeReallocSource(
        self: *AnalysisEngine,
        state: *ProgramState,
        call_info: ResourceCalls.ResourceCall,
        replacement: ids.VarId,
        resized_source: ?ids.VarId,
        current_cfg: *const Cfg,
    ) EngineError!void {
        var source = resized_source;
        if (source == null) {
            const source_expr = call_info.target_expr orelse return;
            source = VarResolution.resolveVarIdFromExpr(self, source_expr, current_cfg);
        }
        const source_var = source orelse return;
        if (source_var == replacement) return;
        // Only a block this frame is holding can be consumed. A pointer it
        // never saw allocated has no region to release, and writing one here
        // would invent a double free at a later release of that same pointer.
        if (state.getRegionState(source_var) != .allocated) return;
        try state.trackFree(source_var, Ownership.resolveCallToken(self, call_info.call_node));
    }

    /// True when `expr` is a realloc whose source this frame is holding,
    /// which is the only block a successful resize can consume. A source
    /// this frame never saw allocated has no region to release, and writing
    /// one freed would report a double free at the next release of that same
    /// pointer instead of leaving the resize alone.
    fn holdsReallocSource(
        self: *AnalysisEngine,
        state: *ProgramState,
        expr: u32,
        current_cfg: *const Cfg,
    ) bool {
        const src = self.source orelse return false;
        const tree = src.ast() catch return false;
        const realloc = ResourceCalls.resolveResourceCallFromExpr(self, tree, expr) orelse return false;
        if (realloc.kind != .realloc) return false;
        const source_expr = realloc.target_expr orelse return false;
        const source_var = VarResolution.resolveVarIdFromExpr(self, source_expr, current_cfg) orelse return false;
        return state.getRegionState(source_var) == .allocated;
    }

    const DeclErrorUnionInfo = struct {
        status: ?bool,
        init_node: ?u32,
    };

    fn isDefinitelyErrorExpr(tree: *const std.zig.Ast, expr_node: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (expr_node >= tags.len) return false;

        switch (tags[expr_node]) {
            .error_value => return true,
            // `ErrorName.Member` is an error value whenever `ErrorName` names
            // an error set. Reading a named error as an ordinary value left
            // the path out of the error state, so the `errdefer` releases
            // that belong to it never ran and everything still live on that
            // path was reported as leaked.
            .field_access => {
                const datas = tree.nodes.items(.data);
                const main_tokens = tree.nodes.items(.main_token);
                const owner: u32 = @intFromEnum(datas[expr_node].node_and_token[0]);
                if (owner >= tags.len or tags[owner] != .identifier) return false;
                const owner_token = main_tokens[owner];
                if (owner_token >= tree.tokens.len or tree.tokenTag(owner_token) != .identifier) return false;
                return isErrorSetDeclNamed(tree, tree.tokenSlice(owner_token));
            },
            .@"switch", .switch_comma => {
                const full_switch = tree.switchFull(@enumFromInt(expr_node));
                if (full_switch.ast.cases.len == 0) return false;
                for (full_switch.ast.cases) |case_node| {
                    const full_case = tree.fullSwitchCase(case_node) orelse return false;
                    if (!isDefinitelyErrorExpr(tree, @intFromEnum(full_case.ast.target_expr))) {
                        return false;
                    }
                }
                return true;
            },
            .@"if", .if_simple => {
                const full_if = tree.fullIf(@enumFromInt(expr_node)) orelse return false;
                if (!isDefinitelyErrorExpr(tree, @intFromEnum(full_if.ast.then_expr))) return false;
                if (full_if.ast.else_expr.unwrap()) |else_node| {
                    return isDefinitelyErrorExpr(tree, @intFromEnum(else_node));
                }
                return false;
            },
            else => return false,
        }
    }

    /// True when a root declaration named `name` is an error set, either
    /// declared directly or through a `const` binding. Anything this cannot
    /// pin down - a local shadow, an unknown name, an enum or union of the
    /// same name - is not treated as an error, so the path stays an ordinary
    /// one.
    fn isErrorSetDeclNamed(tree: *const std.zig.Ast, name: []const u8) bool {
        const tags = tree.nodes.items(.tag);
        const token_tags = tree.tokens.items(.tag);

        for (tree.rootDecls()) |decl_node| {
            const decl: u32 = @intFromEnum(decl_node);
            if (decl >= tags.len) continue;
            switch (tags[decl]) {
                .simple_var_decl, .local_var_decl, .global_var_decl, .aligned_var_decl => {
                    const full = tree.fullVarDecl(@enumFromInt(decl)) orelse continue;
                    if (tree.tokenTag(full.ast.mut_token) != .keyword_const) continue;
                    const init_node = full.ast.init_node.unwrap() orelse continue;
                    if (tags[@intFromEnum(init_node)] != .error_set_decl) continue;
                    const token = full.ast.mut_token + 1;
                    if (token >= token_tags.len or token_tags[token] != .identifier) continue;
                    if (std.mem.eql(u8, tree.tokenSlice(token), name)) return true;
                },
                else => {},
            }
        }
        return false;
    }

    fn declErrorUnionInfo(tree: *const std.zig.Ast, decl_node: u32) DeclErrorUnionInfo {
        const tags = tree.nodes.items(.tag);
        if (decl_node >= tags.len) return .{ .status = null, .init_node = null };

        switch (tags[decl_node]) {
            .simple_var_decl,
            .aligned_var_decl,
            .local_var_decl,
            .global_var_decl,
            => {},
            else => return .{ .status = null, .init_node = null },
        }

        const full_decl = tree.fullVarDecl(@enumFromInt(decl_node)) orelse
            return .{ .status = null, .init_node = null };
        if (full_decl.ast.type_node.unwrap()) |type_node_idx| {
            const type_node = @intFromEnum(type_node_idx);
            return .{ .status = isErrorUnionTypeNode(tree, type_node), .init_node = null };
        }

        if (full_decl.ast.init_node.unwrap()) |init_node_idx| {
            const init_node = @intFromEnum(init_node_idx);
            if (initNodeImpliesErrorUnion(tree, init_node)) {
                return .{ .status = true, .init_node = null };
            }
            return .{ .status = null, .init_node = init_node };
        }

        return .{ .status = null, .init_node = null };
    }

    fn isErrorUnionTypeNode(tree: *const std.zig.Ast, type_node: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (type_node >= tags.len) return false;

        switch (tags[type_node]) {
            .error_union,
            .error_set_decl,
            .merge_error_sets,
            => return true,
            .identifier => {
                const main_tokens = tree.nodes.items(.main_token);
                const token_tags = tree.tokens.items(.tag);
                const token = main_tokens[type_node];
                if (token < token_tags.len and token_tags[token] == .identifier) {
                    return std.mem.eql(u8, tree.tokenSlice(token), "anyerror");
                }
                return false;
            },
            else => return false,
        }
    }

    fn initNodeImpliesErrorUnion(tree: *const std.zig.Ast, init_node: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (init_node >= tags.len) return false;
        // `try` and `catch` produce their successful result values. Their
        // expression types, rather than their syntax, determine whether a
        // returned local still carries an error union.
        return tags[init_node] == .error_value;
    }

    /// Get the count of pruned paths
    pub fn getPrunedPathCount(self: *const AnalysisEngine) u32 {
        return self.pruned_path_count;
    }

    /// Get the exploded graph after analysis
    pub fn getGraph(self: *const AnalysisEngine) *const ExplodedGraph {
        return &self.graph;
    }

    /// Get the state at a specific exploded node
    pub fn getStateAt(self: *const AnalysisEngine, exploded_node_index: u32) ?*const ProgramState {
        if (self.graph.getNode(exploded_node_index)) |node| {
            return &node.state;
        }
        return null;
    }
};

test "AnalysisEngine source parents retain container scope after engine teardown" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Outer = struct {
        \\    const Inner = struct {
        \\        fn member(value: ?u8) void { _ = value; }
        \\    };
        \\};
    ;
    var parsed = try std.zig.Ast.parse(allocator, code, .zig);
    defer parsed.deinit(allocator);
    var source = Source.initParsed(allocator, "parent-scope.zig", &parsed);
    defer source.deinit();
    const tree = try source.ast();
    const root = @intFromEnum(tree.rootDecls()[0]);
    const function = for (tree.nodes.items(.tag), 0..) |tag, node| {
        if (tag == .fn_decl) break @as(u32, @intCast(node));
    } else return error.MissingFunction;
    const function_data = tree.nodes.items(.data)[function].node_and_node;
    const body = @intFromEnum(function_data[1]);
    var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&proto_buffer, function_data[0]) orelse
        return error.MissingPrototype;
    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    // Source metadata must survive an engine that cannot allocate its own map.
    var failing = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
    const parents = shared: {
        var engine = AnalysisEngine.initWithSource(failing.allocator(), &cfg, &source);
        defer engine.deinit();
        break :shared try engine.getParentMap(tree);
    };
    try std.testing.expect(ast_walk.isAncestor(root, body, parents));
    try std.testing.expect(!ast_walk.isAncestor(function, @intFromEnum(proto.ast.params[0]), parents));

    var next_engine = AnalysisEngine.initWithSource(failing.allocator(), &cfg, &source);
    defer next_engine.deinit();
    const next_parents = try next_engine.getParentMap(tree);
    try std.testing.expect(ast_walk.isAncestor(root, body, next_parents));
}

test "AnalysisEngine keeps foreign parent maps separate from source parents" {
    const allocator = std.testing.allocator;
    var source_allocator = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
    var source = Source.init(source_allocator.allocator(), "parents.zig", "fn root() void { if (true) { return; } }");
    defer source.deinit();
    var foreign = Source.init(allocator, "foreign-parents.zig", "fn other() void { return; }");
    defer foreign.deinit();
    const foreign_tree = try foreign.ast();
    const foreign_function = foreign_tree.rootDecls()[0];
    const foreign_body = foreign_tree.nodes.items(.data)[@intFromEnum(foreign_function)].node_and_node[1];
    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    var standalone = AnalysisEngine.init(allocator, &cfg);
    defer standalone.deinit();
    const standalone_parents = try standalone.getParentMap(foreign_tree);
    try std.testing.expect(ast_walk.isAncestor(@intFromEnum(foreign_function), @intFromEnum(foreign_body), standalone_parents));

    var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    // A foreign query must not parse an unrelated lazy source.
    const foreign_parents = try engine.getParentMap(foreign_tree);
    source_allocator.fail_index = std.math.maxInt(usize);
    const tree = try source.ast();
    const function = tree.rootDecls()[0];
    const body = tree.nodes.items(.data)[@intFromEnum(function)].node_and_node[1];
    const parents = try engine.getParentMap(tree);
    try std.testing.expect(ast_walk.isAncestor(@intFromEnum(function), @intFromEnum(body), parents));
    try std.testing.expect(ast_walk.isAncestor(@intFromEnum(foreign_function), @intFromEnum(foreign_body), foreign_parents));
    const foreign_again = try engine.getParentMap(foreign_tree);
    try std.testing.expect(ast_walk.isAncestor(@intFromEnum(foreign_function), @intFromEnum(foreign_body), foreign_again));
}

test "AnalysisEngine resolver cache failure stops before evaluating occurrence IDs" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "fn root() void { var value: i32 = 1; value = 2; }";
    var source = Source.init(allocator, "resolver-cache-oom.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = ids.astId(@intFromEnum(tree.rootDecls()[0]));
    var builder = CfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, fn_node)) orelse return error.MissingCfg;
    defer cfg.deinit();

    // Fail only the resolver cache; all graph and state allocations can succeed.
    var failing = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
    var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    engine.var_resolvers = std.AutoHashMap(AstNodeId, *VarResolver).init(failing.allocator());
    try std.testing.expectError(error.OutOfMemory, engine.run());
    try std.testing.expectEqual(@as(usize, 0), engine.getGraph().nodeCount());

    failing.fail_index = std.math.maxInt(usize);
    try engine.run();
    const declaration = for (cfg.nodes.items) |node| {
        if (node.ir_node.tag == .var_decl) {
            break node.ir_node.ast_node orelse return error.MissingDeclaration;
        }
    } else return error.MissingDeclaration;
    const var_id = AnalysisEngine.VarResolution.resolveVarIdFromVarDecl(&engine, declaration) orelse
        return error.MissingVariable;
    var found_exit = false;
    for (engine.getGraph().nodes.items) |node| {
        if (node.point.node_index != cfg.exit or node.point.kind != .post) continue;
        const value = node.state.getVar(var_id) orelse return error.MissingValue;
        try std.testing.expectEqual(@as(i64, 2), value.concrete_int);
        found_exit = true;
    }
    try std.testing.expect(found_exit);
}

test "AnalysisEngine resolver preparation cleans every partial allocation" {
    const code: [:0]const u8 =
        "fn root() void { var value: i32 = 1; value = 2;" ++
        "{ var value: i32 = 3; value = 4; } value = 5; }";
    var source = Source.init(std.testing.allocator, "resolver-oom.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    var cfg = Cfg.init(std.testing.allocator);
    defer cfg.deinit();
    cfg.fn_ast_node = ids.astId(@intFromEnum(tree.rootDecls()[0]));
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        testResolverPreparationAllocationFailure,
        .{ &source, &cfg },
    );
}

fn testResolverPreparationAllocationFailure(
    allocator: std.mem.Allocator,
    source: *Source,
    cfg: *const Cfg,
) !void {
    var engine = AnalysisEngine.initWithSource(allocator, cfg, source);
    defer engine.deinit();
    try AnalysisEngine.VarResolution.prepare(&engine, cfg);
    const tree = try source.ast();
    var declarations: [2]u32 = undefined;
    var declaration_count: usize = 0;
    var assignment_count: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tree.fullVarDecl(@enumFromInt(index))) |_| {
            try std.testing.expect(declaration_count < declarations.len);
            declarations[declaration_count] = @intCast(index);
            declaration_count += 1;
        }
        if (tag != .assign) continue;
        const declaration = declarations[if (assignment_count == 1) 1 else 0];
        const identifier = @intFromEnum(tree.nodes.items(.data)[index].node_and_node[0]);
        const expected = AnalysisEngine.VarResolution.resolveVarIdFromVarDecl(&engine, declaration) orelse
            return error.MissingVariable;
        const actual = AnalysisEngine.VarResolution.resolveVarIdFromIdentifier(&engine, identifier, cfg);
        try std.testing.expectEqual(expected, actual orelse return error.MissingVariable);
        const info = engine.resolveDeclInfoFromIdentifier(identifier, cfg) orelse
            return error.MissingDeclaration;
        try std.testing.expectEqual(declaration, info.decl_node);
        try std.testing.expect(!info.is_top_level);
        assignment_count += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), declaration_count);
    try std.testing.expectEqual(@as(usize, 3), assignment_count);
}

test "AnalysisEngine inline CFG cache failure propagates without losing ownership" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "fn root() void { callee(); } fn callee() void {}";
    var source = Source.init(allocator, "inline-cfg-oom.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = ids.astId(@intFromEnum(tree.rootDecls()[0]));
    var builder = CfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, fn_node)) orelse return error.MissingCfg;
    defer cfg.deinit();

    // A cache failure must not turn an internal call into an opaque external call.
    var failing = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
    var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    engine.function_cfgs = std.AutoHashMap(AstNodeId, FunctionCfgEntry).init(failing.allocator());
    engine.setUseSummaries(false);
    try std.testing.expectError(error.OutOfMemory, engine.run());
    try std.testing.expectEqual(@as(u32, 0), engine.getInlinedCallCount());
    for (engine.getGraph().nodes.items) |node| {
        try std.testing.expect(node.point.cfg != &cfg or node.point.node_index != cfg.exit);
    }
}

test "AnalysisEngine propagates lazy source parsing failure" {
    var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{ .fail_index = 0 });
    var source = Source.init(failing.allocator(), "source-oom.zig", "fn root() void {}");
    defer source.deinit();
    var cfg = Cfg.init(std.testing.allocator);
    defer cfg.deinit();
    cfg.entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    cfg.exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    try cfg.addEdge(cfg.entry, cfg.exit);
    var engine = AnalysisEngine.initWithSource(std.testing.allocator, &cfg, &source);
    defer engine.deinit();
    try std.testing.expectError(error.OutOfMemory, engine.run());
    try std.testing.expectEqual(@as(usize, 0), engine.getGraph().nodeCount());
}

test "AnalysisEngine entered inline metadata propagates every allocation failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        testEnteredFunctionPreparation,
        .{false},
    );
}

test "AnalysisEngine preseeded work prepares callees and suspended callers" {
    try testEnteredFunctionPreparation(std.testing.allocator, true);
}

fn testEnteredFunctionPreparation(allocator: std.mem.Allocator, preseeded: bool) !void {
    const code: [:0]const u8 =
        "fn root() void { caller(); }" ++
        "fn caller() void { callee(); var parent_value: i32 = 1; parent_value = 2; }" ++
        "fn callee() void { var child_value: i32 = 3; child_value = 4; }";
    var source = Source.init(std.testing.allocator, "entered-metadata.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    const functions = tree.rootDecls();
    var builder = CfgBuilder.init(std.testing.allocator);
    var cfg = (try builder.buildFromFn(&source, ids.astId(@intFromEnum(functions[0])))) orelse
        return error.MissingCfg;
    defer cfg.deinit();
    var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    engine.setUseSummaries(false);

    if (preseeded) {
        const caller = (try engine.getOrBuildFunctionCfg(ids.astId(@intFromEnum(functions[1])))) orelse
            return error.MissingCaller;
        const callee = (try engine.getOrBuildFunctionCfg(ids.astId(@intFromEnum(functions[2])))) orelse
            return error.MissingCallee;
        const root_call = for (cfg.nodes.items) |node| {
            if (node.ir_node.tag == .call) break node.index;
        } else return error.MissingCall;
        const caller_call = for (caller.nodes.items) |node| {
            if (node.ir_node.tag == .call) break node.index;
        } else return error.MissingCall;
        const caller_return = for (caller.edges.items) |edge| {
            if (edge.from == caller_call) break edge.to;
        } else return error.MissingReturn;
        var initial = ProgramState.init(allocator);
        var owns_initial = true;
        defer if (owns_initial) initial.deinit();
        initial.incrementInlineDepth();
        try initial.pushCallSite(.{
            .call_node = root_call,
            .caller_cfg = &cfg,
            .return_node = cfg.exit,
        });
        initial.incrementInlineDepth();
        try initial.pushCallSite(.{
            .call_node = caller_call,
            .caller_cfg = caller,
            .return_node = caller_return,
        });
        const seeded = try engine.graph.getOrCreateNode(ProgramPoint.initPre(callee.entry, callee), &initial);
        owns_initial = seeded.caller_should_deinit;
        try engine.worklist.append(allocator, .{
            .node_index = seeded.index,
            .edge_kind = .normal,
            .pending_constraint = null,
            .cfg = callee,
        });
    }

    try engine.run();
    var parent_var: ?ids.VarId = null;
    var child_var: ?ids.VarId = null;
    for (0..tree.nodes.len) |index| {
        const declaration = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
        const token = declaration.ast.mut_token + 1;
        const name = tree.tokenSlice(token);
        if (std.mem.eql(u8, name, "parent_value")) parent_var = ids.varId(token);
        if (std.mem.eql(u8, name, "child_value")) child_var = ids.varId(token);
    }
    var found_exit = false;
    for (engine.getGraph().nodes.items) |node| {
        if (node.point.cfg != &cfg) continue;
        if (node.point.node_index != cfg.exit or node.point.kind != .post) continue;
        const parent = node.state.getVar(parent_var orelse return error.MissingParent) orelse
            return error.MissingValue;
        const child = node.state.getVar(child_var orelse return error.MissingChild) orelse
            return error.MissingValue;
        try std.testing.expectEqual(@as(i64, 2), parent.concrete_int);
        try std.testing.expectEqual(@as(i64, 4), child.concrete_int);
        try std.testing.expectEqual(@as(usize, 0), node.state.call_stack.items.len);
        found_exit = true;
    }
    try std.testing.expect(found_exit);
}

test "AnalysisEngine cached CFG registration failure retains artifact ownership" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "cached-cfg-oom.zig", "fn callee() void {}");
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = ids.astId(@intFromEnum(tree.rootDecls()[0]));
    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    var artifacts = CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    const cached = blk: {
        var owner = AnalysisEngine.initWithSource(allocator, &cfg, &source);
        defer owner.deinit();
        owner.setCachedArtifacts(&artifacts);
        break :blk (try owner.getOrBuildFunctionCfg(fn_node)) orelse return error.MissingCfg;
    };

    var failing = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
    var engine = AnalysisEngine.init(failing.allocator(), &cfg);
    defer engine.deinit();
    engine.setCachedArtifacts(&artifacts);
    try std.testing.expectError(error.OutOfMemory, engine.getOrBuildFunctionCfg(fn_node));
    try std.testing.expectEqual(cached, artifacts.getCfg(ids.astIndex(fn_node)).?);
    failing.fail_index = std.math.maxInt(usize);
    const registered = (try engine.getOrBuildFunctionCfg(fn_node)) orelse return error.MissingCfg;
    try std.testing.expectEqual(cached, registered);
    try std.testing.expectEqualStrings("callee", registered.fn_name.?);
}

test "AnalysisEngine state cap stops distinct inline call contexts" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "fn caller() void { callee(); callee(); } fn callee() void {}";
    var source = Source.init(allocator, "inline-cap.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .fn_decl) break ids.astId(@intCast(index));
    } else return error.TestUnexpectedResult;
    var builder = CfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, fn_node)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    for ([_]bool{ false, true }) |use_widening| {
        var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
        defer engine.deinit();
        engine.setUseSummaries(false);
        engine.setUseWidening(use_widening);
        engine.setMaxStatesPerPoint(1);
        try std.testing.expectError(error.AnalysisLimitExceeded, engine.run());
        try std.testing.expectEqual(@as(u32, 1), engine.getInlinedCallCount());
        var counts = engine.graph.point_state_counts.valueIterator();
        while (counts.next()) |count| {
            try std.testing.expect(count.* <= 1);
        }
    }
}

test "AnalysisEngine zero state cap stops before seeding" {
    const allocator = std.testing.allocator;
    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    cfg.entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();
    engine.setMaxStatesPerPoint(0);
    try std.testing.expectError(error.AnalysisLimitExceeded, engine.run());
    try std.testing.expectEqual(@as(usize, 0), engine.getGraph().nodeCount());
}

test "AnalysisEngine transfer survives graph relocation and allocation failure" {
    var relocating = std.testing.FailingAllocator.init(std.testing.allocator, .{
        .resize_fail_index = 0,
    });
    // Every resize/remap fails, so node-array growth allocates before freeing
    // its old storage. Later allocations may reuse an earlier address.
    try testTraversalAllocationFailure(relocating.allocator());
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testTraversalAllocationFailure, .{});
}

fn testTraversalAllocationFailure(allocator: std.mem.Allocator) !void {
    var cfg = Cfg.init(std.testing.allocator);
    defer cfg.deinit();
    const entry = try cfg.addNode(cfg_mod.IrNode.initWithAst(.var_decl, 100));
    const left = try cfg.addNode(cfg_mod.IrNode.initWithAst(.var_decl, 200));
    const right = try cfg.addNode(cfg_mod.IrNode.initWithAst(.var_decl, 300));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;
    try cfg.addEdge(entry, left);
    try cfg.addEdge(entry, right);
    try cfg.addEdge(left, exit);
    try cfg.addEdge(right, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();
    engine.setUseWidening(true);
    // Force the first processed state to grow the node array.
    try engine.graph.nodes.ensureTotalCapacityPrecise(allocator, 1);
    var initial = ProgramState.init(allocator);
    var owns_initial = true;
    defer if (owns_initial) initial.deinit();
    try initial.setVar(ids.varId(99), .{ .concrete_int = 42 });
    const seeded = try engine.graph.getOrCreateNode(ProgramPoint.initPre(entry, &cfg), &initial);
    owns_initial = seeded.caller_should_deinit;
    try engine.worklist.append(allocator, .{
        .node_index = seeded.index,
        .edge_kind = .normal,
        .pending_constraint = null,
        .cfg = &cfg,
    });
    try engine.run();

    const original = engine.getStateAt(seeded.index) orelse return error.TestUnexpectedResult;
    const original_value = original.getVar(ids.varId(99)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(i64, 42), original_value.concrete_int);
    try std.testing.expect(original.getVar(ids.varId(100)) == null);
    var found_left = false;
    var found_right = false;
    for (engine.getGraph().nodes.items) |node| {
        if (node.point.kind != .post) continue;
        if (node.point.node_index == left) {
            const value = node.state.getVar(ids.varId(200)) orelse return error.TestUnexpectedResult;
            try std.testing.expect(value.isUnknown());
            try std.testing.expect(node.state.getVar(ids.varId(300)) == null);
            found_left = true;
        } else if (node.point.node_index == right) {
            const value = node.state.getVar(ids.varId(300)) orelse return error.TestUnexpectedResult;
            try std.testing.expect(value.isUnknown());
            try std.testing.expect(node.state.getVar(ids.varId(200)) == null);
            found_right = true;
        }
    }
    try std.testing.expect(found_left);
    try std.testing.expect(found_right);
}

test "AnalysisEngine cached CFGs outlive the engine allocator" {
    var source = Source.init(std.testing.allocator, "artifact-allocator.zig", "fn callee() void {}");
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .fn_decl) break ids.astId(@intCast(index));
    } else return error.TestUnexpectedResult;
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testCachedCfgAllocatorOwnership, .{ &source, fn_node });
}

fn testCachedCfgAllocatorOwnership(allocator: std.mem.Allocator, source: *Source, fn_node: AstNodeId) !void {
    var artifacts = CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var root = Cfg.init(std.testing.allocator);
    defer root.deinit();
    {
        var storage: [16 * 1024]u8 = undefined;
        var scratch = std.heap.FixedBufferAllocator.init(&storage);
        var engine = AnalysisEngine.initWithSource(scratch.allocator(), &root, source);
        defer engine.deinit();
        engine.setCachedArtifacts(&artifacts);
        // The CFG is built and published to the artifact cache while the engine's
        // allocator is the scratch buffer, so the cached copy has to stay valid
        // once that allocator is gone.
        if (try engine.getOrBuildFunctionCfg(fn_node)) |callee| {
            try std.testing.expectEqual(cfg_mod.IrTag.fn_exit, callee.getNode(callee.exit).?.ir_node.tag);
        } else {
            return error.TestUnexpectedResult;
        }
    }
    const cached = artifacts.getCfg(ids.astIndex(fn_node)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqualStrings("callee", cached.fn_name.?);
    try std.testing.expectEqual(cfg_mod.IrTag.fn_entry, cached.getNode(cached.entry).?.ir_node.tag);
    try std.testing.expectEqual(cfg_mod.IrTag.fn_exit, cached.getNode(cached.exit).?.ir_node.tag);
}

test "AnalysisEngine simple CFG traversal" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;
    try cfg.addEdge(entry, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    const graph = engine.getGraph();
    try testing.expect(graph.nodeCount() >= 4);

    const node0 = graph.getNode(0) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(entry, node0.point.node_index);
    try testing.expectEqual(ProgramPoint.Kind.pre, node0.point.kind);
}

test "AnalysisEngine deduplication prevents infinite loops" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const header = try cfg.addNode(cfg_mod.IrNode.init(.loop_header));
    const body = try cfg.addNode(cfg_mod.IrNode.init(.loop_body));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, header);
    try cfg.addEdgeWithKind(header, body, .branch_true);
    try cfg.addEdgeWithKind(header, exit, .loop_exit);
    try cfg.addEdgeWithKind(body, header, .loop_back);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    const graph = engine.getGraph();

    try testing.expect(graph.nodeCount() > 0);
    try testing.expect(graph.nodeCount() <= 12);
}

test "AnalysisEngine branching CFG" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const branch = try cfg.addNode(cfg_mod.IrNode.init(.branch));
    const then_node = try cfg.addNode(cfg_mod.IrNode.init(.block));
    const else_node = try cfg.addNode(cfg_mod.IrNode.init(.block));
    const merge = try cfg.addNode(cfg_mod.IrNode.init(.nop));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, branch);
    try cfg.addEdgeWithKind(branch, then_node, .branch_true);
    try cfg.addEdgeWithKind(branch, else_node, .branch_false);
    try cfg.addEdge(then_node, merge);
    try cfg.addEdge(else_node, merge);
    try cfg.addEdge(merge, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    const graph = engine.getGraph();

    try testing.expect(graph.nodeCount() >= 12);
}

test "AnalysisEngine with var_decl propagates state" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const var_decl = try cfg.addNode(cfg_mod.IrNode.initWithAst(.var_decl, 100));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, var_decl);
    try cfg.addEdge(var_decl, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    const graph = engine.getGraph();
    try testing.expect(graph.nodeCount() >= 6);

    // Find the post-state of var_decl node
    var found_var_decl_post = false;
    for (graph.nodes.items) |node| {
        if (node.point.node_index == var_decl and node.point.kind == .post) {
            const val = node.state.getVar(ids.varId(100));
            try testing.expect(val != null);
            try testing.expect(val.?.isUnknown());
            found_var_decl_post = true;
            break;
        }
    }
    try testing.expect(found_var_decl_post);
}

test "AnalysisEngine try edge sets error state" {
    const allocator = std.testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const try_node = try cfg.addNode(cfg_mod.IrNode.init(.try_expr));
    const success_node = try cfg.addNode(cfg_mod.IrNode.init(.block));
    const error_node = try cfg.addNode(cfg_mod.IrNode.init(.block));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));

    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, try_node);
    try cfg.addEdgeWithKind(try_node, success_node, .try_success);
    try cfg.addEdgeWithKind(try_node, error_node, .try_error);
    try cfg.addEdge(success_node, exit);
    try cfg.addEdge(error_node, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    const graph = engine.getGraph();

    var found_error_state = false;
    var found_normal_state = false;

    for (graph.nodes.items) |node| {
        if (node.point.node_index == error_node and node.point.kind == .pre) {
            if (node.state.isErrorPath()) {
                found_error_state = true;
            }
        }
        if (node.point.node_index == success_node and node.point.kind == .pre) {
            if (node.state.isNormalPath()) {
                found_normal_state = true;
            }
        }
    }

    try std.testing.expect(found_error_state);
    try std.testing.expect(found_normal_state);
}

test "AnalysisEngine catch edge handles error" {
    const allocator = std.testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const try_node = try cfg.addNode(cfg_mod.IrNode.init(.try_expr));
    const catch_node = try cfg.addNode(cfg_mod.IrNode.init(.catch_expr));
    const after_catch = try cfg.addNode(cfg_mod.IrNode.init(.block));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));

    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, try_node);
    try cfg.addEdgeWithKind(try_node, catch_node, .try_error);
    try cfg.addEdgeWithKind(catch_node, after_catch, .catch_error);
    try cfg.addEdgeWithKind(after_catch, exit, .catch_success);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    const graph = engine.getGraph();

    var found_handled_state = false;
    var found_normal_after_catch = false;

    for (graph.nodes.items) |node| {
        if (node.point.node_index == after_catch and node.point.kind == .pre) {
            if (node.state.getErrorState() == .error_handled) {
                found_handled_state = true;
            }
        }
        if (node.point.node_index == exit and node.point.kind == .pre) {
            if (node.state.isNormalPath()) {
                found_normal_after_catch = true;
            }
        }
    }

    try std.testing.expect(found_handled_state);
    try std.testing.expect(found_normal_after_catch);
}

test "AnalysisEngine errdefer only on error path" {
    const allocator = std.testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const try_node = try cfg.addNode(cfg_mod.IrNode.init(.try_expr));
    const success_node = try cfg.addNode(cfg_mod.IrNode.init(.block));
    const errdefer_node = try cfg.addNode(cfg_mod.IrNode.init(.errdefer_stmt));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));

    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, try_node);
    try cfg.addEdgeWithKind(try_node, success_node, .try_success);
    try cfg.addEdgeWithKind(try_node, errdefer_node, .try_error);
    try cfg.addEdgeWithKind(success_node, errdefer_node, .errdefer_edge);
    try cfg.addEdge(errdefer_node, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    const graph = engine.getGraph();

    var errdefer_reached_from_error = false;
    var errdefer_reached_from_success = false;

    for (graph.nodes.items) |node| {
        if (node.point.node_index == errdefer_node and node.point.kind == .pre) {
            if (node.state.isErrorPath()) {
                errdefer_reached_from_error = true;
            } else if (node.state.isNormalPath()) {
                errdefer_reached_from_success = true;
            }
        }
    }

    try std.testing.expect(errdefer_reached_from_error);
    try std.testing.expect(!errdefer_reached_from_success);
}

test "AnalysisEngine max inline depth configuration" {
    const allocator = std.testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try std.testing.expectEqual(default_max_inline_depth, engine.max_inline_depth);

    engine.setMaxInlineDepth(5);
    try std.testing.expectEqual(@as(u32, 5), engine.max_inline_depth);

    engine.setMaxInlineDepth(0);
    try std.testing.expectEqual(@as(u32, 0), engine.max_inline_depth);
}

test "AnalysisEngine inlined call count starts at zero" {
    const allocator = std.testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;
    try cfg.addEdge(entry, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try std.testing.expectEqual(@as(u32, 0), engine.getInlinedCallCount());

    try engine.run();

    // Without source, no calls can be inlined
    try std.testing.expectEqual(@as(u32, 0), engine.getInlinedCallCount());
}

test "AnalysisEngine with source processes simple function" {
    const allocator = std.testing.allocator;

    // Simple source with a function
    const code: [:0]const u8 =
        \\fn foo() void {
        \\    return;
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    // Find the fn_decl node
    const tree = source.ast() catch return;
    const tags = tree.nodes.items(.tag);
    var fn_node: ?AstNodeId = null;
    for (tags, 0..) |tag, i| {
        if (tag == .fn_decl) {
            fn_node = ids.astId(@intCast(i));
            break;
        }
    }
    const fn_idx = fn_node orelse return; // No fn_decl found, skip test

    // Build CFG for the function
    var builder = CfgBuilder.init(allocator);
    var cfg_opt = builder.buildFromFn(&source, fn_idx) catch return;

    if (cfg_opt) |*cfg| {
        defer cfg.deinit();

        var engine = AnalysisEngine.initWithSource(allocator, cfg, &source);
        defer engine.deinit();

        try engine.run();

        // Should complete without error
        try std.testing.expect(engine.getGraph().nodeCount() > 0);
    }
}

test "AnalysisEngine transfer function handles call nodes" {
    const allocator = std.testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const call = try cfg.addNode(cfg_mod.IrNode.initWithAst(.call, 100));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, call);
    try cfg.addEdge(call, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    // Should complete without error - call is treated as unknown effect
    const graph = engine.getGraph();
    try std.testing.expect(graph.nodeCount() >= 6); // entry pre/post, call pre/post, exit pre/post
}

test "AnalysisEngine store tracks allocator alloc/free" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn foo(allocator: std.mem.Allocator) !void {
        \\    var ptr = try allocator.alloc(u8, 1);
        \\    allocator.free(ptr);
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = source.ast() catch return;
    const tags = tree.nodes.items(.tag);
    const token_tags = tree.tokens.items(.tag);

    var fn_node: ?AstNodeId = null;
    var ptr_var_id: ?ids.VarId = null;
    for (tags, 0..) |tag, i| {
        if (tag == .fn_decl) {
            fn_node = ids.astId(@intCast(i));
        }
        switch (tag) {
            .simple_var_decl,
            .aligned_var_decl,
            .local_var_decl,
            .global_var_decl,
            => {
                const full = tree.fullVarDecl(@enumFromInt(i)) orelse continue;
                const name_token = full.ast.mut_token + 1;
                if (name_token >= token_tags.len or token_tags[name_token] != .identifier) continue;
                const name = tree.tokenSlice(name_token);
                if (std.mem.eql(u8, name, "ptr")) {
                    ptr_var_id = ids.varId(name_token);
                }
            },
            else => {},
        }
    }
    const fn_idx = fn_node orelse return;
    const region = ptr_var_id orelse return;

    var builder = CfgBuilder.init(allocator);
    var cfg_opt = builder.buildFromFn(&source, fn_idx) catch return;
    if (cfg_opt) |*cfg| {
        defer cfg.deinit();

        var engine = AnalysisEngine.initWithSource(allocator, cfg, &source);
        defer engine.deinit();

        try engine.run();

        var call_node_id: ?CfgNodeId = null;
        var call_count: usize = 0;
        for (cfg.nodes.items) |node| {
            if (node.ir_node.tag == .call) {
                call_node_id = node.index;
                call_count += 1;
            }
        }
        try testing.expect(call_count >= 1);
        const call_id = call_node_id orelse return;

        var found = false;
        for (engine.getGraph().nodes.items) |node| {
            if (node.point.node_index == call_id and node.point.kind == .post) {
                const state = &node.state;
                try testing.expectEqual(ResourceState.freed, state.getRegionState(region).?);
                try testing.expectEqual(@as(usize, 0), state.getStoreViolations().len);
                found = true;
                break;
            }
        }
        try testing.expect(found);
    }
}

test "AnalysisEngine store records double free violations" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const StoreViolationKind = @import("../store.zig").StoreViolationKind;

    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn foo(allocator: std.mem.Allocator) !void {
        \\    var ptr = try allocator.alloc(u8, 1);
        \\    allocator.free(ptr);
        \\    allocator.free(ptr);
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = source.ast() catch return;
    const tags = tree.nodes.items(.tag);
    const token_tags = tree.tokens.items(.tag);

    var fn_node: ?AstNodeId = null;
    var ptr_var_id: ?ids.VarId = null;
    for (tags, 0..) |tag, i| {
        if (tag == .fn_decl) {
            fn_node = ids.astId(@intCast(i));
        }
        switch (tag) {
            .simple_var_decl,
            .aligned_var_decl,
            .local_var_decl,
            .global_var_decl,
            => {
                const full = tree.fullVarDecl(@enumFromInt(i)) orelse continue;
                const name_token = full.ast.mut_token + 1;
                if (name_token >= token_tags.len or token_tags[name_token] != .identifier) continue;
                const name = tree.tokenSlice(name_token);
                if (std.mem.eql(u8, name, "ptr")) {
                    ptr_var_id = ids.varId(name_token);
                }
            },
            else => {},
        }
    }
    const fn_idx = fn_node orelse return;
    const region = ptr_var_id orelse return;

    var builder = CfgBuilder.init(allocator);
    var cfg_opt = builder.buildFromFn(&source, fn_idx) catch return;
    if (cfg_opt) |*cfg| {
        defer cfg.deinit();

        var engine = AnalysisEngine.initWithSource(allocator, cfg, &source);
        defer engine.deinit();

        try engine.run();

        var call_node_id: ?CfgNodeId = null;
        var call_count: usize = 0;
        for (cfg.nodes.items) |node| {
            if (node.ir_node.tag == .call) {
                call_node_id = node.index;
                call_count += 1;
            }
        }
        try testing.expect(call_count >= 2);
        const second_call = call_node_id orelse return;

        var found = false;
        for (engine.getGraph().nodes.items) |node| {
            if (node.point.node_index == second_call and node.point.kind == .post) {
                const state = &node.state;
                try testing.expectEqual(ResourceState.freed, state.getRegionState(region).?);
                try testing.expectEqual(@as(usize, 1), state.getStoreViolations().len);
                try testing.expectEqual(StoreViolationKind.double_free, state.getStoreViolations()[0].kind);
                found = true;
                break;
            }
        }
        try testing.expect(found);
    }
}

test "AnalysisEngine store tracks self allocator calls" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Foo = struct {
        \\    allocator: std.mem.Allocator,
        \\    fn bar(self: *Foo) !void {
        \\        var ptr = try self.allocator.alloc(u8, 1);
        \\        self.allocator.free(ptr);
        \\        self.allocator.free(ptr);
        \\    }
        \\};
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = source.ast() catch return;
    const tags = tree.nodes.items(.tag);
    const token_tags = tree.tokens.items(.tag);

    var fn_node: ?AstNodeId = null;
    var ptr_var_id: ?ids.VarId = null;
    for (tags, 0..) |tag, i| {
        if (tag == .fn_decl) {
            fn_node = ids.astId(@intCast(i));
        }
        switch (tag) {
            .simple_var_decl,
            .aligned_var_decl,
            .local_var_decl,
            .global_var_decl,
            => {
                const full = tree.fullVarDecl(@enumFromInt(i)) orelse continue;
                const name_token = full.ast.mut_token + 1;
                if (name_token >= token_tags.len or token_tags[name_token] != .identifier) continue;
                const name = tree.tokenSlice(name_token);
                if (std.mem.eql(u8, name, "ptr")) {
                    ptr_var_id = ids.varId(name_token);
                }
            },
            else => {},
        }
    }
    const fn_idx = fn_node orelse return;
    const region = ptr_var_id orelse return;

    var builder = CfgBuilder.init(allocator);
    var cfg_opt = builder.buildFromFn(&source, fn_idx) catch return;
    if (cfg_opt) |*cfg| {
        defer cfg.deinit();

        var engine = AnalysisEngine.initWithSource(allocator, cfg, &source);
        defer engine.deinit();

        try engine.run();

        var found = false;
        for (engine.getGraph().nodes.items) |node| {
            if (node.point.kind == .post) {
                const state = &node.state;
                if (state.getRegionState(region)) |region_state| {
                    if (region_state == .freed and state.getStoreViolations().len == 1) {
                        found = true;
                        break;
                    }
                }
            }
        }
        try testing.expect(found);
    }
}

const mixed_summary_call_source: [:0]const u8 =
    \\fn target(fail: bool) !void {
    \\    if (fail) return error.Failed;
    \\}
    \\fn caller(fail: bool) !void {
    \\    try target(fail);
    \\}
;

fn testSummaryCallOutcomes(
    allocator: std.mem.Allocator,
    code: [:0]const u8,
    initial_error: ErrorState,
    expected_errors: []const ErrorState,
) !void {
    var source = Source.init(std.testing.allocator, "summary-call.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    const call_ast_node = for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .call, .call_comma, .call_one, .call_one_comma => break @as(u32, @intCast(index)),
            else => {},
        }
    } else return error.MissingCall;

    // The builder lowers try calls as try_expr; retain the real call AST here.
    var cfg = Cfg.init(std.testing.allocator);
    defer cfg.deinit();
    cfg.entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const call = try cfg.addNode(cfg_mod.IrNode.initWithAst(.call, call_ast_node));
    cfg.exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.fn_name = "caller";
    try cfg.addEdge(cfg.entry, call);
    try cfg.addEdge(call, cfg.exit);

    // Compute the real summary before injecting failures into its application.
    var summary_engine = AnalysisEngine.initWithSource(std.testing.allocator, &cfg, &source);
    defer summary_engine.deinit();
    try summary_engine.buildFunctionIndex(&source);
    cfg.fn_ast_node = summary_engine.function_names.get("caller") orelse
        return error.MissingCaller;
    const target = summary_engine.function_names.get("target") orelse return error.MissingTarget;
    var summary = (try AnalysisEngine.Summaries.computeSummary(&summary_engine, target)) orelse
        return error.MissingSummary;
    var owns_summary = true;
    defer if (owns_summary) summary.deinit();

    var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    try engine.buildFunctionIndex(&source);
    try AnalysisEngine.VarResolution.prepare(&engine, &cfg);
    try engine.summary_cache.put(summary);
    owns_summary = false;

    var initial = ProgramState.init(allocator);
    var owns_initial = true;
    defer if (owns_initial) initial.deinit();
    initial.setErrorState(initial_error);
    // Keep owned state storage so allocation failures also exercise both clones.
    try initial.addConstraint(Constraint.literalBool(true));
    const seeded = try engine.getOrCreateNode(ProgramPoint.initPre(call, &cfg), &initial, .{});
    owns_initial = seeded.caller_should_deinit;

    // An empty worklist makes the summary enqueue allocate under failure injection.
    try engine.processNode(seeded.index, .normal, null, &cfg);
    try engine.run();

    var actual_counts = [_]usize{ 0, 0, 0 };
    for (engine.getGraph().nodes.items) |node| {
        if (node.point.cfg != &cfg) continue;
        if (node.point.node_index != cfg.exit or node.point.kind != .post) continue;
        actual_counts[@intFromEnum(node.state.error_state)] += 1;
    }
    var expected_counts = [_]usize{ 0, 0, 0 };
    for (expected_errors) |error_state| {
        expected_counts[@intFromEnum(error_state)] += 1;
    }
    try std.testing.expectEqualSlices(usize, &expected_counts, &actual_counts);
    try std.testing.expectEqual(@as(u32, 1), engine.getSummaryUseCount());
    try std.testing.expectEqual(@as(u32, 0), engine.getInlinedCallCount());
    const used_summary = engine.getSummaryCache().summaries.get(target) orelse
        return error.MissingSummary;
    try std.testing.expectEqual(@as(u32, 1), used_summary.use_count);
}

test "AnalysisEngine mixed summary reaches normal and error caller exits" {
    try testSummaryCallOutcomes(
        std.testing.allocator,
        mixed_summary_call_source,
        .normal,
        &.{ .normal, .error_active },
    );
}

test "AnalysisEngine always-error summary reaches only the error caller exit" {
    const code: [:0]const u8 =
        \\fn target() !void { return error.Failed; }
        \\fn caller() !void { try target(); }
    ;
    try testSummaryCallOutcomes(std.testing.allocator, code, .normal, &.{.error_active});
}

test "AnalysisEngine successful summary preserves a pending caller error" {
    const code: [:0]const u8 =
        \\fn target() void {}
        \\fn caller() void { target(); }
    ;
    try testSummaryCallOutcomes(std.testing.allocator, code, .error_active, &.{.error_active});
}

test "AnalysisEngine summary fork owns both outcomes on allocation failure" {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        testSummaryCallOutcomes,
        .{ mixed_summary_call_source, ErrorState.normal, &[_]ErrorState{ .normal, .error_active } },
    );
    // Both outcomes deduplicate when the caller already has a pending error.
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        testSummaryCallOutcomes,
        .{ mixed_summary_call_source, ErrorState.error_active, &[_]ErrorState{.error_active} },
    );
}

test "AnalysisEngine summary cache initialization" {
    const allocator = std.testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    // Summary cache should be initialized
    try std.testing.expectEqual(@as(u32, 0), engine.getSummaryUseCount());

    // use_summaries should default to true
    try std.testing.expect(engine.use_summaries);

    // Can disable summaries
    engine.setUseSummaries(false);
    try std.testing.expect(!engine.use_summaries);
}

test "AnalysisEngine summary use count" {
    const allocator = std.testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;
    try cfg.addEdge(entry, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    // Without any calls, summary use count should be 0
    try engine.run();
    try std.testing.expectEqual(@as(u32, 0), engine.getSummaryUseCount());
}

test "AnalysisEngine widening simple loop converges without drops" {
    // Integration test: simple loop with state-changing operations.
    // Uses var_decl in the loop body to modify state on each iteration.
    // Note: When the same state is produced on successive iterations, deduplication
    // handles convergence. Widening only applies when states differ.
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    // CFG: entry -> loop_header -> loop_body (var_decl) -> loop_header (back edge)
    //                           -> exit (loop exit)
    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const header = try cfg.addNode(cfg_mod.IrNode.init(.loop_header));
    // Use var_decl with ast_node to trigger state changes in the loop body
    const body_ir = cfg_mod.IrNode.initWithAst(.var_decl, 100);
    const body = try cfg.addNode(body_ir);
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));

    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, header);
    try cfg.addEdgeWithKind(header, body, .branch_true);
    try cfg.addEdgeWithKind(header, exit, .loop_exit);
    try cfg.addEdgeWithKind(body, header, .loop_back);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    // Enable widening for this test
    engine.setUseWidening(true);
    // Set a low max_states_per_point
    engine.setMaxStatesPerPoint(5);

    try engine.run();

    const graph = engine.getGraph();

    // Analysis should complete without hitting state limits
    // Combination of deduplication and widening ensures convergence
    try testing.expect(graph.nodeCount() > 0);
    try testing.expect(graph.nodeCount() <= 20);

    // Verify widening infrastructure was used (visit tracking)
    // The header should be tracked for widening even if convergence happened via dedup
    try testing.expect(graph.getTrackedWideningPointCount() >= 1);
}

test "AnalysisEngine widening nested loops widen per header" {
    // Integration test: nested loops with separate loop headers
    // Verifies that each loop header maintains its own widening state.
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    // CFG: entry -> outer_header -> inner_header -> inner_body -> inner_header (back)
    //                            |                            -> outer_body
    //                            -> outer_exit -> exit
    //              outer_body -> outer_header (back)
    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const outer_header = try cfg.addNode(cfg_mod.IrNode.init(.loop_header));
    const inner_header = try cfg.addNode(cfg_mod.IrNode.init(.loop_header));

    const inner_body_ir = cfg_mod.IrNode.initWithAst(.var_decl, 100);
    const inner_body = try cfg.addNode(inner_body_ir);

    const outer_body_ir = cfg_mod.IrNode.initWithAst(.var_decl, 200);
    const outer_body = try cfg.addNode(outer_body_ir);

    const outer_exit_node = try cfg.addNode(cfg_mod.IrNode.init(.nop));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));

    cfg.entry = entry;
    cfg.exit = exit;

    // Entry to outer loop
    try cfg.addEdge(entry, outer_header);

    // Outer loop: header -> inner or exit
    try cfg.addEdgeWithKind(outer_header, inner_header, .branch_true);
    try cfg.addEdgeWithKind(outer_header, outer_exit_node, .loop_exit);

    // Inner loop: header -> body -> header (back) or -> outer_body (exit)
    try cfg.addEdgeWithKind(inner_header, inner_body, .branch_true);
    try cfg.addEdgeWithKind(inner_header, outer_body, .loop_exit);
    try cfg.addEdgeWithKind(inner_body, inner_header, .loop_back);

    // Outer loop back edge
    try cfg.addEdgeWithKind(outer_body, outer_header, .loop_back);

    // Exit
    try cfg.addEdge(outer_exit_node, exit);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    // Enable widening for this test
    engine.setUseWidening(true);
    engine.setMaxStatesPerPoint(5);

    try engine.run();

    const graph = engine.getGraph();

    // Verify that both loop headers are tracked separately for widening.
    // Each loop header has a distinct CFG node index, so they should have
    // different WideningKeys and be tracked independently.
    try testing.expect(graph.getTrackedWideningPointCount() >= 2);

    // Analysis should complete without hitting limits
    try testing.expect(graph.nodeCount() > 0);
}

test "AnalysisEngine widening error path in loop remains sound" {
    // Integration test: loop with error handling (try/catch)
    // Verifies that error_state is handled correctly during widening.
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    // CFG: entry -> header -> try_expr -> success -> body -> header (back)
    //                                  -> error -> error_handler -> header (back)
    //            -> exit
    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const header = try cfg.addNode(cfg_mod.IrNode.init(.loop_header));
    const try_node = try cfg.addNode(cfg_mod.IrNode.init(.try_expr));
    const success_body = try cfg.addNode(cfg_mod.IrNode.init(.block));
    const error_handler = try cfg.addNode(cfg_mod.IrNode.init(.catch_expr));
    const merge = try cfg.addNode(cfg_mod.IrNode.init(.nop));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));

    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, header);
    try cfg.addEdgeWithKind(header, try_node, .branch_true);
    try cfg.addEdgeWithKind(header, exit, .loop_exit);
    try cfg.addEdgeWithKind(try_node, success_body, .try_success);
    try cfg.addEdgeWithKind(try_node, error_handler, .try_error);
    try cfg.addEdge(success_body, merge);
    try cfg.addEdgeWithKind(error_handler, merge, .catch_error);
    try cfg.addEdgeWithKind(merge, header, .loop_back);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    // Enable widening for this test
    engine.setUseWidening(true);
    engine.setMaxStatesPerPoint(10);

    try engine.run();

    const graph = engine.getGraph();

    // Analysis should complete
    try testing.expect(graph.nodeCount() > 0);

    // Verify error path states exist at relevant nodes
    var found_error_path_at_handler = false;
    var found_normal_path_at_success = false;

    for (graph.nodes.items) |node| {
        if (node.point.node_index == error_handler and node.point.kind == .pre) {
            if (node.state.isErrorPath()) {
                found_error_path_at_handler = true;
            }
        }
        if (node.point.node_index == success_body and node.point.kind == .pre) {
            if (node.state.isNormalPath()) {
                found_normal_path_at_success = true;
            }
        }
    }

    // Error states should be tracked correctly through the loop
    try testing.expect(found_error_path_at_handler);
    try testing.expect(found_normal_path_at_success);
}

test "AnalysisEngine widening convergence stops exploration" {
    // Integration test: verifies that loop exploration is bounded.
    // When state doesn't change in the loop body, deduplication ensures
    // convergence by recognizing that we've seen this (point, state) before.
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    // Simple loop that doesn't change state - deduplication handles convergence
    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const header = try cfg.addNode(cfg_mod.IrNode.init(.loop_header));
    const body = try cfg.addNode(cfg_mod.IrNode.init(.nop)); // No state change
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));

    cfg.entry = entry;
    cfg.exit = exit;

    try cfg.addEdge(entry, header);
    try cfg.addEdgeWithKind(header, body, .branch_true);
    try cfg.addEdgeWithKind(header, exit, .loop_exit);
    try cfg.addEdgeWithKind(body, header, .loop_back);

    var engine = AnalysisEngine.init(allocator, &cfg);
    defer engine.deinit();

    try engine.run();

    const graph = engine.getGraph();

    // Analysis should complete and node count should be bounded
    // (deduplication prevents infinite exploration)
    try testing.expect(graph.nodeCount() > 0);
    try testing.expect(graph.nodeCount() <= 20);
}

test "AnalysisEngine widening regression test with real loop code" {
    // Fixture-based regression test: parses actual Zig code with a loop
    // and verifies that widening ensures convergence without state explosion.
    // This is the type of loop that could hit max_states_per_point without widening.
    const testing = std.testing;
    const allocator = testing.allocator;

    // Code with a for loop that iterates over a slice and allocates in each iteration.
    // This pattern is common in real code and was previously prone to state explosion.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn process(allocator: std.mem.Allocator, items: []const u8) !void {
        \\    for (items) |item| {
        \\        const buf = try allocator.alloc(u8, 1);
        \\        defer allocator.free(buf);
        \\        buf[0] = item;
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = source.ast() catch return;
    const tags = tree.nodes.items(.tag);
    var fn_node: ?AstNodeId = null;
    for (tags, 0..) |tag, i| {
        if (tag == .fn_decl) {
            fn_node = ids.astId(@intCast(i));
            break;
        }
    }
    const fn_idx = fn_node orelse return;

    var builder = CfgBuilder.init(allocator);
    var cfg_opt = builder.buildFromFn(&source, fn_idx) catch return;

    if (cfg_opt) |*cfg| {
        defer cfg.deinit();

        var engine = AnalysisEngine.initWithSource(allocator, cfg, &source);
        defer engine.deinit();

        // Set a low max_states_per_point to verify widening prevents state explosion
        engine.setMaxStatesPerPoint(5);

        try engine.run();

        const graph = engine.getGraph();

        // Analysis should complete successfully - widening prevents state explosion
        try testing.expect(graph.nodeCount() > 0);
    }
}

test "AnalysisEngine widening leaves a loop-free join precise" {
    // The branch join below is entered once per arm and can never be revisited,
    // so widening it merged both arms into one state whose resource was
    // `unknown` and the leak recorded at the function exit was lost. The loop in
    // front of it is the part that genuinely has to converge, and it still does:
    // its header is the widening point. The loop has to come first, because a
    // loop downstream of the join would merge the arms again at its own header
    // and hide the difference this test is about.
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn leaky(allocator: std.mem.Allocator, flag: bool) !void {
        \\    var i: usize = 0;
        \\    while (i < 4) : (i += 1) {
        \\        i += 1;
        \\    }
        \\    var ptr = try allocator.alloc(u8, 1);
        \\    if (flag) {
        \\        allocator.free(ptr);
        \\    }
        \\    std.mem.doNotOptimizeAway(ptr.ptr[0..0]);
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = source.ast() catch return;
    var fn_node: ?AstNodeId = null;
    for (tree.nodes.items(.tag), 0..) |tag, i| {
        if (tag == .fn_decl) {
            fn_node = ids.astId(@intCast(i));
            break;
        }
    }
    const fn_idx = fn_node orelse return;

    var builder = CfgBuilder.init(allocator);
    var cfg_opt = builder.buildFromFn(&source, fn_idx) catch return;

    if (cfg_opt) |*cfg| {
        defer cfg.deinit();

        var engine = AnalysisEngine.initWithSource(allocator, cfg, &source);
        defer engine.deinit();
        engine.setUseWidening(true);

        // Convergence control: the loop mutates its own induction variable, so a
        // run that stops here means the loop header stopped being a widening point.
        try engine.run();
        try testing.expect(engine.getGraph().getTrackedWideningPointCount() >= 1);

        var leak_reported = false;
        for (engine.getGraph().nodes.items) |node| {
            for (node.state.getStoreViolations()) |violation| {
                if (violation.kind == .resource_leak) leak_reported = true;
            }
        }
        try testing.expect(leak_reported);
    }
}

/// What each arm of a `catch` left behind for the block a `realloc` was handed.
///
/// Which arm ran is the whole question here. The success arm produced a
/// replacement that took the original over, and a fallback that hands back a
/// block it never allocated still owns the original itself, so the same
/// statement leaves the original held on one path and transferred on the
/// other. A handler that hands the caught error back is the opposite shape
/// again: that path leaves the function the way a failed `try` does, so every
/// `errdefer` in scope runs on it.
const CatchArms = struct {
    /// The fallback returned a block it never allocated, so the original is
    /// still live on that path and belongs to this frame.
    fallback_owns_original: bool,
    /// The success arm produced a replacement, which took the original over.
    success_owns_original: bool,
    /// A handler propagated the caught error, so that path is an error path.
    rethrow_leaves_as_error: bool,
    /// ...and the `errdefer` in scope ran on it, releasing what it owned.
    rethrow_released_original: bool,
};

/// Runs `code` and reports what the block named `binding` was left as on each
/// path that leaves the `tag` node its statement builds.
///
/// A `return`, a declaration's initializer and an assignment's right-hand
/// side all dispatch on the same root and all hand the same question to the
/// arms, so the answer is read off one node's post-states whichever of them
/// built it. Reading it there is also what makes a spelling that decided no
/// arm at all visible: such a spelling is still well formed, it just has one
/// value standing in for both arms instead of one for each.
///
/// The engine here runs without a type context, so a snippet it analyses is
/// read the way an untyped one is: an allocator is recognised by the name its
/// parameter carries, and a parameter called anything else is not an
/// allocator to it at all. A snippet whose allocator is spelled any other way
/// allocates blocks this run never records, and every arm then answers about a
/// block the analysis never saw - which is why the snippets below name it
/// `allocator`.
fn runCatchArms(allocator: std.mem.Allocator, code: [:0]const u8, binding: []const u8, tag: cfg_mod.IrTag) !CatchArms {
    var arms = CatchArms{
        .fallback_owns_original = false,
        .success_owns_original = false,
        .rethrow_leaves_as_error = false,
        .rethrow_released_original = false,
    };

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const token_tags = tree.tokens.items(.tag);

    var fn_node: ?AstNodeId = null;
    var region: ?ids.VarId = null;
    for (tree.nodes.items(.tag), 0..) |node_tag, i| {
        // The declaration is nested under the function it belongs to, so the
        // scan cannot stop at the function node it has to pass on its way.
        if (node_tag == .fn_decl and fn_node == null) fn_node = ids.astId(@intCast(i));
        switch (node_tag) {
            .simple_var_decl,
            .aligned_var_decl,
            .local_var_decl,
            .global_var_decl,
            => {
                const full = tree.fullVarDecl(@enumFromInt(i)) orelse continue;
                const name_token = full.ast.mut_token + 1;
                if (name_token >= token_tags.len or token_tags[name_token] != .identifier) continue;
                if (std.mem.eql(u8, tree.tokenSlice(name_token), binding)) region = ids.varId(name_token);
            },
            else => {},
        }
    }
    const fn_idx = fn_node orelse return error.NoFunctionToAnalyse;
    const owned = region orelse return error.NoBindingToAnalyse;

    var builder = CfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, fn_idx)) orelse return error.NoControlFlowToAnalyse;
    defer cfg.deinit();

    var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    try engine.run();

    for (engine.getGraph().nodes.items) |node| {
        if (node.point.kind != .post) continue;
        const cfg_node = cfg.getNode(node.point.node_index) orelse continue;
        if (cfg_node.ir_node.tag != tag) continue;
        if (tag == .var_decl) {
            const declaration = cfg_node.ir_node.ast_node orelse continue;
            const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse continue;
            if (!std.mem.eql(u8, tree.tokenSlice(full.ast.mut_token + 1), "replacement")) continue;
        }
        if (node.state.isErrorPath()) {
            arms.rethrow_leaves_as_error = true;
            if (node.state.getRegionState(owned)) |state| {
                if (state == .freed) arms.rethrow_released_original = true;
            }
            continue;
        }
        const state = node.state.getRegionState(owned) orelse continue;
        switch (state) {
            .allocated => arms.fallback_owns_original = true,
            .freed => arms.success_owns_original = true,
            else => {},
        }
    }
    return arms;
}

/// Settles one spelling against the answer its shape has to give however it is
/// written, so every spelling below is held to the same thing rather than to
/// whatever it happens to produce on its own.
fn expectCatchArms(
    allocator: std.mem.Allocator,
    code: [:0]const u8,
    tag: cfg_mod.IrTag,
    expected: CatchArms,
) !void {
    const arms = try runCatchArms(allocator, code, "original", tag);
    try std.testing.expectEqual(expected.fallback_owns_original, arms.fallback_owns_original);
    try std.testing.expectEqual(expected.success_owns_original, arms.success_owns_original);
    try std.testing.expectEqual(expected.rethrow_leaves_as_error, arms.rethrow_leaves_as_error);
    try std.testing.expectEqual(expected.rethrow_released_original, arms.rethrow_released_original);
}

/// Both spellings are exercised under an injected allocation failure as well,
/// so the arms above are an answer the split actually reaches rather than one
/// an allocation that ran out halfway through faked.
fn expectCatchArmsUnderAllocationFailure(
    code: [:0]const u8,
    tag: cfg_mod.IrTag,
    expected: CatchArms,
) !void {
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        expectCatchArms,
        .{ code, tag, expected },
    );
}

test "a parenthesised return catch decides the arms the bare spelling decides" {
    // The fallback hands back a block it never allocated, so the original is
    // still live on that path, and the success arm produced a replacement that
    // took the original over. Written bare, then written in parentheses.
    const fallback_bare: [:0]const u8 =
        \\const std = @import("std");
        \\fn fallback(allocator: std.mem.Allocator) ![]u8 {
        \\    const original = try allocator.alloc(u8, 4);
        \\    return allocator.realloc(original, 8) catch &.{};
        \\}
    ;
    const fallback_grouped: [:0]const u8 =
        \\const std = @import("std");
        \\fn fallback(allocator: std.mem.Allocator) ![]u8 {
        \\    const original = try allocator.alloc(u8, 4);
        \\    return (allocator.realloc(original, 8) catch &.{});
        \\}
    ;
    const fallback_arms = CatchArms{
        .fallback_owns_original = true,
        .success_owns_original = true,
        .rethrow_leaves_as_error = false,
        .rethrow_released_original = false,
    };

    // The handler hands the very error the guarded call produced back to the
    // caller, so that path is an error path and the `errdefer` above it
    // releases the original. Only the parentheses around the payload differ.
    const rethrow_bare: [:0]const u8 =
        \\const std = @import("std");
        \\fn rethrown(allocator: std.mem.Allocator) ![]u8 {
        \\    const original = try allocator.alloc(u8, 4);
        \\    errdefer allocator.free(original);
        \\    return allocator.realloc(original, 8) catch |err| return err;
        \\}
    ;
    const rethrow_grouped: [:0]const u8 =
        \\const std = @import("std");
        \\fn rethrown(allocator: std.mem.Allocator) ![]u8 {
        \\    const original = try allocator.alloc(u8, 4);
        \\    errdefer allocator.free(original);
        \\    return allocator.realloc(original, 8) catch |err| return (err);
        \\}
    ;
    const rethrow_arms = CatchArms{
        .fallback_owns_original = false,
        .success_owns_original = true,
        .rethrow_leaves_as_error = true,
        .rethrow_released_original = true,
    };

    try expectCatchArmsUnderAllocationFailure(fallback_bare, .ret, fallback_arms);
    try expectCatchArmsUnderAllocationFailure(fallback_grouped, .ret, fallback_arms);
    try expectCatchArmsUnderAllocationFailure(rethrow_bare, .ret, rethrow_arms);
    try expectCatchArmsUnderAllocationFailure(rethrow_grouped, .ret, rethrow_arms);
}

test "a parenthesised declaration initializer decides the arms the bare spelling decides" {
    // The same fallback, reaching a binding rather than the caller: the arm
    // that failed the growth still owns the original, and the arm that grew it
    // hands that ownership to the replacement.
    const bare: [:0]const u8 =
        \\const std = @import("std");
        \\fn declared(allocator: std.mem.Allocator) !void {
        \\    const original = try allocator.alloc(u8, 4);
        \\    const replacement = allocator.realloc(original, 8) catch &.{};
        \\    allocator.free(replacement);
        \\}
    ;
    const grouped: [:0]const u8 =
        \\const std = @import("std");
        \\fn declared(allocator: std.mem.Allocator) !void {
        \\    const original = try allocator.alloc(u8, 4);
        \\    const replacement = (allocator.realloc(original, 8) catch &.{});
        \\    allocator.free(replacement);
        \\}
    ;
    const arms = CatchArms{
        .fallback_owns_original = true,
        .success_owns_original = true,
        .rethrow_leaves_as_error = false,
        .rethrow_released_original = false,
    };

    try expectCatchArmsUnderAllocationFailure(bare, .var_decl, arms);
    try expectCatchArmsUnderAllocationFailure(grouped, .var_decl, arms);
}

test "a parenthesised assignment decides the arms the bare spelling decides" {
    // The same two arms, arriving through a store instead of a declaration.
    // The store replaces what the binding held, so the arm that grew the block
    // hands the original over there, and the arm that fell back still owns it.
    const bare: [:0]const u8 =
        \\const std = @import("std");
        \\fn assigned(allocator: std.mem.Allocator) !void {
        \\    var replacement: []u8 = &.{};
        \\    const original = try allocator.alloc(u8, 4);
        \\    replacement = allocator.realloc(original, 8) catch &.{};
        \\    allocator.free(replacement);
        \\}
    ;
    const grouped: [:0]const u8 =
        \\const std = @import("std");
        \\fn assigned(allocator: std.mem.Allocator) !void {
        \\    var replacement: []u8 = &.{};
        \\    const original = try allocator.alloc(u8, 4);
        \\    replacement = (allocator.realloc(original, 8) catch &.{});
        \\    allocator.free(replacement);
        \\}
    ;
    const arms = CatchArms{
        .fallback_owns_original = true,
        .success_owns_original = true,
        .rethrow_leaves_as_error = false,
        .rethrow_released_original = false,
    };

    try expectCatchArmsUnderAllocationFailure(bare, .assign, arms);
    try expectCatchArmsUnderAllocationFailure(grouped, .assign, arms);
}

/// What one analysed function left behind at its exit.
///
/// Every number is read off states the exit node was actually reached in, so a
/// snippet whose control flow never got there answers `exit_states = 0` and the
/// expectations below refuse it rather than passing on a run that saw nothing.
/// The leaks are looked up by the region the source bound each name to, so an
/// answer does not depend on the order the statements happen to be written in.
const OverwriteExit = struct {
    /// How many distinct states the function's exit node was reached in.
    exit_states: usize,
    /// How many of those exit states were error paths.
    error_path_exits: usize,
    /// `resource_leak` violations the exit states carry, over every region.
    leaks_at_exit: usize,
    /// ...of those, how many name the region `first` was bound to.
    leaks_of_first_at_exit: usize,
    /// ...how many name the region `second` was bound to, when a second name
    /// was asked about. A payload the container took over can be reported
    /// against either binding, so a snippet naming both is asked about both.
    leaks_of_second_at_exit: usize,
    /// How many of the exit states carry no violation of any kind and are not
    /// error paths. An exit a failed `try` reaches carries nothing whatever it
    /// held - the function never got past the acquisition - so counting it as a
    /// clean exit would let an acquisition that never succeeded vouch for a
    /// release that never ran.
    clean_normal_exit_states: usize,
    /// States entering a store whose right-hand side is a `catch`, split by the
    /// arm that expression ran: which arms the run actually took, rather than
    /// how many times the statement was written down.
    catch_success_arms: usize,
    catch_failure_arms: usize,
    /// Every violation anywhere in the graph, the exit or not. A double free
    /// and a use after free are recorded where they happened and ride along in
    /// the state from there to the exit, so this is what "nothing left behind"
    /// is checked against: an exit that looks tidy is not the whole answer.
    violations_in_graph: usize,
    /// How many distinct states the engine entered a loop body in. A body that
    /// repeats is one it had to walk again carrying something it had not seen,
    /// so this is what says a snippet really took a second pass: a body the
    /// first pass already settled into its own fixed point is answered once,
    /// and an expectation that read only the exit would pass on that run too.
    loop_body_entries: usize,
    /// `use_after_free` violations anywhere in the graph, over every region.
    /// Read of a block a resize consumed, or of a block a release already
    /// handed back, is recorded where it happened rather than at the exit.
    uafs_in_graph: usize,
    /// ...of those, how many name the region `first` was bound to.
    uafs_of_first_in_graph: usize,
    /// ...how many name the region `second` was bound to.
    uafs_of_second_in_graph: usize,
    /// `double_free` violations anywhere in the graph, over every region.
    double_frees_in_graph: usize,
    /// ...of those, how many name the region `first` was bound to.
    double_frees_of_first_in_graph: usize,
    /// ...how many name the region `second` was bound to. A queued release
    /// charged to the wrong binding shows up here rather than as a leak.
    double_frees_of_second_in_graph: usize,
};

/// Analyses the first function `code` declares and reports what it left at its
/// exit, with the regions `first` and `second` are bound to read out of the
/// source itself.
///
/// Nothing here answers "there was nothing to look at": a snippet that does not
/// parse, declares no such function, binds no such name or builds no control
/// flow fails the test instead of passing quietly. The engine runs without a
/// type context, so a snippet is read the way an untyped one is read - its
/// allocator is the parameter named `allocator`, and nothing else is one.
fn runOverwriteExit(
    allocator: std.mem.Allocator,
    code: [:0]const u8,
    first: []const u8,
    second: ?[]const u8,
) !OverwriteExit {
    var exit = OverwriteExit{
        .exit_states = 0,
        .error_path_exits = 0,
        .leaks_at_exit = 0,
        .leaks_of_first_at_exit = 0,
        .leaks_of_second_at_exit = 0,
        .clean_normal_exit_states = 0,
        .catch_success_arms = 0,
        .catch_failure_arms = 0,
        .violations_in_graph = 0,
        .loop_body_entries = 0,
        .uafs_in_graph = 0,
        .uafs_of_first_in_graph = 0,
        .uafs_of_second_in_graph = 0,
        .double_frees_in_graph = 0,
        .double_frees_of_first_in_graph = 0,
        .double_frees_of_second_in_graph = 0,
    };

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    // Parser recovery hands back a tree that walks but answers nothing about
    // what was written, so a snippet that did not parse cleanly fails here
    // instead of quietly analysing the wreckage it recovered.
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    const token_tags = tree.tokens.items(.tag);

    var fn_node: ?AstNodeId = null;
    var first_region: ?ids.VarId = null;
    var second_region: ?ids.VarId = null;
    for (tree.nodes.items(.tag), 0..) |node_tag, i| {
        // The declarations are nested under the function they belong to, so the
        // scan has to pass the function node on its way to them.
        if (node_tag == .fn_decl and fn_node == null) fn_node = ids.astId(@intCast(i));
        switch (node_tag) {
            .simple_var_decl,
            .aligned_var_decl,
            .local_var_decl,
            .global_var_decl,
            => {
                const full = tree.fullVarDecl(@enumFromInt(i)) orelse continue;
                const name_token = full.ast.mut_token + 1;
                if (name_token >= token_tags.len or token_tags[name_token] != .identifier) continue;
                const name = tree.tokenSlice(name_token);
                if (std.mem.eql(u8, name, first)) first_region = ids.varId(name_token);
                if (second) |other| {
                    if (std.mem.eql(u8, name, other)) second_region = ids.varId(name_token);
                }
            },
            else => {},
        }
    }
    const fn_idx = fn_node orelse return error.NoFunctionToAnalyse;
    const first_owned = first_region orelse return error.NoBindingToAnalyse;
    var second_owned: ?ids.VarId = null;
    if (second != null) {
        second_owned = second_region orelse return error.NoBindingToAnalyse;
    }

    var builder = CfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, fn_idx)) orelse return error.NoControlFlowToAnalyse;
    defer cfg.deinit();

    var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    try engine.run();

    for (engine.getGraph().nodes.items) |node| {
        const violations = node.state.getStoreViolations();
        exit.violations_in_graph += violations.len;
        for (violations) |violation| {
            switch (violation.kind) {
                .use_after_free => {
                    exit.uafs_in_graph += 1;
                    if (violation.region == first_owned) exit.uafs_of_first_in_graph += 1;
                    if (second_owned) |other| {
                        if (violation.region == other) exit.uafs_of_second_in_graph += 1;
                    }
                },
                .double_free => {
                    exit.double_frees_in_graph += 1;
                    if (violation.region == first_owned) exit.double_frees_of_first_in_graph += 1;
                    if (second_owned) |other| {
                        if (violation.region == other) exit.double_frees_of_second_in_graph += 1;
                    }
                },
                else => {},
            }
        }

        const cfg_node = cfg.getNode(node.point.node_index) orelse continue;

        // A loop body is entered once per distinct state the header lets
        // through, and states are deduplicated per point, so the count is the
        // number of passes the run actually walked rather than the number of
        // statements the body is written as.
        if (node.point.kind == .pre and cfg_node.ir_node.tag == .loop_body) {
            exit.loop_body_entries += 1;
        }

        // A `catch` on the right of a store splits that store into two arms, and
        // each edge out of the expression records the decision its own arm
        // made, so which arms the run took is read off the states entering the
        // store rather than off the two ways the statement is written.
        if (node.point.kind == .pre and cfg_node.ir_node.tag == .assign) {
            const rhs = cfg_node.ir_node.operand2_node orelse continue;
            const catch_ast = catchOnRightOfStore(tree, rhs) orelse continue;
            if (node.state.getCatchArm(catch_ast)) |arm| {
                switch (arm) {
                    .success => exit.catch_success_arms += 1,
                    .failure => exit.catch_failure_arms += 1,
                }
            }
            continue;
        }

        if (node.point.kind != .post) continue;
        if (cfg_node.ir_node.tag != .fn_exit) continue;

        exit.exit_states += 1;
        const error_path = node.state.isErrorPath();
        if (error_path) exit.error_path_exits += 1;
        if (violations.len == 0 and !error_path) exit.clean_normal_exit_states += 1;

        for (violations) |violation| {
            if (violation.kind != .resource_leak) continue;
            exit.leaks_at_exit += 1;
            if (violation.region == first_owned) exit.leaks_of_first_at_exit += 1;
            if (second_owned) |other| {
                if (violation.region == other) exit.leaks_of_second_at_exit += 1;
            }
        }
    }
    return exit;
}

/// The `catch` expression a store's right-hand side is, read through whatever
/// parentheses are written around it, or null when it is not one at all.
fn catchOnRightOfStore(tree: *const std.zig.Ast, expr: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var current = expr;
    while (current != 0 and current < tags.len) {
        switch (tags[current]) {
            .@"catch" => return current,
            .grouped_expression => current = @intFromEnum(datas[current].node_and_token[0]),
            else => return null,
        }
    }
    return null;
}

/// The snippet has to reach its exit and leave nothing behind anywhere in the
/// graph - no leak, no double free, no use of a block already released.
fn expectNothingLeftBehind(
    allocator: std.mem.Allocator,
    code: [:0]const u8,
    binding: []const u8,
) !void {
    const exit = try runOverwriteExit(allocator, code, binding, null);
    try std.testing.expect(exit.exit_states >= 1);
    try std.testing.expectEqual(@as(usize, 0), exit.violations_in_graph);
}

/// The snippet has to reach its exit and report the block it orphaned there,
/// against the region the source itself bound `binding` to.
fn expectOrphanReportedAtExit(
    allocator: std.mem.Allocator,
    code: [:0]const u8,
    binding: []const u8,
) !void {
    const exit = try runOverwriteExit(allocator, code, binding, null);
    try std.testing.expect(exit.exit_states >= 1);
    try std.testing.expect(exit.leaks_at_exit >= 1);
    try std.testing.expect(exit.leaks_of_first_at_exit >= 1);
}

test "a binding emptied by assignment leaves the block it held an orphan" {
    // The optional is the shape the report came in: the binding is not a plain
    // slice and emptying it hands nothing back, so the acquisition is the only
    // thing that ever names the block. The exit has to report it against the
    // binding that acquired it - reporting it nowhere is the bug, and reporting
    // it against some other region would be a different bug wearing the same
    // test's clothes.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn emptied(allocator: std.mem.Allocator) !void {
        \\    var bytes: ?[]u8 = try allocator.alloc(u8, 4);
        \\    bytes = null;
        \\}
    ;

    try expectOrphanReportedAtExit(std.testing.allocator, code, "bytes");
}

test "a binding overwritten while an alias still names the block leaks nothing" {
    // `saved` is a second name for the same block, so the block is released
    // through it. Reading the overwrite as an orphan would report a leak in the
    // one direction that has none: the alias is exactly what makes the binding
    // losing the block harmless.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn aliased(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    const saved = bytes;
        \\    bytes = &.{};
        \\    allocator.free(saved);
        \\}
    ;

    try expectNothingLeftBehind(std.testing.allocator, code, "bytes");
}

test "a binding assigned its own value has not lost the block" {
    // The right-hand side is the binding itself, so nothing is orphaned: the
    // block stays where it was and the `free` below is the only release of it.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn reassigned(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    bytes = bytes;
        \\    allocator.free(bytes);
        \\}
    ;

    try expectNothingLeftBehind(std.testing.allocator, code, "bytes");
}

test "a discard store into a captured `_` leaves the capture naming the block" {
    // A `|_|` capture binds the name `_` for the arm it belongs to, and the
    // resolver then resolves every identifier spelled `_` in that arm to that
    // one region - so `_ = bytes;` is a store into a name and not a discard.
    //
    // Only the arm the payload was taken on holds the block. An `else` payload
    // names the error the guard carries, which is a value this frame never
    // allocated, so a name bound to it stands for nothing and the orphan on
    // that arm is `bytes`' own to report, whichever way the store is read.
    // The snippet is therefore one path, with `else unreachable` a dead end,
    // so the exit the run reads is the capture's and nothing else answers for
    // it.
    //
    // Reading that store as a discard severs the capture:
    // `Store.replaceRegionForBinding` drops the edge a region was saved under,
    // and a store on the discard path writes none back. `bytes = null` then
    // finds no name still standing for the block and reports it against the
    // binding that acquired it, where the name that took it over is the one
    // that could still say so.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn captured(allocator: std.mem.Allocator) !void {
        \\    var bytes: anyerror![]u8 = try allocator.alloc(u8, 4);
        \\    if (bytes) |_| {
        \\        _ = bytes;
        \\        bytes = null;
        \\    } else unreachable;
        \\}
    ;

    const exit = try runOverwriteExit(std.testing.allocator, code, "bytes", null);

    try std.testing.expect(exit.exit_states >= 1);
    // Nothing releases the block, so it is an orphan either way.
    try std.testing.expect(exit.leaks_at_exit >= 1);
    // What the capture decides is whose orphan it is, and a capture took the
    // block over from the binding that acquired it. A capture is a payload
    // token and not a declaration, so the harness reads no region out of the
    // source for it: the leak is countable only as charged to the binding that
    // did not take the block over, which is why the count above says the block
    // is reported at all and this one says where it must not be.
    try std.testing.expectEqual(@as(usize, 0), exit.leaks_of_first_at_exit);

    // The control that keeps the answer above from being a run that had
    // nothing to report: the same body with no scope binding the name `_`, so
    // the store stands for nothing and leaves no name behind. There the orphan
    // is the binding's, and the binding is the only name the block has.
    const unbound: [:0]const u8 =
        \\const std = @import("std");
        \\fn unbound(allocator: std.mem.Allocator) !void {
        \\    var bytes: anyerror![]u8 = try allocator.alloc(u8, 4);
        \\    _ = bytes;
        \\    bytes = null;
        \\}
    ;

    try expectOrphanReportedAtExit(std.testing.allocator, unbound, "bytes");
}

test "a discard store keeps the alias a `_` declaration stands for" {
    // The same store into the same region, with the name bound by a
    // declaration rather than by a capture. `const _ = bytes;` records the
    // alias the declaration makes, and the store that follows has to leave it
    // standing: it is a second name for the block, and a name the store does
    // not know about is one `replaceRegionForBinding` drops on its way past.
    //
    // The region that declaration bound is read back out of the source by
    // name, so the assertions below say which name the orphan is charged to
    // rather than how many times it is reported.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn aliased(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    const _ = bytes;
        \\    _ = bytes;
        \\    bytes = &.{};
        \\}
    ;

    const exit = try runOverwriteExit(std.testing.allocator, code, "_", "bytes");

    try std.testing.expect(exit.exit_states >= 1);
    try std.testing.expect(exit.leaks_at_exit >= 1);
    // The block is the `_` declaration's orphan: it is the name that was still
    // standing for it when `bytes` gave it up.
    try std.testing.expect(exit.leaks_of_first_at_exit >= 1);
    // The binding that acquired it released nothing and lost it to a name that
    // survived, so charging it there would report an orphan against a binding
    // that held the block only until a saved name took it over.
    try std.testing.expectEqual(@as(usize, 0), exit.leaks_of_second_at_exit);
}

test "an acquisition written straight into `_` is still reported" {
    // The slot an acquisition lands in is a region of its own whether or not a
    // name stands behind it, and the store that hands a block over is settled
    // from what that region is holding - never from the spelling of the name
    // it was written to. So an acquisition written into a discard is a leak
    // like any other, and this is where the fixtures pin it.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn discarded(allocator: std.mem.Allocator) !void {
        \\    var marker: u8 = 0;
        \\    _ = try allocator.alloc(u8, 4);
        \\}
    ;

    const exit = try runOverwriteExit(std.testing.allocator, code, "marker", null);

    try std.testing.expect(exit.exit_states >= 1);
    try std.testing.expect(exit.leaks_at_exit >= 1);
    // Reported against the slot the acquisition was written to, which is no
    // binding of this frame: `marker` is the only name here, and it holds
    // nothing.
    try std.testing.expectEqual(@as(usize, 0), exit.leaks_of_first_at_exit);
}

test "a discard store leaves no name behind where no `_` is bound" {
    // The run above with the `const _ = bytes;` left out, so the only thing
    // the two differ on is whether a scope binds the name `_`. With nothing
    // bound there, the store is the discard `fp_loop_defer_close.zig` pins: it
    // stands for nothing, so the overwrite orphans the block against the
    // binding that acquired it instead of handing it to a name that took it
    // over. Reading it as a store into a name would put a region holding
    // nothing on the ownership graph, and `resetRegion` would hand the block a
    // re-acquired binding is about to take over to that region.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn discarded(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    _ = bytes;
        \\    bytes = &.{};
        \\}
    ;

    try expectOrphanReportedAtExit(std.testing.allocator, code, "bytes");

    // And the same body with the release queued for the binding, which is the
    // fixture itself: a discard that stood in as a saved name would take the
    // block with it on the second pass, and the queue written for the binding
    // would be dropped with the name that carried it.
    const closed: [:0]const u8 =
        \\const std = @import("std");
        \\fn process(dir: std.fs.Dir, names: []const []const u8) !void {
        \\    for (names) |name| {
        \\        const file = try dir.openFile(name, .{});
        \\        defer file.close();
        \\        _ = file;
        \\    }
        \\}
    ;

    try expectNothingLeftBehind(std.testing.allocator, closed, "file");
}

test "a resize whose fallback hands back the original releases it exactly once" {
    // Which arm ran is the whole question. The fallback produced no replacement
    // and handed back the block the resize was handed, so that arm still holds
    // the original - reading it as a transfer would release the original there,
    // and the `free` below would be the second one. The `errdefer` is in scope
    // for the whole of it and never fires, because nothing after it can leave
    // the function in error; it is here so a run that treated this function as
    // an error path would have to say so with a double free.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn grown(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    errdefer allocator.free(bytes);
        \\    bytes = allocator.realloc(bytes, 8) catch bytes;
        \\    allocator.free(bytes);
        \\}
    ;

    try expectNothingLeftBehind(std.testing.allocator, code, "bytes");
}

test "a deferred release over an overwritten variable frees the replacement, not the block it held" {
    // `defer` reads its expression when the scope ends, not when the statement
    // runs, so a `defer` naming the binding releases whatever the binding holds
    // by then. The block the acquisition named is gone from under it and
    // nothing releases that one, on either path out of the function.
    const deferred_overwritten: [:0]const u8 =
        \\const std = @import("std");
        \\fn deferred_overwritten(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    defer allocator.free(bytes);
        \\    bytes = &.{};
        \\}
    ;

    // The same reading of the same variable, spelled `errdefer`. The error arm
    // is where an `errdefer` runs at all, so the snippet carries both paths:
    // the release fires on one and the explicit `free` fires on the other, and
    // the block neither of them reaches is orphaned on both.
    const errdeferred_overwritten: [:0]const u8 =
        \\const std = @import("std");
        \\fn errdeferred_overwritten(allocator: std.mem.Allocator, fail: bool) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    errdefer allocator.free(bytes);
        \\    bytes = &.{};
        \\    if (fail) return error.Bad;
        \\    allocator.free(bytes);
        \\}
    ;

    // Capturing the block in a name of its own is what makes the same `defer`
    // release the block: `saved` still names it when the scope ends, so the
    // overwrite never orphaned anything.
    const deferred_captured: [:0]const u8 =
        \\const std = @import("std");
        \\fn deferred_captured(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    const saved = bytes;
        \\    defer allocator.free(saved);
        \\    bytes = &.{};
        \\}
    ;
    const errdeferred_captured: [:0]const u8 =
        \\const std = @import("std");
        \\fn errdeferred_captured(allocator: std.mem.Allocator, fail: bool) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    const saved = bytes;
        \\    errdefer allocator.free(saved);
        \\    bytes = &.{};
        \\    if (fail) return error.Bad;
        \\    allocator.free(saved);
        \\}
    ;

    const testing = std.testing;
    const allocator = testing.allocator;

    try expectOrphanReportedAtExit(allocator, deferred_overwritten, "bytes");
    try expectOrphanReportedAtExit(allocator, errdeferred_overwritten, "bytes");
    try expectNothingLeftBehind(allocator, deferred_captured, "bytes");
    try expectNothingLeftBehind(allocator, errdeferred_captured, "bytes");

    // The error arm has to be one of the states that reached the exit, or the
    // two `errdefer` runs above never saw the path where the release fires at
    // all and would pass on the normal path alone.
    const overwritten = try runOverwriteExit(allocator, errdeferred_overwritten, "bytes", null);
    try testing.expect(overwritten.exit_states >= 2);
    try testing.expect(overwritten.error_path_exits >= 1);
    const captured = try runOverwriteExit(allocator, errdeferred_captured, "bytes", null);
    try testing.expect(captured.exit_states >= 2);
    try testing.expect(captured.error_path_exits >= 1);
}

test "a deferred release in a loop body discharges the acquisition of that same pass" {
    // The body opens a block, defers its release and then reads it, and the
    // body leaves that scope at the end of every pass, so each pass discharges
    // the block it opened itself. The `_ = bytes;` is the part that has to
    // survive the second pass: a discard is not a name, so it must not be
    // recorded as a saved alias. `Store.resetRegion` hands the resource a
    // re-declared binding is about to re-acquire to whichever saved name still
    // stands for it, and the schedule written for `bytes` is not one of those
    // names to carry - so with a discard standing in, the still-held block
    // moved to the discard, the release queued for `bytes` was dropped with it,
    // and the `_ = bytes;` store then reported an orphan against itself: a leak
    // for a block the same pass releases.
    const released: [:0]const u8 =
        \\const std = @import("std");
        \\fn released(allocator: std.mem.Allocator, inputs: []const []const u8) !void {
        \\    for (inputs) |input| {
        \\        const bytes = try allocator.dupe(u8, input);
        \\        defer allocator.free(bytes);
        \\        _ = bytes;
        \\    }
        \\}
    ;

    // The same body with the release left out. The block is still reported, and
    // it is reported on the pass the engine walked, so the loop has to have
    // been entered more than once for the run above to mean anything.
    const unclosed: [:0]const u8 =
        \\const std = @import("std");
        \\fn unclosed(allocator: std.mem.Allocator, inputs: []const []const u8) !void {
        \\    for (inputs) |input| {
        \\        const bytes = try allocator.dupe(u8, input);
        \\        _ = bytes;
        \\    }
        \\}
    ;

    // The release is queued, but for the handle this body opens afterwards. A
    // schedule written for a different binding settles nothing about this one,
    // so the earlier block is still an orphan at the exit and the later one is
    // not: the pairing has to hold between the two bindings, not just between
    // two passes of one binding.
    const closes_the_later_handle: [:0]const u8 =
        \\const std = @import("std");
        \\fn closes_the_later_handle(allocator: std.mem.Allocator, inputs: []const []const u8) !void {
        \\    for (inputs) |input| {
        \\        const bytes = try allocator.dupe(u8, input);
        \\        _ = bytes;
        \\        const other = try allocator.dupe(u8, input);
        \\        defer allocator.free(other);
        \\    }
        \\}
    ;

    const testing = std.testing;
    const allocator = testing.allocator;

    try expectNothingLeftBehind(allocator, released, "bytes");

    const released_exit = try runOverwriteExit(allocator, released, "bytes", null);
    // The body was walked again with a state the first pass never carried.
    try testing.expect(released_exit.loop_body_entries >= 2);

    try expectOrphanReportedAtExit(allocator, unclosed, "bytes");
    const unclosed_exit = try runOverwriteExit(allocator, unclosed, "bytes", null);
    try testing.expect(unclosed_exit.loop_body_entries >= 2);

    try expectOrphanReportedAtExit(allocator, closes_the_later_handle, "bytes");
    const closes_later = try runOverwriteExit(allocator, closes_the_later_handle, "bytes", "other");
    try testing.expectEqual(@as(usize, 0), closes_later.leaks_of_second_at_exit);
}

test "a second pass through a loop body pairs each acquisition with its own release" {
    // The counter is what makes this a second pass rather than a repeat of the
    // first: each pass reaches the header carrying a different value, so the
    // engine walks the body again with a state the first pass never produced
    // instead of deduplicating it against that one. This is the pass where a
    // release queued for the previous pass's block would be charged to the
    // block this pass acquired, and where a block this pass acquired would be
    // orphaned if its own release were taken out with the previous pass's.
    //
    // The counter is `u31`: the guard constraint domain reads comparisons
    // over signed and narrow unsigned integers, so `pass < 2` prunes the
    // third pass and the run after the second one leaves through the exit.
    // A `usize` counter names no constraint there today, so the same loop
    // written with one never runs out of passes for the widening to join.
    const released: [:0]const u8 =
        \\const std = @import("std");
        \\fn released(allocator: std.mem.Allocator, input: []const u8) !void {
        \\    var pass: u31 = 0;
        \\    while (pass < 2) : (pass += 1) {
        \\        const bytes = try allocator.dupe(u8, input);
        \\        defer allocator.free(bytes);
        \\        _ = bytes;
        \\    }
        \\}
    ;

    // The same two passes with the release left out, so the quiet run above is
    // the release discharging the block and not a body that never opened one.
    const unclosed: [:0]const u8 =
        \\const std = @import("std");
        \\fn unclosed(allocator: std.mem.Allocator, input: []const u8) !void {
        \\    var pass: u31 = 0;
        \\    while (pass < 2) : (pass += 1) {
        \\        const bytes = try allocator.dupe(u8, input);
        \\        _ = bytes;
        \\    }
        \\}
    ;

    const testing = std.testing;
    const allocator = testing.allocator;

    const released_exit = try runOverwriteExit(allocator, released, "bytes", null);
    try testing.expect(released_exit.exit_states >= 1);
    try testing.expectEqual(@as(usize, 0), released_exit.violations_in_graph);
    try testing.expect(released_exit.loop_body_entries >= 2);

    const unclosed_exit = try runOverwriteExit(allocator, unclosed, "bytes", null);
    try expectOrphanReportedAtExit(allocator, unclosed, "bytes");
    try testing.expect(unclosed_exit.loop_body_entries >= 2);
}

test "a payload handed to the container that took it over is released with it" {
    // The store into the aggregate ran, so the block belongs to `out` by the
    // time the binding is overwritten, and the overwrite orphans nothing. The
    // return hands `out` - and through it the payload - to the caller.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\
        \\const Block = struct {
        \\    payload: []u8,
        \\};
        \\
        \\fn handed_over(allocator: std.mem.Allocator) !*Block {
        \\    const out = try allocator.create(Block);
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    out.* = .{ .payload = bytes };
        \\    bytes = &.{};
        \\    return out;
        \\}
    ;

    try expectNothingLeftBehind(std.testing.allocator, code, "bytes");
}

test "destroying the container leaves the payload it took over an orphan" {
    // The same stores as the handed-over snippet, with a release that names the
    // container and not the payload it holds. This is the contrast that says
    // the run above is quiet because the payload was handed on, not because the
    // overwrite is never charged.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\
        \\const Block = struct {
        \\    payload: []u8,
        \\};
        \\
        \\fn dropped(allocator: std.mem.Allocator) !void {
        \\    const out = try allocator.create(Block);
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    out.* = .{ .payload = bytes };
        \\    bytes = &.{};
        \\    allocator.destroy(out);
        \\}
    ;

    // The payload is reported against the region that acquired it. The
    // container cannot stand in for it: `destroy` released that one, so a run
    // blaming the container would be reporting a block this frame had already
    // given back, and the real orphan would go unmentioned.
    const testing = std.testing;
    const exit = try runOverwriteExit(testing.allocator, code, "bytes", "out");
    try testing.expect(exit.exit_states >= 1);
    try testing.expect(exit.leaks_at_exit >= 1);
    try testing.expect(exit.leaks_of_first_at_exit >= 1);
    try testing.expectEqual(@as(usize, 0), exit.leaks_of_second_at_exit);
}

test "a resize that fell back leaves the block it was handed an orphan" {
    // The right-hand side is a resize of the very binding it writes, and its two
    // arms leave that binding in different states of ownership. The arm that
    // grew the block took the original over; the arm that fell back wrote a
    // block this frame never allocated and left the original with nobody
    // holding it. Reading the right-hand side as a resize of its own whichever
    // arm ran hands the original over on a path where no resize happened, and
    // the orphan on that path goes unmentioned.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn resized(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    bytes = allocator.realloc(bytes, 8) catch &.{};
        \\    allocator.free(bytes);
        \\}
    ;

    const testing = std.testing;
    const exit = try runOverwriteExit(testing.allocator, code, "bytes", null);

    // Both arms ran. What is counted here is the states entering the store,
    // each carrying the decision its own arm's edge left with, so this says
    // what the run did rather than what the statement could be read as.
    try testing.expect(exit.catch_success_arms >= 1);
    try testing.expect(exit.catch_failure_arms >= 1);

    // One completed normal path released everything - the arm that grew the
    // block - and one completed path reported the orphan against the region
    // that acquired it, which is the arm that fell back. A run that charged the
    // original on both arms would leave no clean normal path to show here, and
    // a run that charged it on neither would leave nothing to report. The exit
    // a failed allocation reaches is an error path carrying nothing, so it is
    // not counted as the clean one: only a path that allocated can say that the
    // grown block was released.
    try testing.expect(exit.exit_states >= 2);
    try testing.expect(exit.clean_normal_exit_states >= 1);
    try testing.expect(exit.leaks_of_first_at_exit >= 1);
}

test "a resize of a name another binding still holds releases the block through that binding" {
    // The store names the same region on both sides, which is the write that
    // promotes the alias outliving it over the name being replaced. So the
    // block the successful arm freed is left under `saved`, and `saved` is
    // the only name that can say it is gone. Charging the replaced binding
    // instead - which is what reading the call after the store names - marks
    // the growth freed and leaves the original alive under the name that took
    // it over, where nothing is left to report it.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn aliased(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    const saved = bytes;
        \\    bytes = allocator.realloc(bytes, 8) catch bytes;
        \\    allocator.free(bytes);
        \\}
    ;

    const testing = std.testing;
    const exit = try runOverwriteExit(testing.allocator, code, "bytes", "saved");

    // Both arms ran. What is counted is the states entering the store, each
    // carrying the decision its own arm's edge left with, so this says what the
    // run did rather than what the statement could be read as.
    try testing.expect(exit.catch_success_arms >= 1);
    try testing.expect(exit.catch_failure_arms >= 1);

    // And a normal path got all the way out. An exit a failed allocation
    // reaches is an error path carrying nothing whatever it held, so counting
    // it as a clean one would let an acquisition that never succeeded vouch
    // for the releases that did.
    try testing.expect(exit.clean_normal_exit_states >= 1);

    // The arm that grew the block released the original through the resize and
    // the growth through the `free`; the arm that fell back still held the
    // original under both names and released it once. Nothing is orphaned on
    // either, and nothing is released twice.
    try testing.expectEqual(@as(usize, 0), exit.violations_in_graph);
    try testing.expectEqual(@as(usize, 0), exit.leaks_at_exit);
    try testing.expectEqual(@as(usize, 0), exit.leaks_of_second_at_exit);
}

test "a resize written through an alias releases the block the alias was made from" {
    // The same store with the two sides the other way round: the binding
    // written is `saved`, which is an alias, and the block is reached through
    // the name `bytes` that made it. Reading the source off the call after the
    // store names the binding that was replaced - the one the growth now
    // belongs to - so the original is left alive under `bytes` and the `free`
    // below releases a block nobody handed back.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn renamed(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    var saved = bytes;
        \\    saved = allocator.realloc(saved, 8) catch saved;
        \\    allocator.free(saved);
        \\}
    ;

    const testing = std.testing;
    const exit = try runOverwriteExit(testing.allocator, code, "bytes", "saved");

    try testing.expect(exit.catch_success_arms >= 1);
    try testing.expect(exit.catch_failure_arms >= 1);
    try testing.expect(exit.clean_normal_exit_states >= 1);

    // The original is named after the binding the acquisition wrote it to,
    // and it is gone: reported against `saved` instead, that would be the
    // growth the resize produced, which the `free` below does release.
    try testing.expectEqual(@as(usize, 0), exit.violations_in_graph);
    try testing.expectEqual(@as(usize, 0), exit.leaks_at_exit);
    try testing.expectEqual(@as(usize, 0), exit.leaks_of_first_at_exit);
}

test "an alias read after a resize that took its block over is a read of a released block" {
    // The alias outlives the resize and still names a block, so reading it
    // looks like reading something this frame holds. On the arm where the
    // resize ran, that block is the one the resize released. The same read on
    // the arm where the resize fell back is a read of a live block, which is
    // what makes the release below a single release on that arm rather than a
    // second one.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn used_after(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    const saved = bytes;
        \\    bytes = allocator.realloc(bytes, 8) catch bytes;
        \\    const tail = saved.len;
        \\    allocator.free(bytes);
        \\}
    ;

    const testing = std.testing;
    const exit = try runOverwriteExit(testing.allocator, code, "bytes", "saved");

    try testing.expect(exit.catch_success_arms >= 1);
    try testing.expect(exit.catch_failure_arms >= 1);
    try testing.expect(exit.clean_normal_exit_states >= 1);

    // Named after the alias, which is the region the released block was
    // promoted to and the only name still standing for it.
    try testing.expect(exit.uafs_of_second_in_graph >= 1);

    // The arm where the resize fell back kept the original for the `free` to
    // release. Had that arm read the call as a resize that ran, the same
    // `free` would be the second release of a block already handed back.
    try testing.expectEqual(@as(usize, 0), exit.double_frees_in_graph);

    // Nothing is orphaned either way: the successful arm released the original
    // through the resize and the growth through the `free`, and the fallback
    // arm released the one block it still held.
    try testing.expectEqual(@as(usize, 0), exit.leaks_at_exit);
}

test "a release queued for the binding a resize writes still reads that binding" {
    // A `defer` names the binding, and its body runs when the scope ends, so
    // the release it queues is charged to whatever that binding holds then.
    // The resize changed what it holds, so the queued release is what hands
    // back the growth; the original was handed over by the resize itself and
    // must not be credited to the queue as well.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn deferred(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    defer allocator.free(bytes);
        \\    bytes = allocator.realloc(bytes, 8) catch bytes;
        \\}
    ;

    try expectNothingLeftBehind(std.testing.allocator, code, "bytes");
}

test "a release queued for a saved alias is charged to the block that alias named" {
    // The queued release names `saved`, which stops being the binding the
    // resize wrote and stays the name the released block was promoted to. The
    // resize already handed that block back, so the queue running over it is a
    // second release - reported against the old block, where it happened.
    // Lending the queue the growth instead would turn the `free` below into a
    // second release of the grown block and leave the real one unmentioned.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn deferred_alias(allocator: std.mem.Allocator) !void {
        \\    var bytes = try allocator.alloc(u8, 4);
        \\    const saved = bytes;
        \\    defer allocator.free(saved);
        \\    bytes = allocator.realloc(bytes, 8) catch &.{};
        \\    allocator.free(bytes);
        \\}
    ;

    const testing = std.testing;
    const exit = try runOverwriteExit(testing.allocator, code, "bytes", "saved");

    // Both arms ran, which is already proof the function got past its
    // allocation: the resize's success edge cannot be taken otherwise. No
    // clean normal exit is claimed here - the fallback wrote a block this
    // frame never allocated and the `free` below releases it, which is its
    // own finding and says nothing about who owns the resized block.
    try testing.expect(exit.catch_success_arms >= 1);
    try testing.expect(exit.catch_failure_arms >= 1);

    // Named after the alias and never after the binding that took the growth.
    try testing.expect(exit.double_frees_of_second_in_graph >= 1);
    try testing.expectEqual(@as(usize, 0), exit.double_frees_of_first_in_graph);

    // The fallback arm kept the original under `saved` and the queue released
    // it; the successful arm released it through the resize and the growth
    // through the `free`. Neither leaves anything behind.
    try testing.expectEqual(@as(usize, 0), exit.leaks_at_exit);
}

test "a once-around loop continuation hands its payload to the block it returns" {
    // The store in a `while` continuation is lowered as a plain expression, so
    // the payload moves only on a pass that actually runs. `while (i < 1)` over
    // a `usize` counter is a guard the constraint domain cannot phrase - its
    // ranges are defined over signed integers and unsigned ones narrower than
    // a machine word - so the header named no constraint and walked its way out
    // beside the one pass the guard admits. On that pass the continuation never
    // ran, so the payload stayed behind in a frame whose block was already
    // leaving through the return: a leak read off a loop that provably ran.
    //
    // What settles the way out here is the environment, which is stated in a
    // wider domain and does hold the counter: `applyIdentifierStore` and
    // `compoundValue` keep an exact number for one this loop is stepping, and
    // `0 < 1` is decided from it alone.
    const once_around: [:0]const u8 =
        \\const std = @import("std");
        \\
        \\const Block = struct {
        \\    payload: []u8,
        \\};
        \\
        \\fn once_around(allocator: std.mem.Allocator) !*Block {
        \\    const out = try allocator.create(Block);
        \\    const bytes = try allocator.dupe(u8, "abc");
        \\    var i: usize = 0;
        \\    while (i < 1) : (out.* = .{ .payload = bytes }) {
        \\        i += 1;
        \\    }
        \\    return out;
        \\}
    ;

    const testing = std.testing;
    const run = try runOverwriteExit(testing.allocator, once_around, "bytes", null);
    // The body really was entered, so this is a store that moved the payload
    // and not a loop the run skipped: a quiet answer from a body never reached
    // would say nothing about the ownership edge the store records.
    try testing.expect(run.loop_body_entries >= 1);
    try testing.expect(run.exit_states >= 1);
    try testing.expectEqual(@as(usize, 0), run.violations_in_graph);

    // The same loop over the spelling of the counter the domain already reads.
    // Nothing else about the two runs differs - same store, same step, same
    // guard, same returned block - so a run that still separates them is
    // separating the width of the counter rather than anything the loop does.
    const narrow_counter: [:0]const u8 =
        \\const std = @import("std");
        \\
        \\const Block = struct {
        \\    payload: []u8,
        \\};
        \\
        \\fn narrow_counter(allocator: std.mem.Allocator) !*Block {
        \\    const out = try allocator.create(Block);
        \\    const bytes = try allocator.dupe(u8, "abc");
        \\    var i: u32 = 0;
        \\    while (i < 1) : (out.* = .{ .payload = bytes }) {
        \\        i += 1;
        \\    }
        \\    return out;
        \\}
    ;

    const narrow = try runOverwriteExit(testing.allocator, narrow_counter, "bytes", null);
    try testing.expect(narrow.loop_body_entries >= 1);
    try testing.expectEqual(@as(usize, 0), narrow.violations_in_graph);

    // The control the first run has to be told apart from: a counter the guard
    // already rules out admits no pass at all, so the continuation store is
    // never reached and the payload has nobody to move it into the block this
    // function returns. Reading the guard off the environment must not answer
    // for a loop that does not run - the orphan is real here, and it is
    // reported against the region that acquired it.
    const never_runs: [:0]const u8 =
        \\const std = @import("std");
        \\
        \\const Block = struct {
        \\    payload: []u8,
        \\};
        \\
        \\fn never_runs(allocator: std.mem.Allocator) !*Block {
        \\    const out = try allocator.create(Block);
        \\    out.* = .{ .payload = &.{} };
        \\    const bytes = try allocator.dupe(u8, "abc");
        \\    var i: usize = 1;
        \\    while (i < 1) : (out.* = .{ .payload = bytes }) {
        \\        i += 1;
        \\    }
        \\    return out;
        \\}
    ;

    const skipped = try runOverwriteExit(testing.allocator, never_runs, "bytes", "out");
    try testing.expect(skipped.exit_states >= 1);
    try testing.expect(skipped.leaks_of_first_at_exit >= 1);
    // The container is not what leaks: it escapes through the return, and it is
    // the payload it never received that is left standing.
    try testing.expectEqual(@as(usize, 0), skipped.leaks_of_second_at_exit);
}
