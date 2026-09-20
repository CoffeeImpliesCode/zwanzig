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
const SummaryCache = @import("../summary.zig").SummaryCache;
const ProgramPoint = @import("../state.zig").ProgramPoint;
const ProgramState = @import("../state.zig").ProgramState;
const ErrorState = @import("../state.zig").ErrorState;
const WideningKey = @import("../state.zig").WideningKey;
const ResourceState = @import("../store.zig").ResourceState;
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
    /// Owned predecessor counts, saturated at two, for immutable root and inline CFGs.
    /// CFG pointers remain valid until engine teardown.
    predecessor_counts: std.AutoHashMap(*const Cfg, []const u8),
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
    /// Type context for type-aware analysis (optional, not owned).
    type_context: ?*TypeContext,
    /// Config for resource models (optional, not owned).
    config: ?*const Config,
    /// Whether widening is enabled.
    use_widening: bool,
    /// Cached CFG artifacts for this source (optional, not owned).
    cached_artifacts: ?*CachedArtifacts,
    /// Cached parent map for AST scope checks.
    parent_map: ?[]u32,
    /// Scratch buffer for FQN construction
    fqn_buffer: [256]u8 = undefined,

    pub const ResourceCalls = @import("resource_calls.zig").Mixin(@This());
    pub const Literals = @import("literals.zig").Mixin(@This());
    pub const VarResolution = @import("var_resolution.zig").Mixin(@This());
    pub const Ownership = @import("ownership.zig").Mixin(@This());
    pub const Payloads = @import("payloads.zig").Mixin(@This());
    pub const DeferScan = @import("defer_scan.zig").Mixin(@This());
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
            .predecessor_counts = std.AutoHashMap(*const Cfg, []const u8).init(allocator),
            .function_names = std.StringHashMap(AstNodeId).init(allocator),
            .var_resolvers = std.AutoHashMap(AstNodeId, *VarResolver).init(allocator),
            .assertion_scopes = std.AutoHashMap(AstNodeId, assertions.AssertionScope).init(allocator),
            .inlined_call_count = 0,
            .summary_cache = SummaryCache.init(allocator),
            .use_summaries = true,
            .summary_use_count = 0,
            .build_metadata = null,
            .checker_name = null,
            .type_context = null,
            .config = null,
            .use_widening = false,
            .cached_artifacts = null,
            .parent_map = null,
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
        var counts_iter = self.predecessor_counts.valueIterator();
        while (counts_iter.next()) |counts| {
            self.allocator.free(counts.*);
        }
        self.predecessor_counts.deinit();
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
        if (self.parent_map) |map| {
            self.allocator.free(map);
        }
        self.summary_cache.deinit();
    }

    pub fn getParentMap(self: *AnalysisEngine, tree: *const std.zig.Ast) ![]const u32 {
        if (self.parent_map) |map| return map;

        const tags = tree.nodes.items(.tag);
        const parent_map = try self.allocator.alloc(u32, tags.len);
        @memset(parent_map, 0);
        for (0..tags.len) |i| {
            switch (tags[i]) {
                .fn_decl,
                .test_decl,
                .simple_var_decl,
                .local_var_decl,
                .global_var_decl,
                .aligned_var_decl,
                => ast_walk.fillParentMap(tree, @intCast(i), parent_map),
                else => {},
            }
        }
        self.parent_map = parent_map;
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
                            Ownership.trackEscapesFromCall(self, &state_copy, ast_node, current_cfg);
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

                // Check if this is a branch node - if so, we need to extract constraints
                var branch_constraint_buf: [4]?Constraint = .{ null, null, null, null };
                const branch_constraint_count: usize = if (cfg_node) |node| blk: {
                    if (node.ir_node.tag == .branch) {
                        break :blk BranchConstraints.extractBranchConstraints(self, node, current_cfg, &branch_constraint_buf);
                    }
                    break :blk 0;
                } else 0;

                const predecessor_counts: []const u8 = if (self.use_widening)
                    try self.getPredecessorCounts(current_cfg)
                else
                    &.{};
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
                            },
                            .catch_success => {
                                // Exiting catch block - return to normal
                                succ_state.setErrorState(.normal);
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
                                    const constraint_to_apply = if (edge.kind == .branch_true)
                                        bc
                                    else if (edge.kind == .branch_false)
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

                        // Determine if widening should be applied at this point.
                        // Widening triggers on loop-back edges into loop headers and on other join points
                        // when widening is enabled.
                        const widening_options = blk: {
                            if (self.use_widening) {
                                const is_loop_header = blk_loop: {
                                    if (edge.kind != .loop_back) break :blk_loop false;
                                    if (current_cfg.getNode(edge.to)) |succ_cfg_node| {
                                        break :blk_loop succ_cfg_node.ir_node.tag == .loop_header;
                                    }
                                    break :blk_loop false;
                                };
                                const successor = ids.cfgIndex(edge.to);
                                const is_join = successor < predecessor_counts.len and predecessor_counts[successor] > 1;

                                if (is_loop_header or is_join) {
                                    // succ_point is already a pre-state (from ProgramPoint.initPre above)
                                    const widening_key = WideningKey.init(succ_point, &succ_state);
                                    break :blk ExplodedGraph.WideningOptions{
                                        .apply_widening = true,
                                        .widening_key = widening_key,
                                    };
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

    fn getPredecessorCounts(self: *AnalysisEngine, cfg: *const Cfg) std.mem.Allocator.Error![]const u8 {
        if (self.predecessor_counts.get(cfg)) |counts| return counts;

        const counts = try self.allocator.alloc(u8, cfg.nodeCount());
        errdefer self.allocator.free(counts);
        @memset(counts, 0);
        for (cfg.edges.items) |edge| {
            const target = ids.cfgIndex(edge.to);
            if (target < counts.len and counts[target] < 2) {
                counts[target] += 1;
            }
        }
        try self.predecessor_counts.put(cfg, counts);
        return counts;
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
                        if (ResourceCalls.resolveResourceCall(self, init_node)) |call_info| {
                            switch (call_info.kind) {
                                .alloc => try new_state.trackAllocation(var_id),
                                .open => try new_state.trackOpen(var_id),
                                else => {},
                            }
                        } else if (VarResolution.resolveVarIdFromExpr(self, init_node, current_cfg)) |alias_target| {
                            if (alias_target != var_id) {
                                try new_state.trackAlias(var_id, alias_target);
                            }
                        } else if (ResourceCalls.isDefinitelyNonAlloc(self, init_node)) {
                            try new_state.trackNonAllocation(var_id);
                        }
                        try Ownership.recordOwnershipFromExpr(self, &new_state, init_node, var_id, current_cfg);
                        try Ownership.checkUseAfterFreeInExpr(self, &new_state, init_node, current_cfg);
                    }
                }
            },
            .assign => {
                // For assignments, use the LHS identifier node as the key
                // operand_node contains the LHS, operand2_node contains the RHS
                if (ir_node.operand_node) |lhs_node| {
                    var lhs_is_identifier = false;
                    if (self.source) |src| {
                        if (src.ast() catch null) |tree| {
                            const tags = tree.nodes.items(.tag);
                            lhs_is_identifier = lhs_node < tags.len and tags[lhs_node] == .identifier;
                        }
                    }

                    if (lhs_is_identifier) {
                        const var_id = VarResolution.resolveVarIdFromIdentifier(self, lhs_node, current_cfg) orelse ids.varId(lhs_node);
                        new_state.resetRegion(var_id);
                        // Try to evaluate literal value from RHS, fall back to unknown
                        const rhs_value = if (ir_node.operand2_node) |rhs|
                            Literals.evaluateLiteral(self, rhs)
                        else
                            null;
                        try new_state.setVar(var_id, rhs_value orelse .unknown);
                        if (ir_node.operand2_node) |rhs_node| {
                            if (ResourceCalls.resolveResourceCall(self, rhs_node)) |call_info| {
                                switch (call_info.kind) {
                                    .alloc => try new_state.trackAllocation(var_id),
                                    .open => try new_state.trackOpen(var_id),
                                    else => {},
                                }
                            } else if (VarResolution.resolveVarIdFromExpr(self, rhs_node, current_cfg)) |alias_target| {
                                if (alias_target != var_id) {
                                    try new_state.trackAlias(var_id, alias_target);
                                }
                            } else if (ResourceCalls.isDefinitelyNonAlloc(self, rhs_node)) {
                                try new_state.trackNonAllocation(var_id);
                            }
                            try Ownership.recordOwnershipFromExpr(self, &new_state, rhs_node, var_id, current_cfg);
                            try Ownership.checkUseAfterFreeInExpr(self, &new_state, rhs_node, current_cfg);
                        }
                    } else if (ir_node.operand2_node) |rhs_node| {
                        try Ownership.checkUseAfterFreeInExpr(self, &new_state, rhs_node, current_cfg);
                        try Ownership.markEscapedInExpr(self, &new_state, rhs_node, current_cfg);
                        try Ownership.recordOwnershipFromFieldAssign(self, &new_state, lhs_node, rhs_node, current_cfg);
                        if (ResourceCalls.resolveResourceCall(self, rhs_node)) |call_info| {
                            switch (call_info.kind) {
                                .alloc, .open => {
                                    if (self.source) |src| {
                                        if (src.ast() catch null) |tree| {
                                            const tags = tree.nodes.items(.tag);
                                            const datas = tree.nodes.items(.data);
                                            if (lhs_node < tags.len and tags[lhs_node] == .field_access) {
                                                if (VarResolution.resolveVarIdFromExpr(self, lhs_node, current_cfg)) |field_var| {
                                                    switch (call_info.kind) {
                                                        .alloc => try new_state.trackAllocation(field_var),
                                                        .open => try new_state.trackOpen(field_var),
                                                        else => {},
                                                    }
                                                    const field_access_data = datas[lhs_node].node_and_token;
                                                    const base_node = @intFromEnum(field_access_data[0]);
                                                    if (VarResolution.resolveVarIdFromExpr(self, base_node, current_cfg)) |container_var| {
                                                        try new_state.trackOwnership(field_var, container_var);
                                                        try Ownership.escapeOwnedFromFieldBase(self, &new_state, tree, base_node, container_var, field_var);
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
                            else => {},
                        }
                        if (call_info.kind != .free and call_info.kind != .free_owned and call_info.kind != .close) {
                            try Ownership.checkUseAfterFreeInCall(self, &new_state, ast_node, current_cfg);
                        }
                    } else {
                        try Ownership.checkUseAfterFreeInCall(self, &new_state, ast_node, current_cfg);
                    }
                    Ownership.trackEscapesFromCall(self, &new_state, ast_node, current_cfg);
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

                                    if (VarResolution.resolveVarIdFromExpr(self, ret_expr_idx, current_cfg)) |var_id| {
                                        try new_state.trackEscapeOwned(var_id);
                                        new_state.trackEscape(var_id);
                                    }
                                    try Ownership.markEscapedInExpr(self, &new_state, ret_expr_idx, current_cfg);
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
                    Ownership.trackEscapesInExpr(self, &new_state, ast_node, current_cfg);

                    // Check for assertion calls wrapped in try (try testing.expect(...))
                    if (try BranchConstraints.extractTryAssertionConstraint(self, ast_node, current_cfg)) |constraint| {
                        try new_state.addConstraint(constraint);
                    }
                }
            },
            .expr => {
                if (ir_node.ast_node) |ast_node| {
                    try Ownership.checkUseAfterFreeInExpr(self, &new_state, ast_node, current_cfg);
                    Ownership.trackEscapesInExpr(self, &new_state, ast_node, current_cfg);
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

    const DeclErrorUnionInfo = struct {
        status: ?bool,
        init_node: ?u32,
    };

    fn isDefinitelyErrorExpr(tree: *const std.zig.Ast, expr_node: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (expr_node >= tags.len) return false;

        switch (tags[expr_node]) {
            .error_value => return true,
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
    try testTraversalAllocationFailure(relocating.allocator(), true);
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testTraversalAllocationFailure, .{false});
}

fn testTraversalAllocationFailure(allocator: std.mem.Allocator, expect_relocation: bool) !void {
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
    const nodes_address = @intFromPtr(engine.graph.nodes.items.ptr);
    try engine.run();
    if (expect_relocation) {
        try std.testing.expect(nodes_address != @intFromPtr(engine.graph.nodes.items.ptr));
    }

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

test "AnalysisEngine predecessor cache owns root and inline CFG counts on allocation failure" {
    var source = Source.init(std.testing.allocator, "cache-oom.zig", "fn callee() void {}");
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .fn_decl) break ids.astId(@intCast(index));
    } else return error.TestUnexpectedResult;
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testPredecessorCacheAllocationFailure, .{ &source, fn_node });
}

fn testPredecessorCacheAllocationFailure(allocator: std.mem.Allocator, source: *Source, fn_node: AstNodeId) !void {
    var cfg = Cfg.init(std.testing.allocator);
    defer cfg.deinit();
    const entry = try cfg.addNode(cfg_mod.IrNode.init(.fn_entry));
    const other = try cfg.addNode(cfg_mod.IrNode.init(.nop));
    const exit = try cfg.addNode(cfg_mod.IrNode.init(.fn_exit));
    cfg.entry = entry;
    cfg.exit = exit;
    try cfg.addEdge(entry, exit);
    try cfg.addEdge(other, exit);

    var engine = AnalysisEngine.initWithSource(allocator, &cfg, source);
    defer engine.deinit();
    const root_counts = try engine.getPredecessorCounts(&cfg);
    const callee = (try engine.getOrBuildFunctionCfg(fn_node)) orelse return error.TestUnexpectedResult;
    const callee_counts = try engine.getPredecessorCounts(callee);
    try std.testing.expectEqual(@as(u8, 2), root_counts[ids.cfgIndex(exit)]);
    try std.testing.expectEqual(@as(u8, 1), callee_counts[ids.cfgIndex(callee.exit)]);
    try std.testing.expectEqual(@as(u8, 0), callee_counts[ids.cfgIndex(callee.entry)]);
    const cached_root = try engine.getPredecessorCounts(&cfg);
    try std.testing.expectEqualSlices(u8, root_counts, cached_root);
    const cached_callee = (try engine.getOrBuildFunctionCfg(fn_node)) orelse return error.TestUnexpectedResult;
    try std.testing.expect(cached_callee == callee);
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
        const callee = (try engine.getOrBuildFunctionCfg(fn_node)) orelse return error.TestUnexpectedResult;
        const counts = try engine.getPredecessorCounts(callee);
        try std.testing.expectEqual(@as(u8, 1), counts[ids.cfgIndex(callee.exit)]);
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
