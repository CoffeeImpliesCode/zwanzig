const std = @import("std");
const checker_mod = @import("../checker.zig");
const Checker = checker_mod.Checker;
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const Source = @import("../source.zig").Source;
const ids = @import("../ids.zig");
const ast_walk = @import("../ast_walk.zig");
const cfg_mod = @import("../cfg.zig");
const Cfg = cfg_mod.Cfg;
const CfgNodeId = ids.CfgNodeId;
const AstNodeId = ids.AstNodeId;
const engine_mod = @import("../engine.zig");
const AnalysisEngine = engine_mod.AnalysisEngine;
const value = @import("../engine/value.zig");
const import_resolver = @import("../analysis/import_resolver.zig");

/// Engine-based checker that detects catch blocks that swallow errors.
/// An error is considered "swallowed" when:
/// - The catch block has a non-empty handler body
/// - The handler simply ignores the error and continues execution
/// - The handler stores the caught payload only on some paths, in a binding
///   that dies with the handler, or under a shadowed name
/// - The handler does NOT log the error (call to std.debug/log functions)
///
/// This checker uses the CFG and analysis engine to trace error handling paths
/// and identify catch handlers that swallow errors without proper handling.
pub const SwallowedErrorChecker = struct {
    pub const checker: Checker = .{
        .name = "swallowed-error",
        .default_severity = .warning,
        .checkAstFn = checkAst,
    };

    fn checkAst(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        context: checker_mod.CheckerContext,
    ) CheckerError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);

        // Find all function declarations and analyze each one
        for (0..tags.len) |i| {
            const tag = tags[i];
            if (tag == .fn_decl) {
                try analyzeFunction(src, allocator, ids.astId(@intCast(i)), diagnostics, context);
            }
        }
    }

    fn analyzeFunction(
        src: *Source,
        allocator: std.mem.Allocator,
        fn_node: AstNodeId,
        diagnostics: *std.ArrayList(Diagnostic),
        context: checker_mod.CheckerContext,
    ) CheckerError!void {
        var cfg_handle = (context.getOrBuildCfg(allocator, src, fn_node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidAst => return,
        }) orelse return;
        defer cfg_handle.deinit();

        const tree = try src.ast();
        const data = tree.nodes.items(.data);
        const node_tags = tree.nodes.items(.tag);
        const parent_map = try allocator.alloc(u32, node_tags.len);
        defer allocator.free(parent_map);
        @memset(parent_map, 0);
        ast_walk.fillParentMap(tree, ids.astIndex(fn_node), parent_map);

        var analysis = try context.getOrAnalyze(allocator, src, &cfg_handle, checker.name, .plain);
        defer analysis.deinit();
        const engine = analysis.engine;

        // Dump visualizations if requested
        if (context.dump_exploded_graph_dir) |dir| {
            engine_mod.dot.writeExplodedGraphToFile(engine.getGraph(), context.io_context, dir, src.getFilePath(), cfg_handle.cfg.fn_name, allocator);
        }
        if (context.dump_annotated_cfg_dir) |dir| {
            engine_mod.dot.writeAnnotatedCfgToFile(engine.getGraph(), context.io_context, dir, src.getFilePath(), cfg_handle.cfg.fn_name, allocator);
        }
        if (context.dump_path_trace_dir) |dir| {
            engine_mod.dot.writePathTracesToFile(engine.getGraph(), context.io_context, dir, src.getFilePath(), cfg_handle.cfg.fn_name, allocator);
        }

        // A handler that turns the error into the value this function hands
        // back is handling it, not swallowing it. The scan is per function and
        // structural, so the verdict does not depend on the engine finishing.
        var outcome = try OutcomeScan.run(tree, ids.astIndex(fn_node), allocator);
        defer outcome.deinit();

        // Examine CFG nodes for catch_expr with swallowed errors
        for (cfg_handle.cfg.nodes.items) |cfg_node| {
            if (cfg_node.ir_node.tag == .catch_expr) {
                const catch_ast = cfg_node.ir_node.ast_node orelse continue;
                const handler_ast = ids.astId(@intFromEnum(data[catch_ast].node_and_node[1]));
                if (!isBlockHandler(tree, handler_ast)) continue;
                const payload_token = catchPayloadToken(tree, ids.astId(catch_ast));
                const engine_ptr: ?*const AnalysisEngine = if (analysis.complete) engine else null;
                if (try isErrorSwallowed(
                    cfg_handle.cfg,
                    cfg_node.index,
                    handler_ast,
                    payload_token,
                    tree,
                    parent_map,
                    engine_ptr,
                    allocator,
                    &outcome,
                )) {
                    // Get source range from IR node
                    if (cfg_node.ir_node.source_range) |range| {
                        var diag = try Diagnostic.init(
                            allocator,
                            src.getFilePath(),
                            "swallowed-error",
                            .warning,
                            "Error is swallowed without logging or rethrowing. Consider handling the error properly.",
                            range,
                        );
                        errdefer diag.deinit(allocator);
                        try diagnostics.append(allocator, diag);
                    }
                }
            }
        }
    }

    /// Check if a catch_expr swallows an error.
    /// An error is swallowed if:
    /// 1. The catch handler is non-empty (has actual statements)
    /// 2. The handler does NOT return an error
    /// 3. The handler does NOT appear to log the error
    /// 4. The handler completes normally (reaches merge point)
    /// 5. The handler does NOT record the caught payload on every path that
    ///    reaches that merge point
    /// 6. The handler does NOT translate the error into the value the function
    ///    returns to its caller
    fn isErrorSwallowed(
        cfg: *const Cfg,
        catch_node_idx: CfgNodeId,
        handler_ast: AstNodeId,
        payload_token: ?u32,
        tree: *const std.zig.Ast,
        parent_map: []const u32,
        engine: ?*const AnalysisEngine,
        allocator: std.mem.Allocator,
        outcome: *const OutcomeScan,
    ) CheckerError!bool {
        // Find the catch_error edge
        var handler_entry: ?CfgNodeId = null;
        var merge_node: ?CfgNodeId = null;

        for (cfg.edges.items) |edge| {
            if (edge.from == catch_node_idx) {
                if (edge.kind == .catch_error) {
                    handler_entry = edge.to;
                } else if (edge.kind == .catch_success) {
                    // Track the merge node (where catch_success goes)
                    merge_node = edge.to;
                }
            }
        }

        // If no handler entry, no swallowed error (empty catch is handled separately)
        const entry = handler_entry orelse return false;

        // If handler entry is directly the merge node, it's empty (not swallowed)
        // This is the correct way to detect empty handlers - comparing to merge node
        if (merge_node != null and entry == merge_node.?) {
            return false;
        }

        if (payload_token) |token| {
            // The handler merge is the handler's normal continuation: a
            // catch without one leaves the function instead.
            if (try handlerStoresCaughtError(
                cfg,
                entry,
                merge_node orelse cfg.exit,
                handler_ast,
                token,
                tree,
                allocator,
            )) return false;
        }

        // A handler that turns the error into the function's own result is a
        // declared outcome, not a dropped error.
        if (handlerReportsOutcome(tree, ids.astIndex(handler_ast), outcome)) return false;

        // Trace through the handler to see if it:
        // 1. Returns an error (good)
        // 2. Contains a call (potentially logging)
        const scan = scanHandlerTokens(tree, handler_ast, parent_map);
        var has_return = scan.has_return;
        var has_call = scan.has_call;
        const has_input_progress = scan.has_input_progress and scan.has_control_transfer;
        var current_nodes: std.ArrayList(CfgNodeId) = .empty;
        defer current_nodes.deinit(allocator);
        var visited = std.AutoHashMap(CfgNodeId, void).init(allocator);
        defer visited.deinit();

        try current_nodes.append(allocator, entry);
        var reaches_merge_from_handler = false;

        while (current_nodes.items.len > 0) {
            const node_idx = current_nodes.pop() orelse continue;

            if (visited.contains(node_idx)) continue;
            try visited.put(node_idx, {});

            // Completion is an edge to this catch's merge, not a handler node count.
            if (merge_node != null and node_idx == merge_node.?) {
                reaches_merge_from_handler = true;
                continue;
            }

            const cfg_node = cfg.getNode(node_idx) orelse continue;

            switch (cfg_node.ir_node.tag) {
                .ret => {
                    has_return = true;
                },
                .call => {
                    has_call = true;
                },
                else => {},
            }

            // Standalone handlers reach their merge through catch_success edges.
            // The merge check above stops before statements after the catch.
            for (cfg.edges.items) |edge| {
                if (edge.from == node_idx) {
                    try current_nodes.append(allocator, edge.to);
                }
            }
        }

        // Check using the analysis engine for error state paths
        var reaches_merge_from_error = false;
        if (engine) |eng| {
            const graph = eng.getGraph();

            // Look for exploded nodes at the merge point with error_handled state
            if (merge_node) |merge| {
                for (graph.nodes.items) |exploded_node| {
                    if (exploded_node.point.node_index == merge and
                        exploded_node.point.kind == .pre)
                    {
                        // This node reached the merge - check if it came from error handler
                        // by looking at predecessors
                        for (exploded_node.predecessors.items) |pred_idx| {
                            if (graph.getNode(pred_idx)) |pred_node| {
                                if (pred_node.state.getErrorState() == .error_handled) {
                                    reaches_merge_from_error = true;
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }

        // Error is swallowed if:
        // - Handler reaches merge without return
        // - Handler doesn't have a call (potential logging)
        // - Analysis shows error path reaches normal completion
        if (engine != null and !has_return and !has_call and !has_input_progress and reaches_merge_from_error) {
            return true;
        }

        // Empty handlers were excluded above. With incomplete analysis, require
        // a CFG path from the non-empty handler to its normal continuation.
        return !has_return and !has_call and !has_input_progress and reaches_merge_from_handler;
    }

    fn isBlockHandler(tree: *const std.zig.Ast, handler_ast: AstNodeId) bool {
        const handler = ids.astIndex(handler_ast);
        const tags = tree.nodes.items(.tag);
        if (handler == 0 or handler >= tags.len) return false;

        return switch (tags[handler]) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => true,
            else => false,
        };
    }

    fn catchPayloadToken(tree: *const std.zig.Ast, catch_ast: AstNodeId) ?u32 {
        const catch_node = ids.astIndex(catch_ast);
        const main_tokens = tree.nodes.items(.main_token);
        if (catch_node == 0 or catch_node >= main_tokens.len) return null;

        const token_tags = tree.tokens.items(.tag);
        const catch_token = main_tokens[catch_node];
        if (catch_token + 2 >= token_tags.len) return null;
        if (token_tags[catch_token] != .keyword_catch) return null;
        if (token_tags[catch_token + 1] != .pipe) return null;

        var payload_token = catch_token + 2;
        if (token_tags[payload_token] == .asterisk) {
            payload_token += 1;
        }
        if (payload_token >= token_tags.len or token_tags[payload_token] != .identifier) return null;
        if (payload_token + 1 >= token_tags.len) return null;
        if (token_tags[payload_token + 1] != .pipe) return null;
        if (std.mem.eql(u8, tree.tokenSlice(payload_token), "_")) return null;
        return payload_token;
    }

    /// A path through the handler that has not stored the caught payload yet.
    const path_without_store: u2 = 1;
    /// A path through the handler that has already stored the caught payload.
    const path_with_store: u2 = 2;

    /// Prove that the handler records the caught payload on every path that
    /// continues past it, and therefore does not swallow the error.
    ///
    /// The proof walks the handler's CFG region from the handler entry to this
    /// catch's merge node and carries one bit per path: whether the payload has
    /// been stored so far. Only feasible edges are followed, so a statically
    /// unreachable arm such as `if (false)` contributes no path at all. A path
    /// that reaches the continuation without storing the payload leaves the
    /// handler with the error dropped, so the exemption is withheld. Paths that
    /// end in `return`, `unreachable`, or a propagated `try` error never
    /// continue and need no store.
    ///
    /// The walk is structural: it reads the CFG and the AST only, so the
    /// verdict does not depend on whether the analysis engine finished inside
    /// its budget.
    fn handlerStoresCaughtError(
        cfg: *const Cfg,
        entry: CfgNodeId,
        continuation: CfgNodeId,
        handler_ast: AstNodeId,
        payload_token: u32,
        tree: *const std.zig.Ast,
        allocator: std.mem.Allocator,
    ) CheckerError!bool {
        const token_tags = tree.tokens.items(.tag);
        if (payload_token >= token_tags.len or token_tags[payload_token] != .identifier) return false;

        var declared_names: std.ArrayList(HandlerBinding) = .empty;
        defer declared_names.deinit(allocator);
        try collectHandlerDeclarations(tree, ids.astIndex(handler_ast), &declared_names, allocator);

        const proof = PayloadStoreProof{
            .tree = tree,
            .payload_name = import_resolver.normalizeIdentifier(tree.tokenSlice(payload_token)),
            .declared_names = declared_names.items,
        };

        const paths = try allocator.alloc(u2, cfg.nodes.items.len);
        defer allocator.free(paths);
        @memset(paths, 0);

        var work: std.ArrayList(CfgNodeId) = .empty;
        defer work.deinit(allocator);

        const entry_index = ids.cfgIndex(entry);
        if (entry_index >= paths.len) return false;
        paths[entry_index] = if (proof.nodeStoresPayload(cfg, entry)) path_with_store else path_without_store;
        try work.append(allocator, entry);

        while (work.items.len > 0) {
            const node_idx = work.pop() orelse continue;
            const current = paths[ids.cfgIndex(node_idx)];
            if (current == 0) continue;

            for (cfg.edges.items) |edge| {
                if (edge.from != node_idx) continue;
                if (!isFeasibleEdge(tree, cfg, node_idx, edge)) continue;

                if (edge.to == continuation) {
                    if ((current & path_without_store) != 0) return false;
                    continue;
                }

                const target = ids.cfgIndex(edge.to);
                if (target >= paths.len) continue;
                const reached = if (proof.nodeStoresPayload(cfg, edge.to)) path_with_store else current;
                const merged = paths[target] | reached;
                if (merged == paths[target]) continue;
                paths[target] = merged;
                try work.append(allocator, edge.to);
            }
        }
        return true;
    }

    /// Filter the CFG edges a runtime path can actually take.
    ///
    /// `return` and `unreachable` end the path, a `try` error edge leaves the
    /// function, and a statically known condition removes the arm that cannot
    /// be selected.
    fn isFeasibleEdge(
        tree: *const std.zig.Ast,
        cfg: *const Cfg,
        from: CfgNodeId,
        edge: cfg_mod.CfgEdge,
    ) bool {
        const cfg_node = cfg.getNode(from) orelse return false;
        switch (cfg_node.ir_node.tag) {
            .ret, .unreachable_stmt => return false,
            .try_expr => {
                if (edge.kind == .try_error) return false;
            },
            .branch => {
                if (ifConditionLiteral(tree, cfg_node.ir_node)) |taken| {
                    if (edge.kind == .branch_true) return taken;
                    if (edge.kind == .branch_false) return !taken;
                }
            },
            .loop_header => {
                if (whileConditionLiteral(tree, cfg_node.ir_node)) |taken| {
                    if (edge.kind == .branch_true) return taken;
                    if (edge.kind == .loop_exit) return !taken;
                }
            },
            else => {},
        }
        return true;
    }

    /// Statically known `if` condition, if the branch node is an `if` whose
    /// condition is a `true`/`false` literal.
    fn ifConditionLiteral(tree: *const std.zig.Ast, ir_node: cfg_mod.IrNode) ?bool {
        const ast_node = ir_node.ast_node orelse return null;
        const tags = tree.nodes.items(.tag);
        if (ast_node >= tags.len) return null;
        switch (tags[ast_node]) {
            .@"if", .if_simple => {},
            else => return null,
        }
        const condition = ir_node.operand_node orelse return null;
        return value.evaluateBoolLiteral(tree, condition);
    }

    /// Statically known `while` condition, if the loop header's condition is a
    /// `true`/`false` literal.
    fn whileConditionLiteral(tree: *const std.zig.Ast, ir_node: cfg_mod.IrNode) ?bool {
        const ast_node = ir_node.ast_node orelse return null;
        const tags = tree.nodes.items(.tag);
        if (ast_node >= tags.len) return null;
        switch (tags[ast_node]) {
            .@"while", .while_simple, .while_cont => {},
            else => return null,
        }
        const full_while = tree.fullWhile(@enumFromInt(ast_node)) orelse return null;
        return value.evaluateBoolLiteral(tree, @intFromEnum(full_while.ast.cond_expr));
    }

    const HandlerBinding = struct {
        name: []const u8,
        declaration: u32 = 0,
    };

    /// Binding identity of the payload caught by one handler.
    const PayloadStoreProof = struct {
        tree: *const std.zig.Ast,
        payload_name: []const u8,
        declared_names: []const HandlerBinding,

        /// True when the node assigns the caught payload into a binding that
        /// outlives the handler.
        fn nodeStoresPayload(self: *const PayloadStoreProof, cfg: *const Cfg, node_idx: CfgNodeId) bool {
            const cfg_node = cfg.getNode(node_idx) orelse return false;
            if (cfg_node.ir_node.tag != .assign) return false;
            const ast_node = cfg_node.ir_node.ast_node orelse return false;

            const tags = self.tree.nodes.items(.tag);
            if (ast_node == 0 or ast_node >= tags.len or tags[ast_node] != .assign) return false;

            const assignment = self.tree.nodes.items(.data)[ast_node].node_and_node;
            const lhs = @intFromEnum(assignment[0]);
            const rhs = @intFromEnum(assignment[1]);
            if (isDiscardIdentifier(self.tree, lhs)) return false;
            if (!self.referencesCaughtPayload(rhs)) return false;

            return self.targetOutlivesHandler(lhs);
        }

        /// Follow immutable aliases through storage projections. Declaration
        /// tokens strictly decrease, so alias cycles need no depth cutoff.
        fn targetOutlivesHandler(self: *const PayloadStoreProof, lhs: u32) bool {
            var base = placeBase(self.tree, lhs);
            const indirect = base != lhs;
            var before = self.tree.firstToken(@enumFromInt(lhs));
            const tags = self.tree.nodes.items(.tag);
            const datas = self.tree.nodes.items(.data);
            while (identifierToken(self.tree, base)) |token| {
                const name = import_resolver.normalizeIdentifier(self.tree.tokenSlice(token));
                var binding: ?HandlerBinding = null;
                for (self.declared_names) |declared| {
                    if (!std.mem.eql(u8, declared.name, name)) continue;
                    if (binding != null) return false;
                    binding = declared;
                }
                const local = binding orelse return true;
                if (!indirect or local.declaration == 0) return false;
                const declaration = self.tree.fullVarDecl(@enumFromInt(local.declaration)) orelse return false;
                if (self.tree.tokenTag(declaration.ast.mut_token) != .keyword_const) return false;
                if (declaration.ast.mut_token >= before) return false;
                before = declaration.ast.mut_token;
                var initializer = @intFromEnum(declaration.ast.init_node.unwrap() orelse return false);
                if (initializer >= tags.len) return false;
                if (tags[initializer] == .address_of) initializer = @intFromEnum(datas[initializer].node);
                base = placeBase(self.tree, initializer);
            }
            return false;
        }

        /// True when the handler binds this name anywhere. Both sides are
        /// identifier slices with `@"..."` quoting normalized away.
        fn declaresName(self: *const PayloadStoreProof, name: []const u8) bool {
            for (self.declared_names) |declared| {
                if (std.mem.eql(u8, declared.name, name)) return true;
            }
            return false;
        }

        /// The caught binding answers to its name for the whole handler unless
        /// the handler binds that name again. Nothing outside the handler can
        /// shadow it, because the catch clause introduces the payload.
        fn referencesCaughtPayload(self: *const PayloadStoreProof, node: u32) bool {
            if (!isPayloadIdentifier(self.tree, node, self.payload_name)) return false;
            return !self.declaresName(self.payload_name);
        }
    };

    /// Root binding of an assignment target such as `state.saved`, `items[0]`,
    /// or `ptr.*`.
    fn placeBase(tree: *const std.zig.Ast, node: u32) u32 {
        const tags = tree.nodes.items(.tag);
        var current = node;
        while (current != 0 and current < tags.len) {
            const data = tree.nodes.items(.data)[current];
            current = switch (tags[current]) {
                .field_access => @intFromEnum(data.node_and_token[0]),
                .array_access => @intFromEnum(data.node_and_node[0]),
                .deref => @intFromEnum(data.node),
                .grouped_expression => @intFromEnum(data.node_and_token[0]),
                else => return current,
            };
        }
        return current;
    }

    fn identifierToken(tree: *const std.zig.Ast, node: u32) ?u32 {
        const tags = tree.nodes.items(.tag);
        if (node == 0 or node >= tags.len or tags[node] != .identifier) return null;
        const token = tree.nodes.items(.main_token)[node];
        if (!isIdentifierToken(tree, token)) return null;
        return token;
    }

    fn isIdentifierToken(tree: *const std.zig.Ast, token: u32) bool {
        const token_tags = tree.tokens.items(.tag);
        return token < token_tags.len and token_tags[token] == .identifier;
    }

    /// Binding name an identifier token answers to, with `@"..."` quoting
    /// normalized away so quoted and bare spellings compare equal.
    fn tokenName(tree: *const std.zig.Ast, token: u32) []const u8 {
        return import_resolver.normalizeIdentifier(tree.tokenSlice(token));
    }

    /// Binding name of an identifier node, or null when the node is not a
    /// plain identifier.
    fn identifierName(tree: *const std.zig.Ast, node: u32) ?[]const u8 {
        const token = identifierToken(tree, node) orelse return null;
        return tokenName(tree, token);
    }

    fn varDeclName(tree: *const std.zig.Ast, node: u32) ?u32 {
        const full = tree.fullVarDecl(@enumFromInt(node)) orelse return null;
        const name_token = full.ast.mut_token + 1;
        if (!isIdentifierToken(tree, name_token)) return null;
        return name_token;
    }

    fn isPayloadIdentifier(tree: *const std.zig.Ast, node: u32, payload_name: []const u8) bool {
        const token = identifierToken(tree, node) orelse return false;
        return std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(token)), payload_name);
    }

    fn isDiscardIdentifier(tree: *const std.zig.Ast, node: u32) bool {
        const token = identifierToken(tree, node) orelse return false;
        return std.mem.eql(u8, tree.tokenSlice(token), "_");
    }

    /// Record handler-local bindings. Immutable pointer aliases can lead to
    /// outside storage; local values and unresolved captures cannot.
    fn collectHandlerDeclarations(
        tree: *const std.zig.Ast,
        handler_ast: u32,
        names: *std.ArrayList(HandlerBinding),
        allocator: std.mem.Allocator,
    ) CheckerError!void {
        if (handler_ast == 0 or handler_ast >= tree.nodes.items(.tag).len) return;
        var collector = DeclNameCollector{ .names = names, .allocator = allocator };
        try ast_walk.walk(DeclNameCollector, tree, handler_ast, &collector);
    }

    const DeclNameCollector = struct {
        names: *std.ArrayList(HandlerBinding),
        allocator: std.mem.Allocator,
        stop: bool = false,

        pub fn visit(
            self: *@This(),
            tree: *const std.zig.Ast,
            node: u32,
            tag: std.zig.Ast.Node.Tag,
        ) !void {
            if (import_resolver.isVarDeclTag(tag)) {
                const name_token = varDeclName(tree, node) orelse return;
                try self.names.append(self.allocator, .{
                    .name = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)),
                    .declaration = node,
                });
                return;
            }
            switch (tag) {
                .fn_decl => try appendFnParamNames(tree, node, self.names, self.allocator),
                .@"if", .if_simple => {
                    const full_if = tree.fullIf(@enumFromInt(node)) orelse return;
                    try appendCaptureNames(tree, full_if.payload_token, self.names, self.allocator);
                    try appendCaptureNames(tree, full_if.error_token, self.names, self.allocator);
                },
                .@"while", .while_simple, .while_cont => {
                    const full_while = tree.fullWhile(@enumFromInt(node)) orelse return;
                    try appendCaptureNames(tree, full_while.payload_token, self.names, self.allocator);
                    try appendCaptureNames(tree, full_while.error_token, self.names, self.allocator);
                },
                .@"for", .for_simple => {
                    const full_for = tree.fullFor(@enumFromInt(node)) orelse return;
                    try appendCaptureNames(
                        tree,
                        if (full_for.payload_token != 0) full_for.payload_token else null,
                        self.names,
                        self.allocator,
                    );
                },
                else => {
                    const full_case = tree.fullSwitchCase(@enumFromInt(node)) orelse return;
                    try appendCaptureNames(tree, full_case.payload_token, self.names, self.allocator);
                },
            }
        }
    };

    /// Names bound by a capture such as `|value|`, `|*value|`, or
    /// `|item, index|`. The token points just past the opening pipe.
    fn appendCaptureNames(
        tree: *const std.zig.Ast,
        payload_token: ?u32,
        names: *std.ArrayList(HandlerBinding),
        allocator: std.mem.Allocator,
    ) CheckerError!void {
        var token = payload_token orelse return;
        const token_tags = tree.tokens.items(.tag);
        if (token >= token_tags.len) return;
        if (token_tags[token] == .pipe) token += 1;
        while (token < token_tags.len) : (token += 1) {
            if (token_tags[token] == .pipe) return;
            if (token_tags[token] != .identifier) continue;
            try appendName(tree, token, names, allocator);
        }
    }

    fn appendFnParamNames(
        tree: *const std.zig.Ast,
        fn_node: u32,
        names: *std.ArrayList(HandlerBinding),
        allocator: std.mem.Allocator,
    ) CheckerError!void {
        const tags = tree.nodes.items(.tag);
        if (fn_node >= tags.len or tags[fn_node] != .fn_decl) return;
        const proto_node = @intFromEnum(tree.nodes.items(.data)[fn_node].node_and_node[0]);
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buffer, @enumFromInt(proto_node)) orelse return;
        var parameters = proto.iterate(tree);
        while (parameters.next()) |parameter| {
            const name_token = parameter.name_token orelse continue;
            if (!isIdentifierToken(tree, name_token)) continue;
            try appendName(tree, name_token, names, allocator);
        }
    }

    /// Append a bound name with `@"..."` quoting normalized away, so quoted and
    /// bare spellings of one identifier compare equal.
    fn appendName(
        tree: *const std.zig.Ast,
        token: u32,
        names: *std.ArrayList(HandlerBinding),
        allocator: std.mem.Allocator,
    ) CheckerError!void {
        try names.append(allocator, .{ .name = import_resolver.normalizeIdentifier(tree.tokenSlice(token)) });
    }

    const ConditionIdentifierFinder = struct {
        name: []const u8,
        found: bool = false,
        stop: bool = false,

        pub fn visit(
            self: *@This(),
            tree: *const std.zig.Ast,
            node: u32,
            tag: std.zig.Ast.Node.Tag,
        ) !void {
            if (tag != .identifier or node >= tree.nodes.items(.main_token).len) return;
            const token = tree.nodes.items(.main_token)[node];
            if (token >= tree.tokens.items(.tag).len) return;
            if (std.mem.eql(u8, tree.tokenSlice(token), self.name)) {
                self.found = true;
                self.stop = true;
            }
        }
    };

    fn whileConditionReferencesIdentifier(
        tree: *const std.zig.Ast,
        while_node: u32,
        name: []const u8,
    ) bool {
        const full = tree.fullWhile(@enumFromInt(while_node)) orelse return false;
        var finder = ConditionIdentifierFinder{ .name = name };
        ast_walk.walk(ConditionIdentifierFinder, tree, @intFromEnum(full.ast.cond_expr), &finder) catch return false;
        return finder.found;
    }

    fn findEnclosingWhile(
        tree: *const std.zig.Ast,
        parent_map: []const u32,
        handler_ast: AstNodeId,
    ) ?u32 {
        const tags = tree.nodes.items(.tag);
        var node = ids.astIndex(handler_ast);
        while (node < parent_map.len) {
            const parent = parent_map[node];
            if (parent == 0 or parent >= tags.len) return null;
            switch (tags[parent]) {
                .@"while", .while_simple, .while_cont => return parent,
                else => node = parent,
            }
        }
        return null;
    }

    const TokenScan = struct {
        has_return: bool,
        has_call: bool,
        has_control_transfer: bool,
        has_input_progress: bool,
    };

    fn scanHandlerTokens(
        tree: *const std.zig.Ast,
        handler_ast: AstNodeId,
        parent_map: []const u32,
    ) TokenScan {
        if (ids.astIndex(handler_ast) == 0) {
            return .{
                .has_return = false,
                .has_call = false,
                .has_control_transfer = false,
                .has_input_progress = false,
            };
        }
        const token_tags = tree.tokens.items(.tag);
        const ast_index = ids.astIndex(handler_ast);
        const first = tree.firstToken(@enumFromInt(ast_index));
        const last = tree.lastToken(@enumFromInt(ast_index));
        if (first >= token_tags.len) {
            return .{
                .has_return = false,
                .has_call = false,
                .has_control_transfer = false,
                .has_input_progress = false,
            };
        }
        var has_return = false;
        var has_call = false;
        var has_control_transfer = false;
        var has_input_progress = false;
        const enclosing_while = findEnclosingWhile(tree, parent_map, handler_ast);
        var i = first;
        const end = if (last < token_tags.len) last else token_tags.len - 1;
        while (i <= end) : (i += 1) {
            const tag = token_tags[i];
            if (tag == .keyword_return) {
                has_return = true;
            }
            if (tag == .keyword_break or tag == .keyword_continue) {
                has_control_transfer = true;
            }
            if (!has_input_progress and tag == .plus_equal and i > first and token_tags[i - 1] == .identifier) {
                if (enclosing_while) |while_node| {
                    if (whileConditionReferencesIdentifier(tree, while_node, tree.tokenSlice(i - 1))) {
                        has_input_progress = true;
                    }
                }
            }
            if (!has_call and (tag == .identifier or tag == .builtin)) {
                var j = i + 1;
                if (j <= end and token_tags[j] == .period) {
                    while (j + 1 <= end and token_tags[j] == .period and token_tags[j + 1] == .identifier) {
                        j += 2;
                    }
                }
                if (j <= end and token_tags[j] == .l_paren) {
                    has_call = true;
                }
            }
        }
        return .{
            .has_return = has_return,
            .has_call = has_call,
            .has_control_transfer = has_control_transfer,
            .has_input_progress = has_input_progress,
        };
    }

    /// What one function hands back to its caller.
    ///
    /// A handler that turns the error into that value is handling it: the
    /// caller observes the failure instead of the error disappearing. The scan
    /// is per function and purely structural, so the verdict does not depend on
    /// whether the analysis engine finished inside its budget.
    const OutcomeScan = struct {
        tree: *const std.zig.Ast,
        allocator: std.mem.Allocator,
        /// Name the function returns, when every `return` names it. A binding
        /// is identified by name, not by token: a declaration and each of its
        /// uses are distinct tokens.
        result_name: ?[]const u8 = null,
        /// False once a `return` names something else or returns nothing.
        uniform: bool = true,
        /// The settled way this result records a failure, or null when the
        /// function has no single outcome to report.
        outcome_kind: ?OutcomeKind = null,
        /// Assignment nodes whose target root is a plain identifier.
        writes: std.ArrayList(u32) = .empty,
        /// Names whose address is taken, which would let a call change the
        /// result after the handler wrote it.
        borrowed: std.ArrayList([]const u8) = .empty,
        /// Every local declaration this function introduces.
        declarations: std.ArrayList(LocalDecl) = .empty,

        fn deinit(self: *OutcomeScan) void {
            self.writes.deinit(self.allocator);
            self.borrowed.deinit(self.allocator);
            self.declarations.deinit(self.allocator);
        }

        /// A local binding, with the name it introduces and whether it can be
        /// assigned after its initializer.
        const LocalDecl = struct { name: []const u8, node: u32, mutable: bool };

        fn run(
            tree: *const std.zig.Ast,
            fn_node: u32,
            allocator: std.mem.Allocator,
        ) CheckerError!OutcomeScan {
            var scan = OutcomeScan{ .tree = tree, .allocator = allocator };
            errdefer scan.deinit();
            var collector = OutcomeCollector{ .scan = &scan };
            try walkOutcome(tree, fn_node, &collector);
            resolveResult(&scan);
            return scan;
        }
    };

    /// `return` operands, local declarations, and the names that assignments
    /// and borrows name. A nested declaration is a separate function with its
    /// own result, so its body is never entered.
    const OutcomeCollector = struct {
        scan: *OutcomeScan,
        depth: u8 = 0,

        fn visit(self: *@This(), tree: *const std.zig.Ast, node: u32) CheckerError!void {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            switch (tags[node]) {
                .@"return" => {
                    const operand = datas[node].opt_node.unwrap() orelse {
                        self.scan.uniform = false;
                        return;
                    };
                    const name = resultName(tree, @intFromEnum(operand)) orelse {
                        self.scan.uniform = false;
                        return;
                    };
                    const known = self.scan.result_name orelse {
                        self.scan.result_name = name;
                        return;
                    };
                    if (!std.mem.eql(u8, known, name)) self.scan.uniform = false;
                },
                .address_of => {
                    const name = identifierName(tree, @intFromEnum(datas[node].node)) orelse return;
                    try self.scan.borrowed.append(self.scan.allocator, name);
                },
                .simple_var_decl,
                .local_var_decl,
                .aligned_var_decl,
                => {
                    const name_token = varDeclName(tree, node) orelse return;
                    const full = tree.fullVarDecl(@enumFromInt(node)) orelse return;
                    try self.scan.declarations.append(self.scan.allocator, .{
                        .name = tokenName(tree, name_token),
                        .node = node,
                        .mutable = tree.tokenTag(full.ast.mut_token) == .keyword_var,
                    });
                },
                .assign,
                .assign_mul,
                .assign_div,
                .assign_mod,
                .assign_add,
                .assign_sub,
                .assign_shl,
                .assign_shl_sat,
                .assign_shr,
                .assign_bit_and,
                .assign_bit_xor,
                .assign_bit_or,
                .assign_mul_wrap,
                .assign_add_wrap,
                .assign_sub_wrap,
                .assign_mul_sat,
                .assign_add_sat,
                .assign_sub_sat,
                => {
                    if (writeTargetName(tree, node) == null) return;
                    try self.scan.writes.append(self.scan.allocator, node);
                },
                else => {},
            }
        }

        fn child(tree: *const std.zig.Ast, child_node: u32, self: *@This()) CheckerError!void {
            const tags = tree.nodes.items(.tag);
            if (child_node != 0 and child_node < tags.len) {
                switch (tags[child_node]) {
                    .fn_decl, .test_decl => return,
                    else => {},
                }
            }
            try walkOutcome(tree, child_node, self);
        }
    };

    fn walkOutcome(
        tree: *const std.zig.Ast,
        node: u32,
        collector: *OutcomeCollector,
    ) CheckerError!void {
        const tags = tree.nodes.items(.tag);
        if (node == 0 or node >= tags.len) return;
        if (collector.depth == 64) return;
        collector.depth += 1;
        defer collector.depth -= 1;
        try collector.visit(tree, node);
        try ast_walk.walkChildren(OutcomeCollector, tree, node, collector, OutcomeCollector.child);
    }

    /// The one way this function's result records a failure.
    ///
    /// A rejection writes `false` into the returned boolean; a counter
    /// accumulates into the returned count. Writes that disagree, because one
    /// of them could hand the caller a success, leave no outcome to report.
    const OutcomeKind = enum { rejection, counter };

    /// Settle the result binding: exactly one mutable local must carry the name
    /// every `return` hands back, nothing may reach it through a borrow, and
    /// every write to it must encode the same failure.
    fn resolveResult(scan: *OutcomeScan) void {
        const result_name = scan.result_name orelse return;
        if (!scan.uniform) return;
        for (scan.borrowed.items) |name| {
            if (std.mem.eql(u8, name, result_name)) return;
        }
        const tree = scan.tree;
        var declaration: u32 = 0;
        for (scan.declarations.items) |local| {
            if (!std.mem.eql(u8, local.name, result_name)) continue;
            // A second binding of the same name makes a spelling match
            // ambiguous, so no write can be attributed to the result.
            if (declaration != 0 or !local.mutable) return;
            declaration = local.node;
        }
        if (declaration == 0) return;
        const is_boolean = bindingIsBoolean(tree, declaration);

        const tags = tree.nodes.items(.tag);
        var rejections: usize = 0;
        var counters: usize = 0;
        for (scan.writes.items) |write| {
            if (write == 0 or write >= tags.len) return;
            const target = writeTargetName(tree, write) orelse continue;
            if (!std.mem.eql(u8, target, result_name)) continue;
            switch (tags[write]) {
                .assign => {
                    if (!is_boolean or !assignsRejection(tree, write)) return;
                    rejections += 1;
                },
                .assign_add, .assign_sub => {
                    if (!counterChangeIsNonZero(tree, write)) return;
                    counters += 1;
                },
                else => return,
            }
        }
        if (rejections != 0 and counters == 0) {
            scan.outcome_kind = .rejection;
        } else if (counters != 0 and rejections == 0) {
            scan.outcome_kind = .counter;
        }
    }

    /// Name of a `return` operand that is exactly one identifier.
    fn resultName(tree: *const std.zig.Ast, node: u32) ?[]const u8 {
        const tags = tree.nodes.items(.tag);
        var current = node;
        for (0..4) |_| {
            if (current == 0 or current >= tags.len) return null;
            switch (tags[current]) {
                .identifier => return identifierName(tree, current),
                .grouped_expression => current = @intFromEnum(tree.nodes.items(.data)[current].node_and_token[0]),
                else => return null,
            }
        }
        return null;
    }

    /// Name an assignment writes, taken from the plain identifier its target
    /// is rooted at, so `state.saved` and `ptr.*` name `state` and `ptr`.
    ///
    /// Crediting the root is what the caller reads back: the returned value
    /// carries its own fields and elements and reaches whatever a pointer
    /// designates, so a write made through any of them is read through that
    /// same returned value. A different local that merely shares the spelling,
    /// or a call that could change the result behind the handler, is what this
    /// excludes — `resolveResult` demands one mutable declaration under the
    /// returned name whose address is taken nowhere.
    fn writeTargetName(tree: *const std.zig.Ast, node: u32) ?[]const u8 {
        const tags = tree.nodes.items(.tag);
        if (node == 0 or node >= tags.len) return null;
        const lhs = @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]);
        return identifierName(tree, placeBase(tree, lhs));
    }

    /// A local is a boolean when it is declared `bool` or initialized from a
    /// boolean literal.
    fn bindingIsBoolean(tree: *const std.zig.Ast, decl: u32) bool {
        const full = tree.fullVarDecl(@enumFromInt(decl)) orelse return false;
        if (full.ast.type_node.unwrap()) |type_node| {
            const node = @intFromEnum(type_node);
            const token = identifierToken(tree, node) orelse return false;
            return std.mem.eql(u8, tree.tokenSlice(token), "bool");
        }
        const init = @intFromEnum(full.ast.init_node.unwrap() orelse return false);
        return value.evaluateBoolLiteral(tree, init) != null;
    }

    /// True when the handler writes the function's result in the one way this
    /// function records a failure, so the caller observes the rejection or the
    /// failure count instead of the error vanishing.
    ///
    /// Every statement must be such a write or a control transfer, because a
    /// branch inside the handler could leave the result untouched on one path.
    /// `resolveResult` has already proved that no write anywhere in the
    /// function can turn the result back into a success, so another write of
    /// the same kind keeps the outcome observable.
    fn handlerReportsOutcome(
        tree: *const std.zig.Ast,
        handler_ast: u32,
        outcome: *const OutcomeScan,
    ) bool {
        const kind = outcome.outcome_kind orelse return false;
        const tags = tree.nodes.items(.tag);
        var inline_buffer: [2]u32 = undefined;
        const statements = ast_walk.getBlockStatements(tree, handler_ast, &inline_buffer) orelse return false;
        if (statements.len == 0) return false;

        var reports = false;
        for (statements) |statement| {
            if (statement == 0 or statement >= tags.len) return false;
            switch (tags[statement]) {
                .@"break", .@"continue", .@"return" => {},
                .assign => {
                    if (kind != .rejection) return false;
                    if (!writesResult(tree, statement, outcome)) return false;
                    reports = true;
                },
                .assign_add, .assign_sub => {
                    if (kind != .counter) return false;
                    if (!writesResult(tree, statement, outcome)) return false;
                    reports = true;
                },
                else => return false,
            }
        }
        return reports;
    }

    /// True when this statement writes the binding the settled outcome names.
    fn writesResult(tree: *const std.zig.Ast, statement: u32, outcome: *const OutcomeScan) bool {
        const result_name = outcome.result_name orelse return false;
        const target = writeTargetName(tree, statement) orelse return false;
        return std.mem.eql(u8, target, result_name);
    }

    /// True when `lhs = rhs` stores a value that is statically false, which is
    /// how a handler says the input was rejected.
    fn assignsRejection(tree: *const std.zig.Ast, statement: u32) bool {
        const rhs = @intFromEnum(tree.nodes.items(.data)[statement].node_and_node[1]);
        return staticBool(tree, rhs, 0) == false;
    }

    /// True when a `+=` or `-=` actually records a failure. Only a written-out
    /// nonzero integer counts: `+= 0`, a constant known to be zero, and an
    /// operand whose value is not spelled out all leave the returned count at
    /// the success value the caller already sees.
    fn counterChangeIsNonZero(tree: *const std.zig.Ast, statement: u32) bool {
        const rhs = @intFromEnum(tree.nodes.items(.data)[statement].node_and_node[1]);
        return positiveIntLiteral(tree, rhs, 0);
    }

    /// A nonzero integer literal, following only parentheses.
    fn positiveIntLiteral(tree: *const std.zig.Ast, node: u32, depth: u8) bool {
        if (depth > 2) return false;
        const tags = tree.nodes.items(.tag);
        if (node == 0 or node >= tags.len) return false;
        switch (tags[node]) {
            .number_literal => {
                const token = tree.nodes.items(.main_token)[node];
                const amount = integerLiteralValue(tree, token) orelse return false;
                return amount != 0;
            },
            .grouped_expression => return positiveIntLiteral(
                tree,
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                depth + 1,
            ),
            else => return false,
        }
    }

    /// Value of a plain integer literal in any base. `_` separators are
    /// ignored, and the float, exponent, and hex-float forms a count never
    /// uses are rejected rather than guessed at.
    fn integerLiteralValue(tree: *const std.zig.Ast, token: u32) ?u64 {
        const token_tags = tree.tokens.items(.tag);
        if (token >= token_tags.len or token_tags[token] != .number_literal) return null;
        const slice = tree.tokenSlice(token);
        if (slice.len == 0) return null;
        for (slice) |c| {
            if (c == '.' or c == 'e' or c == 'E' or c == 'p' or c == 'P') return null;
        }
        var base: u64 = 10;
        var digits = slice;
        if (slice.len > 2 and slice[0] == '0') {
            switch (slice[1]) {
                'x', 'X' => base = 16,
                'o', 'O' => base = 8,
                'b', 'B' => base = 2,
                else => {},
            }
            if (base != 10) digits = slice[2..];
        }
        if (digits.len == 0) return null;
        var parsed_value: u64 = 0;
        for (digits) |c| {
            if (c == '_') continue;
            const digit: u64 = switch (c) {
                '0'...'9' => @intCast(c - '0'),
                'a'...'f' => @intCast(10 + (c - 'a')),
                'A'...'F' => @intCast(10 + (c - 'A')),
                else => return null,
            };
            if (digit >= base) return null;
            parsed_value = std.math.add(u64, std.math.mul(u64, parsed_value, base) catch return null, digit) catch return null;
        }
        return parsed_value;
    }

    /// Statically known boolean, following only parentheses and negation.
    fn staticBool(tree: *const std.zig.Ast, node: u32, depth: u8) ?bool {
        if (depth > 4) return null;
        if (value.evaluateBoolLiteral(tree, node)) |literal| return literal;
        const tags = tree.nodes.items(.tag);
        if (node == 0 or node >= tags.len) return null;
        switch (tags[node]) {
            .grouped_expression => return staticBool(
                tree,
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                depth + 1,
            ),
            .bool_not => {
                const inner = staticBool(tree, @intFromEnum(tree.nodes.items(.data)[node].node), depth + 1) orelse
                    return null;
                return !inner;
            },
            else => return null,
        }
    }
};

test "swallowed_error - no diagnostic for catch that returns error" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: catch that returns error (not swallowed)
    const code: [:0]const u8 =
        \\fn foo() !i32 {
        \\    return error.Failed;
        \\}
        \\fn bar() !i32 {
        \\    const x = foo() catch |err| {
        \\        return err;
        \\    };
        \\    return x;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "swallowed_error - no diagnostic for catch handler that returns in switch" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() !i32 {
        \\    return error.FontUnavailable;
        \\}
        \\fn bar() !i32 {
        \\    const x = foo() catch |err| switch (err) {
        \\        error.FontUnavailable => return err,
        \\        error.OutOfMemory => return err,
        \\    };
        \\    return x;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "swallowed_error - no diagnostic for catch handler with call in switch" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn foo() !i32 {
        \\    return error.Failed;
        \\}
        \\fn bar() i32 {
        \\    const x = foo() catch |err| switch (err) {
        \\        error.Failed => std.debug.print("oops\\n", .{}),
        \\        else => {},
        \\    };
        \\    _ = x;
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "swallowed_error - no diagnostic for catch with call (logging)" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: catch that logs (has a call - not swallowed)
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn foo() !i32 {
        \\    return error.Failed;
        \\}
        \\fn bar() i32 {
        \\    const x = foo() catch |err| {
        \\        std.debug.print("Error: {}\n", .{err});
        \\        return 0;
        \\    };
        \\    return x;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "swallowed_error - no diagnostic for empty catch" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: empty catch (handled by empty-catch rule, not swallowed-error)
    const code: [:0]const u8 =
        \\fn foo() !i32 {
        \\    return 42;
        \\}
        \\fn bar() void {
        \\    const x = foo() catch {};
        \\    _ = x;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "swallowed_error - no diagnostic for catch mapped to error" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn operation() error{Failed}!void {
        \\    return error.Failed;
        \\}
        \\fn mappedOperation() error{Mapped}!void {
        \\    return operation() catch error.Mapped;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "swallowed_error - no diagnostic for catch mapped to null" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn operation() error{Failed}!i32 {
        \\    return error.Failed;
        \\}
        \\fn optionalOperation() ?i32 {
        \\    return operation() catch null;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "swallowed_error - no diagnostic for catch that captures error state" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn operation() error{Failed}!void {
        \\    return error.Failed;
        \\}
        \\fn rememberOperationError() ?anyerror {
        \\    var operation_error: ?anyerror = null;
        \\    operation() catch |err| {
        \\        operation_error = err;
        \\    };
        \\    return operation_error;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "swallowed_error - detects swallowed error with assignment only" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: catch that just assigns to a variable (swallowed)
    const code: [:0]const u8 =
        \\fn foo() !i32 {
        \\    return error.Failed;
        \\}
        \\fn bar() i32 {
        \\    var y: i32 = 0;
        \\    const x = foo() catch |_| {
        \\        y = 1;
        \\    };
        \\    _ = x;
        \\    return y;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("swallowed-error", diagnostics.items[0].rule_id);
}

test "swallowed_error - fallback stops at the handler merge and requires completion" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\fn fail() error{Failed}!void {
        \\    return error.Failed;
        \\}
        \\fn afterCatch() void {}
        \\fn unsafeControl() void {
        \\    var ignored = false;
        \\    fail() catch {
        \\        ignored = true;
        \\    };
        \\    afterCatch();
        \\    _ = ignored;
        \\}
        \\fn terminatingHandler() void {
        \\    var ignored = false;
        \\    fail() catch {
        \\        ignored = true;
        \\        unreachable;
        \\    };
        \\    _ = ignored;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    // A later call cannot handle this error; an unreachable handler cannot resume.
    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
        try std.testing.expectEqualStrings("swallowed-error", diagnostics.items[0].rule_id);
        try std.testing.expectEqual(@as(usize, 7), diagnostics.items[0].range.start.line);
    }
}

test "skript regression: malformed input recovery is not a swallowed error" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\fn decode() error{Malformed}!void {
        \\    return error.Malformed;
        \\}
        \\fn recoverMalformedInput(bytes: []const u8) usize {
        \\    var index: usize = 0;
        \\    while (index < bytes.len) {
        \\        decode() catch {
        \\            index += 1;
        \\            continue;
        \\        };
        \\    }
        \\    return index;
        \\}
        \\fn unsafeControl() void {
        \\    var ignored = false;
        \\    decode() catch {
        \\        ignored = true;
        \\    };
        \\    _ = ignored;
        \\}
    ;
    var source = Source.init(allocator, "skript-regression.zig", code);
    defer source.deinit();

    // The AST fallback must retain recovery handling when analysis stops early.
    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        var stats: checker_mod.AnalysisStats = .{};
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_stats = &stats,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
        try std.testing.expectEqualStrings("swallowed-error", diagnostics.items[0].rule_id);
        try std.testing.expectEqual(@as(usize, 16), diagnostics.items[0].range.start.line);
        try std.testing.expectEqual(@as(u64, 3), stats.total_runs);
    }
}

test "swallowed_error - storing on one branch only is not proof" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const State = struct { saved: ?anyerror = null, ignored: bool = false };
        \\fn operation() error{Failed}!void { return error.Failed; }
        \\fn record(state: *State, keep: bool) void {
        \\    operation() catch |err| {
        \\        if (keep) { state.saved = err; }
        \\        state.ignored = true;
        \\    };
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    // The store proof is structural, so the verdict holds for the engine run
    // and for the conservative fallback alike.
    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
        try std.testing.expectEqualStrings("swallowed-error", diagnostics.items[0].rule_id);
        try std.testing.expectEqual(@as(usize, 4), diagnostics.items[0].range.start.line);
    }
}

test "swallowed_error - storing in an unreachable branch is not proof" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const State = struct { saved: ?anyerror = null, ignored: bool = false };
        \\fn operation() error{Failed}!void { return error.Failed; }
        \\fn record(state: *State) void {
        \\    operation() catch |err| {
        \\        if (false) { state.saved = err; }
        \\        state.ignored = true;
        \\    };
        \\}
        \\fn spin(state: *State) void {
        \\    operation() catch |err| {
        \\        while (false) { state.saved = err; }
        \\        state.ignored = true;
        \\    };
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
        try std.testing.expectEqual(@as(usize, 4), diagnostics.items[0].range.start.line);
        try std.testing.expectEqual(@as(usize, 10), diagnostics.items[1].range.start.line);
        for (diagnostics.items) |diagnostic| {
            try std.testing.expectEqualStrings("swallowed-error", diagnostic.rule_id);
        }
    }
}

test "swallowed_error - a handler-local binding is not a store" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const State = struct { saved: ?anyerror = null, ignored: bool = false };
        \\fn operation() error{Failed}!void { return error.Failed; }
        \\fn record(state: *State) void {
        \\    operation() catch |err| {
        \\        var local: ?anyerror = null;
        \\        local = err;
        \\        state.ignored = local != null;
        \\    };
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
        try std.testing.expectEqualStrings("swallowed-error", diagnostics.items[0].rule_id);
    }
}

test "swallowed_error - a shadowed name is not the caught payload" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const State = struct { saved: ?anyerror = null };
        \\fn operation() error{Failed}!void { return error.Failed; }
        \\fn shadowedDecl(state: *State) void {
        \\    operation() catch |err| {
        \\        const err = error.Shadowed;
        \\        state.saved = err;
        \\    };
        \\}
        \\fn shadowedCapture(state: *State, maybe: ?anyerror) void {
        \\    operation() catch |err| {
        \\        if (maybe) |err| {
        \\            state.saved = err;
        \\        } else {
        \\            state.saved = err;
        \\        }
        \\    };
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    // Both arms store into `state`, but the then arm stores the if-capture
    // that shadows the caught payload, so the handler still drops the error.
    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
        try std.testing.expectEqual(@as(usize, 4), diagnostics.items[0].range.start.line);
        try std.testing.expectEqual(@as(usize, 10), diagnostics.items[1].range.start.line);
        for (diagnostics.items) |diagnostic| {
            try std.testing.expectEqualStrings("swallowed-error", diagnostic.rule_id);
        }
    }
}

test "swallowed_error - storing on every path keeps the exemption" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const State = struct { first: ?anyerror = null, second: ?anyerror = null };
        \\fn operation() error{Failed}!void { return error.Failed; }
        \\fn bothBranches(state: *State, first: bool) void {
        \\    operation() catch |err| {
        \\        if (first) { state.first = err; } else { state.second = err; }
        \\    };
        \\}
        \\fn everyArm(state: *State, code: u8) void {
        \\    operation() catch |err| {
        \\        switch (code) {
        \\            0 => { state.first = err; },
        \\            else => { state.second = err; },
        \\        }
        \\    };
        \\}
        \\fn afterMaybeEmptyLoop(state: *State, keep: bool) void {
        \\    operation() catch |err| {
        \\        while (keep) { state.first = err; }
        \\        state.second = err;
        \\    };
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);
    }
}

test "swallowed_error - a returned rejection or failure count is not swallowed" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn mayFail() error{BadByte}!u8 { return error.BadByte; }
        \\const Sanitizer = struct {
        \\    last: []const u8 = "",
        \\    pub fn acceptCluster(self: *Sanitizer, cluster: []const u8) bool {
        \\        var accepted = true;
        \\        var i: usize = 0;
        \\        while (i < cluster.len) {
        \\            const len: usize = std.unicode.utf8ByteSequenceLength(cluster[i]) catch {
        \\                accepted = false;
        \\                break;
        \\            };
        \\            i += len;
        \\        }
        \\        self.last = cluster;
        \\        return accepted;
        \\    }
        \\};
        \\pub fn tallied() u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected += 1;
        \\    };
        \\    return rejected;
        \\}
        \\pub fn subtally() i8 {
        \\    var rejected: i8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected -= 1;
        \\    };
        \\    return rejected;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    // The verdict is structural, so it holds for the engine run and for the
    // conservative fallback alike.
    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);
    }
}

test "swallowed_error - a write through a field or index of the result is the caller's outcome" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Stats = struct { failures: u8 = 0 };
        \\fn mayFail() error{BadByte}!void { return error.BadByte; }
        \\fn tallyThroughField() Stats {
        \\    var stats = Stats{};
        \\    _ = mayFail() catch {
        \\        stats.failures += 1;
        \\    };
        \\    return stats;
        \\}
        \\fn tallyThroughIndex() [2]u8 {
        \\    var counts = [_]u8{ 0, 0 };
        \\    _ = mayFail() catch {
        \\        counts[0] += 1;
        \\    };
        \\    return counts;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    // The handler writes storage the returned value carries, so the caller
    // reads the failure back out of it: crediting the target's root is what
    // makes these two handlers exemptions rather than warnings.
    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);
    }
}

test "swallowed_error - a result that never reaches the caller is still swallowed" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\fn mayFail() error{BadByte}!u8 { return error.BadByte; }
        \\fn report(slot: *u8) void { _ = slot; }
        \\fn arbitraryValue() i32 {
        \\    var y: i32 = 0;
        \\    _ = mayFail() catch {
        \\        y = 1;
        \\    };
        \\    return y;
        \\}
        \\fn acceptedValue() bool {
        \\    var ok = true;
        \\    _ = mayFail() catch {
        \\        ok = true;
        \\    };
        \\    return ok;
        \\}
        \\fn overwrittenTally() u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected += 1;
        \\    };
        \\    rejected = 0;
        \\    return rejected;
        \\}
        \\fn borrowedTally() u8 {
        \\    var rejected: u8 = 0;
        \\    report(&rejected);
        \\    _ = mayFail() catch {
        \\        rejected += 1;
        \\    };
        \\    return rejected;
        \\}
        \\fn shadowedTally() u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail() catch {
        \\        var rejected: u8 = 9;
        \\        rejected += 1;
        \\        _ = rejected;
        \\    };
        \\    return rejected;
        \\}
        \\fn notReturned() u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected += 1;
        \\    };
        \\    return 0;
        \\}
        \\fn conditionallyReturned(flag: bool) u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected += 1;
        \\    };
        \\    if (flag) return rejected;
        \\    return 0;
        \\}
        \\fn branchedHandler(flag: bool) u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail() catch {
        \\        if (flag) rejected += 1;
        \\    };
        \\    return rejected;
        \\}
        \\fn zeroIncrement() u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected += 0;
        \\    };
        \\    return rejected;
        \\}
        \\fn zeroDecrement() i8 {
        \\    var rejected: i8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected -= 0;
        \\    };
        \\    return rejected;
        \\}
        \\fn zeroConstIncrement() u8 {
        \\    var rejected: u8 = 0;
        \\    const bump: u8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected += bump;
        \\    };
        \\    return rejected;
        \\}
        \\fn maybeZeroIncrement(step: u8) u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail() catch {
        \\        rejected += step;
        \\    };
        \\    return rejected;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    // Every one of these handlers either stores an arbitrary value, lets the
    // result be discarded before the caller sees it, can leave it untouched on
    // a path, or changes a counter by an amount that records nothing.
    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 12), diagnostics.items.len);
        for (diagnostics.items) |diagnostic| {
            try std.testing.expectEqualStrings("swallowed-error", diagnostic.rule_id);
        }
    }
}

test "swallowed_error - the rejected-by-the-result reducer reports no finding" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn mayFail(byte: u8) error{ PermissionDenied, BadByte }!u8 {
        \\    _ = byte;
        \\    return error.BadByte;
        \\}
        \\pub const Sanitizer = struct {
        \\    last: []const u8 = "",
        \\
        \\    pub fn acceptCluster(self: *Sanitizer, cluster: []const u8) bool {
        \\        var accepted = true;
        \\        var i: usize = 0;
        \\        while (i < cluster.len) {
        \\            const len: usize = std.unicode.utf8ByteSequenceLength(cluster[i]) catch {
        \\                accepted = false;
        \\                break;
        \\            };
        \\            if (len > cluster.len - i) {
        \\                accepted = false;
        \\                break;
        \\            }
        \\            i += len;
        \\        }
        \\        self.last = cluster;
        \\        return accepted;
        \\    }
        \\};
        \\pub fn rethrown(byte: u8) error{ PermissionDenied, BadByte }!u8 {
        \\    return mayFail(byte) catch |err| return err;
        \\}
        \\pub fn logged(byte: u8) u8 {
        \\    return mayFail(byte) catch |err| blk: {
        \\        std.log.err("cluster rejected: {any}", .{err});
        \\        break :blk 0;
        \\    };
        \\}
        \\pub fn discarded(byte: u8) void {
        \\    _ = mayFail(byte) catch {};
        \\}
        \\pub fn tallied(byte: u8) u8 {
        \\    var rejected: u8 = 0;
        \\    _ = mayFail(byte) catch {
        \\        rejected += 1;
        \\    };
        \\    return rejected;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    // The returned binding is spelled by a declaration token and by separate
    // use tokens; the rethrow, the log, and the empty discard keep their own
    // verdicts, and the empty discard stays the empty-catch rule's business.
    for ([_]?usize{ null, 0 }) |max_steps| {
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try SwallowedErrorChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = null,
            .analysis_limits = .{ .max_worklist_steps = max_steps },
        });
        try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);
    }
}
