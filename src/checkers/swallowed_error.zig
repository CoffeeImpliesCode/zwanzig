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

/// Engine-based checker that detects catch blocks that swallow errors.
/// An error is considered "swallowed" when:
/// - The catch block has a non-empty handler body
/// - The handler does NOT rethrow the error (return error or propagate)
/// - The handler does NOT log the error (call to std.debug/log functions)
/// - The handler simply ignores the error and continues execution
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
    fn isErrorSwallowed(
        cfg: *const Cfg,
        catch_node_idx: CfgNodeId,
        handler_ast: AstNodeId,
        payload_token: ?u32,
        tree: *const std.zig.Ast,
        parent_map: []const u32,
        engine: ?*const AnalysisEngine,
        allocator: std.mem.Allocator,
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
            if (handlerStoresCaughtError(tree, handler_ast, token)) return false;
        }

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

    const ErrorStoreFinder = struct {
        payload_name: []const u8,
        found: bool = false,
        stop: bool = false,

        pub fn visit(
            self: *ErrorStoreFinder,
            tree: *const std.zig.Ast,
            node: u32,
            tag: std.zig.Ast.Node.Tag,
        ) !void {
            if (tag != .assign) return;

            const assignment = tree.nodes.items(.data)[node].node_and_node;
            const lhs = @intFromEnum(assignment[0]);
            const rhs = @intFromEnum(assignment[1]);
            if (isDiscardIdentifier(tree, lhs)) return;
            if (!isPayloadIdentifier(tree, rhs, self.payload_name)) return;

            self.found = true;
            self.stop = true;
        }
    };

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

    fn handlerStoresCaughtError(
        tree: *const std.zig.Ast,
        handler_ast: AstNodeId,
        payload_token: u32,
    ) bool {
        const token_tags = tree.tokens.items(.tag);
        if (payload_token >= token_tags.len or token_tags[payload_token] != .identifier) {
            return false;
        }

        var finder = ErrorStoreFinder{
            .payload_name = tree.tokenSlice(payload_token),
        };
        ast_walk.walk(ErrorStoreFinder, tree, ids.astIndex(handler_ast), &finder) catch return false;
        return finder.found;
    }

    fn isPayloadIdentifier(
        tree: *const std.zig.Ast,
        node: u32,
        payload_name: []const u8,
    ) bool {
        const tags = tree.nodes.items(.tag);
        if (node == 0 or node >= tags.len or tags[node] != .identifier) return false;

        const token = tree.nodes.items(.main_token)[node];
        const token_tags = tree.tokens.items(.tag);
        if (token >= token_tags.len or token_tags[token] != .identifier) return false;
        return std.mem.eql(u8, tree.tokenSlice(token), payload_name);
    }

    fn isDiscardIdentifier(tree: *const std.zig.Ast, node: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (node == 0 or node >= tags.len or tags[node] != .identifier) return false;

        const token = tree.nodes.items(.main_token)[node];
        const token_tags = tree.tokens.items(.tag);
        if (token >= token_tags.len or token_tags[token] != .identifier) return false;
        return std.mem.eql(u8, tree.tokenSlice(token), "_");
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
