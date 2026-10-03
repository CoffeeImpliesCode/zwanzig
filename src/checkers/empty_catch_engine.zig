const std = @import("std");
const checker_mod = @import("../checker.zig");
const Checker = checker_mod.Checker;
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const Source = @import("../source.zig").Source;
const ids = @import("../ids.zig");
const cfg_mod = @import("../cfg.zig");
const Cfg = cfg_mod.Cfg;
const CfgNodeId = ids.CfgNodeId;
const AstNodeId = ids.AstNodeId;
const engine_mod = @import("../engine.zig");

/// Detects empty catch handlers from CFG structure.
/// Dataflow analysis runs only when graph visualizations are requested.
pub const EmptyCatchEngineChecker = struct {
    pub const checker: Checker = .{
        .name = "empty-catch-engine",
        .default_severity = .warning,
        .type_requirement = .none,
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

        // Also check for empty catch blocks at file scope (top-level declarations)
        try checkTopLevelCatches(src, allocator, diagnostics);
    }

    fn checkTopLevelCatches(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
    ) CheckerError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        const main_tokens = tree.nodes.items(.main_token);
        const token_tags = tree.tokens.items(.tag);
        const token_starts = tree.tokens.items(.start);

        // Build a list of function body token ranges (start, end)
        const Range = struct { start: u32, end: u32 };
        var fn_body_ranges: std.ArrayList(Range) = .empty;
        defer fn_body_ranges.deinit(allocator);

        for (tags, 0..) |tag, i| {
            if (tag == .fn_decl) {
                const fn_data = datas[i];
                const body_node: u32 = @intFromEnum(fn_data.node_and_node[1]);
                if (body_node != 0) {
                    // Get token range of the function body
                    const body_start = main_tokens[body_node];
                    const body_end = tree.lastToken(@enumFromInt(body_node));
                    try fn_body_ranges.append(allocator, .{ .start = body_start, .end = body_end });
                }
            }
        }

        // Find catch nodes that are not inside any function body (by token position)
        for (tags, 0..) |tag, node_idx| {
            if (tag == .@"catch") {
                const catch_token = main_tokens[node_idx];

                // Check if this catch token is inside any function body
                var inside_fn = false;
                for (fn_body_ranges.items) |range| {
                    if (catch_token >= range.start and catch_token <= range.end) {
                        inside_fn = true;
                        break;
                    }
                }

                if (!inside_fn) {
                    // Check if the catch has an empty body
                    if (hasEmptyCatchBody(token_tags, catch_token)) {
                        const catch_start = token_starts[catch_token];
                        const range = try src.byteRangeToSourceRange(catch_start, catch_start + 5);

                        var diag = try Diagnostic.init(
                            allocator,
                            src.getFilePath(),
                            "empty-catch-engine",
                            .warning,
                            "Empty catch block detected. Consider handling the error or using '_' to explicitly ignore it.",
                            range,
                        );
                        errdefer diag.deinit(allocator);
                        try diagnostics.append(allocator, diag);
                    }
                }
            }
        }
    }

    fn hasEmptyCatchBody(token_tags: []const std.zig.Token.Tag, catch_token: u32) bool {
        // Scan forward from catch token to find the block
        var token_idx = catch_token + 1;
        const num_tokens = token_tags.len;

        // Skip whitespace, comments, and potential |err| capture
        while (token_idx < num_tokens) {
            const tok_tag = token_tags[token_idx];

            if (tok_tag == .l_brace) {
                // Found the opening brace of the catch block
                // Check if the next token is the closing brace
                const next_token_idx = token_idx + 1;
                if (next_token_idx < num_tokens and token_tags[next_token_idx] == .r_brace) {
                    return true;
                }
                return false;
            } else if (tok_tag == .pipe) {
                // Skip past the |err| capture: | identifier |
                token_idx += 1;
                while (token_idx < num_tokens and token_tags[token_idx] != .pipe) {
                    token_idx += 1;
                }
            } else if (tok_tag == .semicolon or tok_tag == .r_paren or tok_tag == .r_brace) {
                // Hit a boundary without finding a block - not an empty block pattern
                return false;
            }
            token_idx += 1;
        }
        return false;
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

        if (context.dump_exploded_graph_dir != null or
            context.dump_annotated_cfg_dir != null or
            context.dump_path_trace_dir != null)
        {
            var analysis = try context.getOrAnalyze(allocator, src, &cfg_handle, checker.name, .plain);
            defer analysis.deinit();
            const engine = analysis.engine;

            if (context.dump_exploded_graph_dir) |dir| {
                engine_mod.dot.writeExplodedGraphToFile(engine.getGraph(), context.io_context, dir, src.getFilePath(), cfg_handle.cfg.fn_name, allocator);
            }
            if (context.dump_annotated_cfg_dir) |dir| {
                engine_mod.dot.writeAnnotatedCfgToFile(engine.getGraph(), context.io_context, dir, src.getFilePath(), cfg_handle.cfg.fn_name, allocator);
            }
            if (context.dump_path_trace_dir) |dir| {
                engine_mod.dot.writePathTracesToFile(engine.getGraph(), context.io_context, dir, src.getFilePath(), cfg_handle.cfg.fn_name, allocator);
            }
        }

        // Examine CFG nodes for catch_expr with empty handlers
        for (cfg_handle.cfg.nodes.items) |cfg_node| {
            if (cfg_node.ir_node.tag == .catch_expr) {
                if (hasEmptyHandler(cfg_handle.cfg, cfg_node.index)) {
                    // Get source range from IR node
                    if (cfg_node.ir_node.source_range) |range| {
                        var diag = try Diagnostic.init(
                            allocator,
                            src.getFilePath(),
                            "empty-catch-engine",
                            .warning,
                            "Empty catch block detected. Consider handling the error or using '_' to explicitly ignore it.",
                            range,
                        );
                        errdefer diag.deinit(allocator);
                        try diagnostics.append(allocator, diag);
                    }
                }
            }
        }
    }

    /// Check if a catch_expr node has an empty handler.
    /// A catch handler is considered empty if the catch_error edge goes directly
    /// to the same merge node as catch_success (no intervening handler nodes).
    fn hasEmptyHandler(cfg: *const Cfg, catch_node_idx: CfgNodeId) bool {
        // Find both catch_error and catch_success targets
        var catch_error_target: ?CfgNodeId = null;
        var catch_success_target: ?CfgNodeId = null;

        for (cfg.edges.items) |edge| {
            if (edge.from == catch_node_idx) {
                if (edge.kind == .catch_error) {
                    catch_error_target = edge.to;
                } else if (edge.kind == .catch_success) {
                    catch_success_target = edge.to;
                }
            }
        }

        // Empty handler: catch_error goes directly to the same merge node as catch_success
        if (catch_error_target != null and catch_success_target != null) {
            return catch_error_target.? == catch_success_target.?;
        }
        return false;
    }
};

test "checker AST and CFG allocation failures are not empty reports" {
    const allocator = std.testing.allocator;
    const checkers = [_]*const Checker{
        &EmptyCatchEngineChecker.checker,
        &@import("swallowed_error.zig").SwallowedErrorChecker.checker,
        &@import("stack_escape_engine.zig").StackEscapeEngineChecker.checker,
        &@import("unreachable_code_checker.zig").UnreachableCodeChecker.checker,
    };
    for (checkers) |checker| {
        for ([_]bool{ false, true }) |parsed| {
            var failing = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
            var source = Source.init(
                if (parsed) allocator else failing.allocator(),
                "entry-oom.zig",
                "fn sample() void {}",
            );
            defer source.deinit();
            if (parsed) _ = try source.ast();
            var diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer {
                for (diagnostics.items) |*diagnostic| diagnostic.deinit(failing.allocator());
                diagnostics.deinit(failing.allocator());
            }

            try std.testing.expectError(
                error.OutOfMemory,
                checker.checkAst(&source, failing.allocator(), &diagnostics, .{ .build_metadata = null }),
            );
            try std.testing.expect(failing.has_induced_failure);
        }
    }
}

test "empty_catch_engine - top-level range and diagnostic allocations propagate" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "top-level-oom.zig",
        \\fn sample() void {}
        \\const result = fallible() catch {};
    );
    defer source.deinit();
    const tree = try source.ast();
    const Harness = struct {
        fn run(memory: std.mem.Allocator, ast: *const std.zig.Ast) !void {
            var input = Source.initParsed(memory, "top-level-oom.zig", ast);
            defer input.deinit();
            var diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer {
                for (diagnostics.items) |*diagnostic| diagnostic.deinit(memory);
                diagnostics.deinit(memory);
            }
            try EmptyCatchEngineChecker.checkTopLevelCatches(&input, memory, &diagnostics);
            try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
            try std.testing.expectEqual(@as(usize, 2), diagnostics.items[0].range.start.line);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Harness.run, .{tree});
}

test "empty_catch_engine - detects empty catch via CFG" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: empty catch block
    const code1: [:0]const u8 =
        \\fn foo() !i32 {
        \\    return 42;
        \\}
        \\fn bar() void {
        \\    const x = foo() catch {};
        \\    _ = x;
        \\}
    ;
    var source1 = Source.init(allocator, "test.zig", code1);
    defer source1.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    var stats: checker_mod.AnalysisStats = .{};
    const context = checker_mod.CheckerContext{
        .build_metadata = null,
        .analysis_stats = &stats,
        .analysis_limits = .{ .max_worklist_steps = 0 },
    };
    try EmptyCatchEngineChecker.checker.checkAst(&source1, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("empty-catch-engine", diagnostics.items[0].rule_id);
    try testing.expectEqual(@as(u64, 0), stats.total_runs);
}

test "empty_catch_engine - diagnostic append failure releases its message" {
    const allocator = std.testing.allocator;
    const declarations = "extern fn fallible() error{Failed}!void;\n";
    for ([_][:0]const u8{
        declarations ++ "fn sample() void { fallible() catch {}; }\n",
        declarations ++ "const result = fallible() catch {};\n",
    }) |code| {
        var source = Source.init(allocator, "oom.zig", code);
        defer source.deinit();
        var artifacts = checker_mod.CachedArtifacts.init(allocator);
        defer artifacts.deinit();
        const context: checker_mod.CheckerContext = .{
            .build_metadata = null,
            .cached_artifacts = &artifacts,
        };

        // Warm the AST and CFG so failure follows message allocation.
        const tree = try source.ast();
        for (tree.nodes.items(.tag), 0..) |tag, index| {
            if (tag != .fn_decl) continue;
            var cfg = (try context.getOrBuildCfg(allocator, &source, ids.astId(@intCast(index)))) orelse
                return error.TestUnexpectedResult;
            cfg.deinit();
        }
        var failing = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 1 });
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(failing.allocator());
            diagnostics.deinit(failing.allocator());
        }
        try std.testing.expectError(
            error.OutOfMemory,
            EmptyCatchEngineChecker.checker.checkAst(&source, failing.allocator(), &diagnostics, context),
        );
        try std.testing.expectEqual(failing.allocated_bytes, failing.freed_bytes);
    }
}

test "empty_catch_engine - graph output requests preserve analysis results" {
    const compat = @import("../compat.zig");
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();

    // Each output flag must work on its own. CFG output must not run dataflow.
    const Output = enum { cfg, exploded, annotated, traces };
    for ([_]Output{ .cfg, .exploded, .annotated, .traces }) |output| {
        var temp_dir = compat.TestDir.init();
        defer temp_dir.cleanup();
        const code: [:0]const u8 =
            \\const std = @import("std");
            \\extern fn fallible() error{Failed}!void;
            \\fn sample(allocator: std.mem.Allocator) !void {
            \\    const ptr = try allocator.alloc(u8, 1);
            \\    allocator.free(ptr);
            \\    allocator.free(ptr);
            \\    fallible() catch {};
            \\}
        ;
        var source = Source.init(allocator, "graphs.zig", code);
        defer source.deinit();
        const tree = try source.ast();
        const fn_node = for (tree.nodes.items(.tag), 0..) |tag, index| {
            if (tag == .fn_decl) break index;
        } else return error.TestUnexpectedResult;

        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        var stats: checker_mod.AnalysisStats = .{};
        var context: checker_mod.CheckerContext = .{
            .build_metadata = null,
            .analysis_stats = &stats,
            .io_context = &io_context,
        };
        switch (output) {
            .cfg => context.dump_cfg_dir = temp_dir.path(),
            .exploded => context.dump_exploded_graph_dir = temp_dir.path(),
            .annotated => context.dump_annotated_cfg_dir = temp_dir.path(),
            .traces => context.dump_path_trace_dir = temp_dir.path(),
        }
        try EmptyCatchEngineChecker.checker.checkAst(&source, allocator, &diagnostics, context);
        try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
        try std.testing.expectEqualStrings("empty-catch-engine", diagnostics.items[0].rule_id);
        try std.testing.expectEqual(@as(u64, if (output == .cfg) 0 else 1), stats.total_runs);

        const path = if (output == .cfg)
            try std.fmt.allocPrint(allocator, "{s}/graphs_sample_{d}.dot", .{ temp_dir.path(), fn_node })
        else
            try std.fmt.allocPrint(allocator, "{s}/graphs_sample_{s}.dot", .{ temp_dir.path(), @tagName(output) });
        defer allocator.free(path);
        const dot = try compat.readFileAlloc(&io_context, allocator, path, 1024 * 1024);
        defer allocator.free(dot);
        switch (output) {
            .cfg => {
                try std.testing.expect(std.mem.indexOf(u8, dot, "catch_error") != null);
                try std.testing.expect(std.mem.indexOf(u8, dot, "catch_success") != null);
            },
            .exploded => {
                try std.testing.expect(std.mem.indexOf(u8, dot, "(fn_entry) pre") != null);
                try std.testing.expect(std.mem.indexOf(u8, dot, "(fn_exit) post") != null);
            },
            .annotated => {
                const prefix = "fn_entry|states: ";
                const entry = std.mem.indexOf(u8, dot, prefix) orelse return error.TestUnexpectedResult;
                const count_start = entry + prefix.len;
                const count_end = std.mem.indexOfScalarPos(u8, dot, count_start, '}') orelse
                    return error.TestUnexpectedResult;
                const state_count = try std.fmt.parseInt(usize, dot[count_start..count_end], 10);
                try std.testing.expect(state_count > 0);
            },
            .traces => {
                try std.testing.expect(std.mem.indexOf(u8, dot, "double_free") != null);
                try std.testing.expect(std.mem.indexOf(u8, dot, "step 0|cfg:") != null);
            },
        }
    }
}

test "empty_catch_engine - no diagnostic for non-empty catch" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: non-empty catch block
    const code: [:0]const u8 =
        \\fn foo() !i32 {
        \\    return 42;
        \\}
        \\fn bar() i32 {
        \\    const x = foo() catch {
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
    try EmptyCatchEngineChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "empty_catch_engine - detects catch with capture but empty body" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: catch with error capture but empty body
    const code: [:0]const u8 =
        \\fn foo() !i32 {
        \\    return 42;
        \\}
        \\fn bar() void {
        \\    const x = foo() catch |_| {};
        \\    _ = x;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try EmptyCatchEngineChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
}

test "empty_catch_engine - detects empty catch at file scope" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: empty catch block at top-level (file scope)
    const code: [:0]const u8 =
        \\fn tryFunc() !i32 {
        \\    return 42;
        \\}
        \\const x = tryFunc() catch {};
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try EmptyCatchEngineChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("empty-catch-engine", diagnostics.items[0].rule_id);
}

test "empty_catch_engine - no diagnostic for non-empty catch at file scope" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Test case: non-empty catch block at top-level
    const code: [:0]const u8 =
        \\fn tryFunc() !i32 {
        \\    return error.Failed;
        \\}
        \\const x = tryFunc() catch {
        \\    @compileError("initialization failed");
        \\};
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try EmptyCatchEngineChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}
