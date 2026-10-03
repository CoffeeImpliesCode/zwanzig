const std = @import("std");
const checker_mod = @import("../checker.zig");
const Checker = checker_mod.Checker;
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const Source = @import("../source.zig").Source;
const TypeContext = @import("../type_context.zig").TypeContext;
const config_mod = @import("../config.zig");
const Config = config_mod.Config;
const ResourceModel = config_mod.ResourceModel;
const ids = @import("../ids.zig");
const engine_mod = @import("../engine.zig");
const store_mod = @import("../engine/store.zig");
const StoreViolation = store_mod.StoreViolation;

/// Engine-based checker that reports store violations (double-free, free without alloc).
pub const StoreViolationsEngineChecker = struct {
    pub const checker: Checker = .{
        .name = "store-violations-engine",
        .default_severity = .err,
        .type_requirement = .optional,
        .checkAstFn = checkAst,
    };

    const ReportedKey = struct { u32, store_mod.StoreViolationKind };

    fn checkAst(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        context: checker_mod.CheckerContext,
    ) CheckerError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);

        var reported: std.AutoHashMap(ReportedKey, void) = .init(allocator);
        defer reported.deinit();

        for (0..tags.len) |i| {
            if (tags[i] == .fn_decl) {
                try analyzeFunction(src, allocator, ids.astId(@intCast(i)), diagnostics, context, &reported);
            }
        }
    }

    fn analyzeFunction(
        src: *Source,
        allocator: std.mem.Allocator,
        fn_node: ids.AstNodeId,
        diagnostics: *std.ArrayList(Diagnostic),
        context: checker_mod.CheckerContext,
        reported: *std.AutoHashMap(ReportedKey, void),
    ) CheckerError!void {
        var cfg_handle = (context.getOrBuildCfg(allocator, src, fn_node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidAst => return,
        }) orelse return;
        defer cfg_handle.deinit();

        var analysis = try context.getOrAnalyze(allocator, src, &cfg_handle, checker.name, .configured);
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

        if (!analysis.complete) return;

        for (engine.getGraph().nodes.items) |node| {
            for (node.state.getStoreViolations()) |violation| {
                const token = if (violation.call_token) |t| t else ids.varIndex(violation.region);
                const key: ReportedKey = .{ token, violation.kind };
                if (reported.contains(key)) continue;
                try reported.put(key, {});
                try emitViolationDiagnostic(src, allocator, diagnostics, violation);
            }
        }
    }

    fn emitViolationDiagnostic(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        violation: StoreViolation,
    ) CheckerError!void {
        const message = switch (violation.kind) {
            .double_free => "double-free detected for resource",
            .free_without_alloc => "free without tracked allocation",
            .double_close => "double-close detected for resource",
            .close_without_open => "close without tracked open",
            .use_after_free => "use after free",
            .use_after_close => "use after close",
            .resource_leak => "resource leak: allocation or open not released",
            .defer_frees_escapee => "resource is freed by defer but already escaped into an outer container — use-after-free",
        };

        const token = violation.call_token orelse ids.varIndex(violation.region);
        const loc = try src.tokenLocation(token);

        var diag = try Diagnostic.initAtLocation(
            allocator,
            src.getFilePath(),
            "store-violations-engine",
            .err,
            message,
            loc.line,
            loc.column,
        );
        errdefer diag.deinit(allocator);

        try diagnostics.append(allocator, diag);
    }
};

test "store_violations_engine propagates AST and CFG allocation failures" {
    const testing = std.testing;
    for ([_]bool{ false, true }) |preparse| {
        var failing = testing.FailingAllocator.init(testing.allocator, .{});
        const allocator = failing.allocator();
        {
            var source = Source.init(allocator, "store-oom.zig", "fn foo() void {}");
            defer source.deinit();
            if (preparse) _ = try source.ast();
            failing.fail_index = failing.alloc_index;
            failing.resize_fail_index = failing.resize_index;

            var diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer {
                for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
                diagnostics.deinit(allocator);
            }
            try testing.expectError(error.OutOfMemory, StoreViolationsEngineChecker.checker.checkAst(
                &source,
                allocator,
                &diagnostics,
                .{ .build_metadata = null },
            ));
        }
        try testing.expectEqual(failing.allocated_bytes, failing.freed_bytes);
    }
}

test "store violation diagnostic propagates allocation failures without leaks" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testStoreDiagnosticAllocationFailure, .{});
}

fn testStoreDiagnosticAllocationFailure(allocator: std.mem.Allocator) !void {
    const code: [:0]const u8 =
        \\fn foo(pointer: usize) void {
        \\    free(pointer);
        \\}
    ;
    var source = Source.init(allocator, "store-oom.zig", code);
    defer source.deinit();
    const tree = try source.ast();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    for (tree.tokens.items(.tag), 0..) |tag, index| {
        const token: u32 = @intCast(index);
        if (tag != .identifier or !std.mem.eql(u8, tree.tokenSlice(token), "free")) continue;
        try StoreViolationsEngineChecker.emitViolationDiagnostic(&source, allocator, &diagnostics, .{
            .region = ids.varId(token),
            .kind = .free_without_alloc,
            .call_token = token,
        });
        try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
        try std.testing.expectEqual(@as(usize, 2), diagnostics.items[0].range.start.line);
        return;
    }
    return error.TestUnexpectedResult;
}

test "store_violations_engine reports double free" {
    const testing = std.testing;
    const allocator = testing.allocator;

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
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| {
            diag.deinit(allocator);
        }
        diagnostics.deinit(allocator);
    }

    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{ .build_metadata = null, .type_context = &type_ctx });
    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("store-violations-engine", diagnostics.items[0].rule_id);
    try testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "double-free") != null);
}

test "store_violations_engine keeps fractional and wide integer paths reachable" {
    // Local aliases have scalar state, so integer-only refinement cannot hide behind
    // an absent parameter value. Each resource error lies on a feasible numeric path.
    const cases = [_]struct { value_type: []const u8, first: []const u8, second: []const u8, expected: usize }{
        .{ .value_type = "f64", .first = "value > 0", .second = "value < 1", .expected = 1 },
        .{ .value_type = "u64", .first = "value > 0", .second = "value > 9223372036854775807", .expected = 1 },
        .{ .value_type = "i128", .first = "value < 0", .second = "value < -9223372036854775808", .expected = 1 },
        .{ .value_type = "anytype", .first = "value > 0", .second = "value < 1", .expected = 1 },
        .{ .value_type = "i32", .first = "value > 0", .second = "value < 1", .expected = 0 },
        .{ .value_type = "i64", .first = "value > 0", .second = "value < 1", .expected = 0 },
        .{ .value_type = "u32", .first = "value > 0", .second = "value < 1", .expected = 0 },
    };
    const allocator = std.testing.allocator;
    for (cases) |case| {
        for ([_]bool{ false, true }) |with_types| {
            var buffer: [1024]u8 = undefined;
            const code = try std.fmt.bufPrintZ(
                &buffer,
                \\const std = @import("std");
                \\fn check(allocator: std.mem.Allocator, input: {s}) !void {{
                \\    const value = input;
                \\    if ({s}) {{
                \\        if ({s}) {{
                \\            const ptr = try allocator.alloc(u8, 1);
                \\            allocator.free(ptr);
                \\            allocator.free(ptr);
                \\        }}
                \\    }}
                \\}}
            ,
                .{ case.value_type, case.first, case.second },
            );
            var source = Source.init(allocator, "numeric-domain.zig", code);
            defer source.deinit();
            var type_context = TypeContext.init(allocator, &source);
            defer type_context.deinit();
            var diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer {
                for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
                diagnostics.deinit(allocator);
            }

            try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{
                .build_metadata = null,
                .type_context = if (with_types) &type_context else null,
                .analysis_limits = .{ .use_widening = false },
            });
            try std.testing.expectEqual(case.expected, diagnostics.items.len);
            for (diagnostics.items) |diagnostic| {
                try std.testing.expectEqual(@as(usize, 8), diagnostic.range.start.line);
                try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "double-free") != null);
            }
        }
    }
}

test "store_violations_engine reports free without alloc" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn foo(allocator: std.mem.Allocator) void {
        \\    var buf = [_]u8{0};
        \\    var ptr = buf[0..];
        \\    allocator.free(ptr);
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| {
            diag.deinit(allocator);
        }
        diagnostics.deinit(allocator);
    }

    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{ .build_metadata = null, .type_context = &type_ctx });
    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("store-violations-engine", diagnostics.items[0].rule_id);
    try testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "free without tracked allocation") != null);
}

test "store_violations_engine reports use after free" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn foo(allocator: std.mem.Allocator) !void {
        \\    var ptr = try allocator.alloc(u8, 1);
        \\    allocator.free(ptr);
        \\    _ = ptr;
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| {
            diag.deinit(allocator);
        }
        diagnostics.deinit(allocator);
    }

    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{ .build_metadata = null, .type_context = &type_ctx });
    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("store-violations-engine", diagnostics.items[0].rule_id);
    try testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "use after free") != null);
}

test "store_violations_engine reports leak" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn foo(allocator: std.mem.Allocator) !void {
        \\    var ptr = try allocator.alloc(u8, 1);
        \\    _ = ptr;
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| {
            diag.deinit(allocator);
        }
        diagnostics.deinit(allocator);
    }

    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{ .build_metadata = null, .type_context = &type_ctx });
    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("store-violations-engine", diagnostics.items[0].rule_id);
    try testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "resource leak") != null);
}

test "store_violations_engine detects config-driven resource model" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const MyPool = struct {
        \\    fn acquire(_: *const MyPool) i32 { return 42; }
        \\};
        \\fn foo() void {
        \\    const pool = MyPool{};
        \\    const res = pool.acquire();
        \\    // Missing pool.release(res) - should detect as leak based on config model
        \\    _ = res;
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| {
            diag.deinit(allocator);
        }
        diagnostics.deinit(allocator);
    }

    // Create a config with a custom resource model that treats "acquire" as an open
    const cfg = Config{
        .rule_filter = .none,
        .resource_models = &.{
            ResourceModel{ .kind = .open, .method_name = "acquire", .receiver_type = "MyPool" },
        },
    };

    const context = checker_mod.CheckerContext{
        .build_metadata = null,
        .type_context = &type_ctx,
        .config = &cfg,
    };
    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    // Should detect a leak because acquire() is recognized as an open based on config
    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("store-violations-engine", diagnostics.items[0].rule_id);
    try testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "resource leak") != null);
}

test "store_violations_engine detects config-driven fqn model with field access chain" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const MyPool = struct {
        \\    fn acquire(_: *MyPool) i32 { return 42; }
        \\};
        \\const Context = struct {
        \\    pool: MyPool,
        \\};
        \\fn foo() void {
        \\    var ctx = Context{ .pool = MyPool{} };
        \\    const res = ctx.pool.acquire();
        \\    _ = res;
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| {
            diag.deinit(allocator);
        }
        diagnostics.deinit(allocator);
    }

    const cfg = Config{
        .rule_filter = .none,
        .resource_models = &.{
            ResourceModel{ .kind = .open, .fqn = "ctx.pool.acquire" },
        },
    };

    const context = checker_mod.CheckerContext{
        .build_metadata = null,
        .type_context = &type_ctx,
        .config = &cfg,
    };
    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("store-violations-engine", diagnostics.items[0].rule_id);
    try testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "resource leak") != null);
}

/// Helper: run the engine checker and return the number of `defer_frees_escapee`-style
/// diagnostics. Counting the keyword keeps the assertion stable even if other
/// engine checks pick up unrelated issues in a fixture.
fn countEscapeeDiagnostics(allocator: std.mem.Allocator, code: [:0]const u8) !usize {
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| diag.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{
        .build_metadata = null,
        .type_context = &type_ctx,
    });

    var count: usize = 0;
    for (diagnostics.items) |diag| {
        if (std.mem.indexOf(u8, diag.message, "escaped into an outer container") != null) {
            count += 1;
        }
    }
    return count;
}

test "store_violations_engine flags defer-free of slice escaped into outer ArrayList" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Item = struct { text: []const u8 };
        \\fn render(allocator: std.mem.Allocator) !void {
        \\    var run_inputs: std.ArrayList(Item) = .empty;
        \\    defer run_inputs.deinit(allocator);
        \\    if (true) {
        \\        const spaces = try allocator.alloc(u8, 2);
        \\        defer allocator.free(spaces);
        \\        try run_inputs.append(allocator, .{ .text = spaces });
        \\    }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 1), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine ignores defer at function-body scope" {
    // Same-scope defers fire in reverse order, so the container is destroyed
    // before the resource. No UAF, no diagnostic.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Item = struct { text: []const u8 };
        \\fn ok(allocator: std.mem.Allocator) !void {
        \\    var run_inputs: std.ArrayList(Item) = .empty;
        \\    defer run_inputs.deinit(allocator);
        \\    const spaces = try allocator.alloc(u8, 2);
        \\    defer allocator.free(spaces);
        \\    try run_inputs.append(allocator, .{ .text = spaces });
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine flags fn-body defer when container is a parameter" {
    // The container outlives the function, so the defer at function-body scope
    // fires while the caller still holds the appended slice — a real UAF.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Item = struct { text: []const u8 };
        \\fn render(allocator: std.mem.Allocator, sink: *std.ArrayList(Item)) !void {
        \\    const spaces = try allocator.alloc(u8, 2);
        \\    defer allocator.free(spaces);
        \\    try sink.append(allocator, .{ .text = spaces });
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 1), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine ignores escape into container declared in same block" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Item = struct { text: []const u8 };
        \\fn ok(allocator: std.mem.Allocator) !void {
        \\    if (true) {
        \\        var inner: std.ArrayList(Item) = .empty;
        \\        defer inner.deinit(allocator);
        \\        const spaces = try allocator.alloc(u8, 2);
        \\        defer allocator.free(spaces);
        \\        try inner.append(allocator, .{ .text = spaces });
        \\    }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine ignores errdefer ownership-transfer idiom" {
    // errdefer fires only on the error path; on success the container owns the
    // resource. This is the canonical transfer-on-success pattern.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn load(allocator: std.mem.Allocator, src: []const u8, list: *std.ArrayList([]u8)) !void {
        \\    while (true) {
        \\        const path_copy = try allocator.dupe(u8, src);
        \\        errdefer allocator.free(path_copy);
        \\        try list.append(allocator, path_copy);
        \\    }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine flags escape through insertSlice into outer list" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn render(allocator: std.mem.Allocator, list: *std.ArrayList([]const u8)) !void {
        \\    if (true) {
        \\        const value = try allocator.alloc(u8, 2);
        \\        defer allocator.free(value);
        \\        try list.insertSlice(allocator, 0, &.{value});
        \\    }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 1), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine ignores defer free of var never appended" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Item = struct { text: []const u8 };
        \\fn ok(allocator: std.mem.Allocator) !void {
        \\    var run_inputs: std.ArrayList(Item) = .empty;
        \\    defer run_inputs.deinit(allocator);
        \\    if (true) {
        \\        const spaces = try allocator.alloc(u8, 2);
        \\        defer allocator.free(spaces);
        \\        _ = spaces[0];
        \\    }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine ignores appendSlice copy idiom" {
    // appendSlice / appendSliceAssumeCapacity / insertSlice iterate the slice
    // argument and copy each element. A bare slice arg (`appendSlice(out, tmp)`)
    // is consumed during the call; freeing tmp afterwards is safe. Only nested
    // references (e.g. `&.{tmp}`) retain a pointer to the freed memory.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn ok(allocator: std.mem.Allocator, out: *std.ArrayList(u8)) !void {
        \\    if (true) {
        \\        const tmp = try allocator.alloc(u8, 4);
        \\        defer allocator.free(tmp);
        \\        try out.appendSlice(allocator, tmp);
        \\    }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine ignores appendSlice copy from slice expression" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn ok(allocator: std.mem.Allocator, out: *std.ArrayList(u8)) !void {
        \\    if (true) {
        \\        const content = try allocator.alloc(u8, 4);
        \\        defer allocator.free(content);
        \\        try out.appendSlice(allocator, content[1..3]);
        \\    }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 0), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine flags defer-free of slice escaped from switch arm" {
    // The architect-crash shape: a switch arm wraps the alloc + defer + append
    // pattern. Before switch CFG support landed, the engine never visited arm
    // bodies; this test guards that the engine now sees the escape.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Item = struct { text: []const u8 };
        \\const Kind = enum { heading, paragraph };
        \\fn render(allocator: std.mem.Allocator, kind: Kind, indent_spaces: usize) !void {
        \\    var run_inputs: std.ArrayList(Item) = .empty;
        \\    defer run_inputs.deinit(allocator);
        \\    switch (kind) {
        \\        .heading, .paragraph => {
        \\            if (indent_spaces > 0) {
        \\                const spaces = try allocator.alloc(u8, indent_spaces);
        \\                defer allocator.free(spaces);
        \\                try run_inputs.append(allocator, .{ .text = spaces });
        \\            }
        \\        },
        \\    }
        \\}
    ;
    try std.testing.expectEqual(@as(usize, 1), try countEscapeeDiagnostics(std.testing.allocator, code));
}

test "store_violations_engine detects double_free inside switch arm" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Kind = enum { a, b };
        \\fn run(allocator: std.mem.Allocator, k: Kind) !void {
        \\    switch (k) {
        \\        .a => {
        \\            const p = try allocator.alloc(u8, 4);
        \\            allocator.free(p);
        \\            allocator.free(p);
        \\        },
        \\        .b => {},
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| diag.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{
        .build_metadata = null,
        .type_context = &type_ctx,
    });

    var double_free_count: usize = 0;
    for (diagnostics.items) |diag| {
        if (std.mem.indexOf(u8, diag.message, "double-free") != null) double_free_count += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), double_free_count);
}

fn expectStoreDiagnostics(code: [:0]const u8, expected: usize, message_fragment: []const u8) !void {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "skript-regression.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{
        .build_metadata = null,
        .type_context = &type_ctx,
    });
    if (diagnostics.items.len != expected) {
        for (diagnostics.items) |diagnostic| {
            std.debug.print(
                "store diagnostic at {d}:{d}: {s}\n",
                .{
                    diagnostic.range.start.line,
                    diagnostic.range.start.column,
                    diagnostic.message,
                },
            );
        }
    }
    try std.testing.expectEqual(expected, diagnostics.items.len);
    for (diagnostics.items) |diagnostic| {
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, message_fragment) != null);
    }
}

test "skript regression: allocator fields do not imply region ownership" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Context = struct { allocator: std.mem.Allocator };
        \\fn frameView(ctx: *const Context) ![]u8 {
        \\    const first = try std.fmt.allocPrint(ctx.allocator, "{d}", .{1});
        \\    const second = try std.fmt.allocPrint(ctx.allocator, "{s}", .{first});
        \\    return second;
        \\}
        \\fn leaks(allocator: std.mem.Allocator) !void {
        \\    const leaked = try std.fmt.allocPrint(allocator, "{d}", .{1});
        \\    _ = leaked;
        \\}
    ;

    try expectStoreDiagnostics(code, 2, "resource leak");
}

test "skript regression: real error returns remain error paths" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn propagatesError(allocator: std.mem.Allocator) !void {
        \\    const leaked = try std.fmt.allocPrint(allocator, "{d}", .{1});
        \\    const failure = error.Failed;
        \\    _ = leaked;
        \\    return failure;
        \\}
    ;

    try expectStoreDiagnostics(code, 0, "resource leak");
}

test "skript regression: close-like state methods are not resource closes" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Control = struct {
        \\    const File = struct {
        \\        fn close(_: File) void {}
        \\        fn release(_: File) void {}
        \\    };
        \\    fn close(_: *Control) void {}
        \\    fn release(_: *Control) void {}
        \\};
        \\fn cleanup(file: *Control) void {
        \\    file.close();
        \\    file.release();
        \\}
        \\fn cleanupValue(file: Control.File) void {
        \\    file.close();
        \\    file.release();
        \\}
        \\fn unsafeUse(file: std.fs.File) !void {
        \\    file.close();
        \\    _ = try file.stat();
        \\}
    ;

    try expectStoreDiagnostics(code, 1, "use after close");
}
