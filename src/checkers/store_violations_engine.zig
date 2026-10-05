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
const import_resolver = @import("../analysis/import_resolver.zig");
const BuildMetadata = @import("../build_metadata.zig").BuildMetadata;
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

/// Consumer findings for the resource checker, keyed by the shape of the guard
/// around the allocation. The fractional and wide-integer bodies are the ones the
/// consumer reports for issue #21: their numeric domain has no witness the
/// engine's integer lattice can represent, so the state entering the guard's
/// join is identical on both sides of it.
const resource_cases = [_]struct { name: []const u8, code: [:0]const u8, expected: usize, message: []const u8 }{
    .{ .name = "leak under a fractional guard", .expected = 1, .message = "resource leak", .code = 
    \\const std = @import("std");
    \\
    \\fn fractionalLeak(allocator: std.mem.Allocator, input: f64) !void {
    \\    const value = input;
    \\    if (value > 0) {
    \\        if (value < 1) {
    \\            var ptr = try allocator.alloc(u8, 1);
    \\            std.mem.doNotOptimizeAway(ptr.ptr[0..0]);
    \\        }
    \\    }
    \\}
    },
    .{ .name = "double free under a fractional guard", .expected = 1, .message = "double-free", .code = 
    \\const std = @import("std");
    \\
    \\fn fractionalDoubleFree(allocator: std.mem.Allocator, input: f64) void {
    \\    const value = input;
    \\    if (value > 0) {
    \\        if (value < 1) {
    \\            const ptr = allocator.alloc(u8, 1) catch return;
    \\            allocator.free(ptr);
    \\            allocator.free(ptr);
    \\        }
    \\    }
    \\}
    },
    .{ .name = "use after free under a fractional guard", .expected = 1, .message = "use after free", .code = 
    \\const std = @import("std");
    \\
    \\fn fractionalUseAfterFree(allocator: std.mem.Allocator, input: f64) void {
    \\    const value = input;
    \\    if (value > 0) {
    \\        if (value < 1) {
    \\            const ptr = allocator.alloc(u8, 1) catch return;
    \\            allocator.free(ptr);
    \\            std.mem.doNotOptimizeAway(ptr);
    \\        }
    \\    }
    \\}
    },
    .{ .name = "empty integer guard stays silent", .expected = 0, .message = "", .code = 
    \\const std = @import("std");
    \\
    \\fn unreachableDoubleFree(allocator: std.mem.Allocator, input: i32) void {
    \\    const value = input;
    \\    if (value > 0) {
    \\        if (value < 1) {
    \\            const ptr = allocator.alloc(u8, 1) catch return;
    \\            allocator.free(ptr);
    \\            allocator.free(ptr);
    \\        }
    \\    }
    \\}
    \\
    \\fn unreachableUseAfterFree(allocator: std.mem.Allocator, input: i32) void {
    \\    const value = input;
    \\    if (value > 0) {
    \\        if (value < 1) {
    \\            const ptr = allocator.alloc(u8, 1) catch return;
    \\            allocator.free(ptr);
    \\            std.mem.doNotOptimizeAway(ptr);
    \\        }
    \\    }
    \\}
    \\
    \\fn unreachableLeak(allocator: std.mem.Allocator, input: i32) !void {
    \\    const value = input;
    \\    if (value > 0) {
    \\        if (value < 1) {
    \\            var ptr = try allocator.alloc(u8, 1);
    \\            std.mem.doNotOptimizeAway(ptr.ptr[0..0]);
    \\        }
    \\    }
    \\}
    },
    .{ .name = "leak under a wide unsigned guard", .expected = 1, .message = "resource leak", .code = 
    \\const std = @import("std");
    \\
    \\fn wideUnsignedLeak(allocator: std.mem.Allocator, input: u64) !void {
    \\    const value = input;
    \\    if (value > 0) {
    \\        if (value > 9223372036854775807) {
    \\            var ptr = try allocator.alloc(u8, 1);
    \\            std.mem.doNotOptimizeAway(ptr.ptr[0..0]);
    \\        }
    \\    }
    \\}
    },
    .{ .name = "leak under a wide signed guard", .expected = 1, .message = "resource leak", .code = 
    \\const std = @import("std");
    \\
    \\fn wideSignedLeak(allocator: std.mem.Allocator, input: i128) !void {
    \\    const value = input;
    \\    if (value < 0) {
    \\        if (value < -9223372036854775808) {
    \\            var ptr = try allocator.alloc(u8, 1);
    \\            std.mem.doNotOptimizeAway(ptr.ptr[0..0]);
    \\        }
    \\    }
    \\}
    },
    .{ .name = "leak across an inlined call", .expected = 1, .message = "resource leak", .code = 
    \\const std = @import("std");
    \\
    \\fn leakyHelper(allocator: std.mem.Allocator, size: usize) void {
    \\    const ptr = allocator.alloc(u8, size) catch return;
    \\    _ = ptr;
    \\}
    \\
    \\fn caller(allocator: std.mem.Allocator) void {
    \\    leakyHelper(allocator, 10,);
    \\}
    },
    .{ .name = "unconditional leak", .expected = 1, .message = "resource leak", .code = 
    \\const std = @import("std");
    \\
    \\fn straightLineLeak(allocator: std.mem.Allocator) !void {
    \\    var ptr = try allocator.alloc(u8, 1);
    \\    std.mem.doNotOptimizeAway(ptr.ptr[0..0]);
    \\}
    },
    // The loop comes first and the join after it: a leak is read off the state
    // that reaches the function exit, so a loop downstream of the join would
    // merge the arms at its own header and hide what this case is about. One arm
    // holds an allocation and one holds nothing, so widening the join turns the
    // held resource into `unknown` and the leak on the holding arm is lost.
    .{ .name = "leak at a join after a loop", .expected = 1, .message = "resource leak", .code = 
    \\const std = @import("std");
    \\
    \\fn leakPastLoop(allocator: std.mem.Allocator, flag: bool) !void {
    \\    var i: usize = 0;
    \\    while (i < 4) : (i += 1) {
    \\        i += 1;
    \\    }
    \\    if (flag) {
    \\        var ptr = try allocator.alloc(u8, 1);
    \\        std.mem.doNotOptimizeAway(ptr.ptr[0..0]);
    \\    }
    \\}
    },
};

test "store_violations_engine findings survive the CLI widening default" {
    // The CLI turns widening on; the fixtures pin the widened-off behaviour.
    // Both must agree. A leak is read off the state that reaches the function
    // exit, so a join that widens (turning a held resource into `unknown`) or
    // that subsumes the state holding it away both erase it.
    const testing = std.testing;
    const allocator = testing.allocator;

    for (resource_cases) |case| {
        for ([_]bool{ false, true }) |with_types| {
            var narrow = Source.init(allocator, "resource-widening.zig", case.code);
            defer narrow.deinit();
            var narrow_types = TypeContext.init(allocator, &narrow);
            defer narrow_types.deinit();
            var narrow_diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer narrow_diagnostics.deinit(allocator);
            defer for (narrow_diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);

            var wide = Source.init(allocator, "resource-widening.zig", case.code);
            defer wide.deinit();
            var wide_types = TypeContext.init(allocator, &wide);
            defer wide_types.deinit();
            var wide_diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer wide_diagnostics.deinit(allocator);
            defer for (wide_diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);

            try StoreViolationsEngineChecker.checker.checkAst(&narrow, allocator, &narrow_diagnostics, .{
                .build_metadata = null,
                .type_context = if (with_types) &narrow_types else null,
                .analysis_limits = .{ .use_widening = false },
            });
            try StoreViolationsEngineChecker.checker.checkAst(&wide, allocator, &wide_diagnostics, .{
                .build_metadata = null,
                .type_context = if (with_types) &wide_types else null,
                .analysis_limits = .{ .use_widening = true },
            });

            const narrow_items = narrow_diagnostics.items;
            try testing.expectEqual(case.expected, narrow_items.len);
            for (narrow_items) |diagnostic| {
                try testing.expectEqualStrings("store-violations-engine", diagnostic.rule_id);
                try testing.expectEqual(checker_mod.Severity.err, diagnostic.severity);
                try testing.expect(std.mem.indexOf(u8, diagnostic.message, case.message) != null);
            }

            try testing.expectEqual(narrow_items.len, wide_diagnostics.items.len);
            for (narrow_items, wide_diagnostics.items) |expected, actual| {
                try testing.expectEqualStrings(expected.file_path, actual.file_path);
                try testing.expectEqualStrings(expected.rule_id, actual.rule_id);
                try testing.expectEqualStrings(expected.message, actual.message);
                try testing.expectEqual(expected.severity, actual.severity);
                try testing.expectEqual(expected.range, actual.range);
                try testing.expectEqual(expected.related_range, actual.related_range);
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

test "a wrapper proven to close its argument releases the caller's resource" {
    const testing = std.testing;
    const allocator = testing.allocator;
    // `compat.closeDir` re-exports a helper whose body closes the directory it
    // is handed. `compat.nextDir` takes the same `*Directory` and only reads
    // it, `closeDirFake` closes a look-alike on a different field, and
    // `closeSometimes` closes behind a branch: none of those is a release, so
    // the proof has to come from the body, never from the name.
    const io_code: [:0]const u8 =
        \\const std = @import("std");
        \\pub const Context = struct {};
        \\pub const Handle = struct {
        \\    raw: std.posix.fd_t,
        \\    fn close(_: *Handle) void {}
        \\};
        \\pub const Directory = struct {
        \\    handle: std.fs.File,
        \\    other: Handle,
        \\};
        \\pub fn openDir(_: *Context, path: []const u8) !Directory {
        \\    _ = path;
        \\    return .{ .handle = undefined };
        \\}
        \\pub fn closeDir(_: *Context, directory: *Directory) void {
        \\    directory.handle.close();
        \\}
        \\pub fn nextDir(_: *Context, directory: *Directory) !u32 {
        \\    _ = directory;
        \\    return 0;
        \\}
        \\pub fn closeDirFake(_: *Context, directory: *Directory) void {
        \\    directory.other.close();
        \\}
        \\pub fn closeSometimes(_: *Context, directory: *Directory, flag: bool) void {
        \\    if (flag) directory.handle.close();
        \\}
        \\pub const Pair = struct {
        \\    primary: std.fs.File,
        \\    secondary: std.fs.File,
        \\};
        \\pub fn openPair(_: *Context, path: []const u8) !Pair {
        \\    _ = path;
        \\    return .{ .primary = undefined, .secondary = undefined };
        \\}
        \\pub fn closeSecondary(_: *Context, pair: *Pair) void {
        \\    pair.secondary.close();
        \\}
    ;
    const app_code: [:0]const u8 =
        \\const std = @import("std");
        \\const compat = @import("io.zig");
        \\fn released(ctx: *compat.Context) !void {
        \\    var directory = try compat.openDir(ctx, "p");
        \\    defer compat.closeDir(ctx, &directory);
        \\    _ = &directory;
        \\}
        \\fn iterated(ctx: *compat.Context) !void {
        \\    var directory = try compat.openDir(ctx, "p");
        \\    defer compat.nextDir(ctx, &directory);
        \\    _ = &directory;
        \\}
        \\fn leaked(ctx: *compat.Context) !void {
        \\    var directory = try compat.openDir(ctx, "p");
        \\    _ = &directory;
        \\}
        \\fn wrongTarget(ctx: *compat.Context) !void {
        \\    var other = try compat.openDir(ctx, "other");
        \\    var directory = try compat.openDir(ctx, "p");
        \\    defer compat.closeDir(ctx, &other);
        \\    _ = &directory;
        \\    _ = &other;
        \\}
        \\fn fakedRelease(ctx: *compat.Context) !void {
        \\    var directory = try compat.openDir(ctx, "p");
        \\    defer compat.closeDirFake(ctx, &directory);
        \\    _ = &directory;
        \\}
        \\fn conditionalRelease(ctx: *compat.Context, flag: bool) !void {
        \\    var directory = try compat.openDir(ctx, "p");
        \\    defer compat.closeSometimes(ctx, &directory, flag);
        \\    _ = &directory;
        \\}
        \\fn wrongResourceField(ctx: *compat.Context) !void {
        \\    var pair = try compat.openPair(ctx, "p");
        \\    defer compat.closeSecondary(ctx, &pair);
        \\    _ = &pair;
        \\}
    ;

    var io_source = Source.init(allocator, "io.zig", io_code);
    defer io_source.deinit();
    var app_source = Source.init(allocator, "app.zig", app_code);
    defer app_source.deinit();
    var type_ctx = TypeContext.init(allocator, &app_source);
    defer type_ctx.deinit();

    const files = [_]import_resolver.File{
        .{ .path = io_source.getFilePath(), .tree = try io_source.ast() },
        .{ .path = app_source.getFilePath(), .tree = try app_source.ast() },
    };
    type_ctx.project_resolver = .{ .files = &files, .file_index = 1 };

    const cfg = Config{
        .rule_filter = .none,
        .resource_models = &.{
            ResourceModel{ .kind = .open, .method_name = "openDir" },
            ResourceModel{ .kind = .open, .method_name = "openPair" },
        },
    };

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diag| diag.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try StoreViolationsEngineChecker.checker.checkAst(&app_source, allocator, &diagnostics, .{
        .build_metadata = null,
        .type_context = &type_ctx,
        .config = &cfg,
    });

    // Only `released` releases. Every other call site keeps its leak:
    // `iterated` (nextDir reads only), `fakedRelease` (close on a look-alike
    // field), `conditionalRelease` (close behind a branch),
    // `wrongResourceField` (a wrapper carrying two genuine resource fields
    // closes the wrong one), `leaked` (no release at all) and `wrongTarget`
    // (release of a different variable).
    var leaks: usize = 0;
    for (diagnostics.items) |diag| {
        if (std.mem.indexOf(u8, diag.message, "resource leak") != null) leaks += 1;
    }
    try testing.expectEqual(@as(usize, 6), leaks);
    try testing.expectEqual(@as(usize, 6), diagnostics.items.len);
}

test "with its declared resource models the CLI-shaped path pins the same findings as the fixture gate" {
    // The fixture gate hands the checker a bare type context, no project and
    // no build metadata, and leaves widening off. The CLI hands it a resolved
    // compilation root, project metadata and widening on, and a callee the
    // wider resolution can now inline. A finding only the narrow path produces
    // is one the shipped binary never reports, so both shapes run here through
    // the wider context instead.
    //
    // These fixtures declare their resource models in an inline `// CONFIG:`
    // line that the fixture gate parses. The CLI does not read that line: it is
    // configured from a config file, so the parity check here supplies the same
    // models through the context the way a CLI run configured with them does.
    const testing = std.testing;
    const allocator = testing.allocator;
    const metadata = BuildMetadata.init(.{ .arch = .x86_64, .os = .linux, .abi = null }, .release_fast);

    // Both sources are the fixture verbatim, so the pinned line is the line the
    // fixture pins, and each case carries the models its own `// CONFIG:` line
    // declares.
    const cases = [_]struct {
        path: []const u8,
        code: [:0]const u8,
        models: []const ResourceModel,
        line: usize,
        message: []const u8,
    }{
        .{
            .path = "errdefer-over-free-owned-release.zig",
            .code =
            \\const std = @import("std");
            \\
            \\const ThreadContext = struct {
            \\    allocator: std.mem.Allocator,
            \\    url: []u8,
            \\
            \\    pub fn deinit(self: *ThreadContext) void {
            \\        self.allocator.free(self.url);
            \\    }
            \\};
            \\
            \\fn foo(allocator: std.mem.Allocator, url: []const u8) !void {
            \\    const ctx = allocator.create(ThreadContext) catch return error.OutOfMemory;
            \\    errdefer allocator.destroy(ctx);
            \\
            \\    ctx.allocator = allocator;
            \\    ctx.url = allocator.dupe(u8, url) catch return error.OutOfMemory;
            \\    errdefer allocator.free(ctx.url);
            \\
            \\    ctx.deinit();
            \\    return error.OutOfMemory;
            \\}
            ,
            .models = &.{.{ .kind = .free_owned, .method_name = "deinit" }},
            .line = 18,
            .message = "double-free",
        },
        .{
            .path = "acquisition-through-field-access-receiver.zig",
            .code =
            \\const std = @import("std");
            \\// zwanzig-disable: unused-decl
            \\
            \\const MyPool = struct {
            \\    fn acquire(_: *MyPool) i32 {
            \\        return 1;
            \\    }
            \\};
            \\
            \\const Context = struct {
            \\    pool: MyPool,
            \\};
            \\
            \\fn leakFromFieldAccess() void {
            \\    var ctx = Context{ .pool = MyPool{} };
            \\    const handle = ctx.pool.acquire();
            \\    _ = handle;
            \\}
            ,
            .models = &.{.{ .kind = .open, .method_name = "acquire", .receiver_type = "MyPool" }},
            .line = 16,
            .message = "resource leak",
        },
    };

    for (cases) |case| {
        var source = Source.init(allocator, case.path, case.code);
        defer source.deinit();
        var types = TypeContext.init(allocator, &source);
        defer types.deinit();
        const files = [_]import_resolver.File{.{ .path = source.getFilePath(), .tree = try source.ast() }};
        types.project_resolver = .{ .files = &files, .file_index = 0 };

        const config: Config = .{ .rule_filter = .none, .resource_models = case.models };
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{
            .build_metadata = &metadata,
            .type_context = &types,
            .config = &config,
            .analysis_limits = .{ .use_widening = true },
        });

        try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
        try testing.expectEqualStrings("store-violations-engine", diagnostics.items[0].rule_id);
        try testing.expectEqual(checker_mod.Severity.err, diagnostics.items[0].severity);
        try testing.expectEqual(case.line, diagnostics.items[0].range.start.line);
        try testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, case.message) != null);
    }
}

test "a returned aggregate carries the payload resources it holds" {
    // Each case runs as its own Source. Combined into one file the
    // field-allocated resources all report against the same out-of-range
    // token, so the checker folds them into a single diagnostic and one
    // unsafe case could hide behind another.
    // Kept as a string-literal pointer, not a slice, so `++` below stays a
    // compile-time concatenation and each case ends up sentinel-terminated.
    const model_type =
        \\const std = @import("std");
        \\const ResourceModel = struct {
        \\    kind: u8,
        \\    method_name: ?[]const u8 = null,
        \\    receiver_type: ?[]const u8 = null,
        \\    return_type: ?[]const u8 = null,
        \\};
    ;

    // Proven shape: the store is the penultimate statement of the loop body,
    // the last statement is `valid_count += 1`, both bindings are declared
    // outside the loop, and nothing else writes the cursor or reaches the
    // aggregate, so the resources travel with the returned aggregate.
    const proven_shape = model_type ++
        \\fn parseResourceModels(allocator: std.mem.Allocator, n: usize) ![]ResourceModel {
        \\    var models = try allocator.alloc(ResourceModel, n);
        \\    var valid_count: usize = 0;
        \\    errdefer allocator.free(models);
        \\    for (0..n) |_| {
        \\        var model = ResourceModel{ .kind = 0 };
        \\        model.method_name = try allocator.dupe(u8, "method");
        \\        model.receiver_type = try allocator.dupe(u8, "receiver");
        \\        model.return_type = try allocator.dupe(u8, "return");
        \\        models[valid_count] = model;
        \\        valid_count += 1;
        \\    }
        \\    return models;
        \\}
    ;
    try expectStoreDiagnostics(proven_shape, 0, "resource leak");

    // A cursor that advances by zero lands on the same element every pass.
    const zero_step_cursor = model_type ++
        \\fn zeroStepCursor(allocator: std.mem.Allocator, n: usize) ![]ResourceModel {
        \\    var models = try allocator.alloc(ResourceModel, n);
        \\    var slot: usize = 0;
        \\    for (0..n) |_| {
        \\        var model = ResourceModel{ .kind = 0 };
        \\        model.method_name = try allocator.dupe(u8, "method");
        \\        models[slot] = model;
        \\        slot += 0;
        \\    }
        \\    return models;
        \\}
    ;
    try expectStoreDiagnostics(zero_step_cursor, 1, "resource leak");

    // A constant cursor is one store site that repeats the same element.
    const const_index_loop = model_type ++
        \\fn constIndexLoop(allocator: std.mem.Allocator, n: usize) ![]ResourceModel {
        \\    var models = try allocator.alloc(ResourceModel, n);
        \\    const slot: usize = 0;
        \\    for (0..n) |_| {
        \\        var model = ResourceModel{ .kind = 0 };
        \\        model.method_name = try allocator.dupe(u8, "method");
        \\        models[slot] = model;
        \\    }
        \\    return models;
        \\}
    ;
    try expectStoreDiagnostics(const_index_loop, 1, "resource leak");

    // A field write through the aggregate after the store drops the payload.
    const overwrite_after_store = model_type ++
        \\fn overwriteAfterStore(allocator: std.mem.Allocator) ![]ResourceModel {
        \\    var models = try allocator.alloc(ResourceModel, 2);
        \\    var slot: usize = 0;
        \\    var model = ResourceModel{ .kind = 0 };
        \\    model.method_name = try allocator.dupe(u8, "method");
        \\    models[slot] = model;
        \\    models[slot].method_name = null;
        \\    return models;
        \\}
    ;
    try expectStoreDiagnostics(overwrite_after_store, 1, "resource leak");

    // A whole-place reassignment of the aggregate drops the payload too.
    const whole_overwrite = model_type ++
        \\fn wholeOverwrite(allocator: std.mem.Allocator) ![]ResourceModel {
        \\    var models = try allocator.alloc(ResourceModel, 2);
        \\    var slot: usize = 0;
        \\    var model = ResourceModel{ .kind = 0 };
        \\    model.method_name = try allocator.dupe(u8, "method");
        \\    models[slot] = model;
        \\    models = try allocator.alloc(ResourceModel, 2);
        \\    return models;
        \\}
    ;
    try expectStoreDiagnostics(whole_overwrite, 1, "resource leak");

    // A payload that never reaches an aggregate is never handed over.
    const dropped_payload = model_type ++
        \\fn dropResourceModels(allocator: std.mem.Allocator) !usize {
        \\    var model = ResourceModel{ .kind = 0 };
        \\    model.method_name = try allocator.dupe(u8, "method");
        \\    _ = &model;
        \\    return 0;
        \\}
    ;
    try expectStoreDiagnostics(dropped_payload, 1, "resource leak");
}

test "an arena binding written over before an allocation owns nothing on the project path" {
    // The source the `undischarged_local_arena_leaks` fixture pins, run with a
    // project file list attached - the shape a project run hands the type
    // context and a bare fixture never does. With a resolver in place the
    // declared type of `arena` resolves, and a declared type is what the
    // binding was declared with: it says nothing about the value the binding
    // holds after the write below it. So the second frame's `deinit` disposes
    // the arena the write put there, while the constructor the binding was
    // declared with proves nothing about the value the allocation runs
    // through, and the block stays the frame's own.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\
        \\const verified_std = @import("std");
        \\
        \\fn undrainedArenaLeaks(gpa: std.mem.Allocator) !void {
        \\    var arena = verified_std.heap.ArenaAllocator.init(gpa);
        \\    const allocator = arena.allocator();
        \\    const buf = try allocator.alloc(u8, 8);
        \\    buf[0] = 'a';
        \\}
        \\
        \\fn reassignedArenaProvesNothing(gpa: std.mem.Allocator) !void {
        \\    var arena = verified_std.heap.ArenaAllocator.init(gpa);
        \\    defer arena.deinit();
        \\    arena = verified_std.heap.ArenaAllocator.init(gpa);
        \\    const allocator = arena.allocator();
        \\    const buf = try allocator.alloc(u8, 8);
        \\    buf[0] = 'b';
        \\}
    ;

    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "arena-reassigned.zig", code);
    defer source.deinit();
    var type_ctx = TypeContext.init(allocator, &source);
    defer type_ctx.deinit();

    const files = [_]import_resolver.File{
        .{ .path = source.getFilePath(), .tree = try source.ast() },
    };
    type_ctx.project_resolver = .{ .files = &files, .file_index = 0 };

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try StoreViolationsEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{
        .build_metadata = null,
        .type_context = &type_ctx,
    });

    // Both frames keep the block they made: the one that disposes nothing,
    // and the one whose disposal covers only the arena its own write put in
    // place. The lines below are the two allocations of the source above.
    const pinned = [_]usize{ 8, 17 };
    var lines: [pinned.len]usize = undefined;
    for (diagnostics.items, 0..) |diagnostic, index| {
        try std.testing.expect(index < lines.len);
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "resource leak") != null);
        lines[index] = diagnostic.range.start.line;
    }
    try std.testing.expectEqual(lines.len, diagnostics.items.len);
    for (lines) |line| {
        var found = false;
        for (pinned) |expected| {
            if (line == expected) found = true;
        }
        try std.testing.expect(found);
    }
}
