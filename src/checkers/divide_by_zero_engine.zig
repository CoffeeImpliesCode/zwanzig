const std = @import("std");
const checker_mod = @import("../checker.zig");
const Checker = checker_mod.Checker;
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const Source = @import("../source.zig").Source;
const TypeContext = @import("../type_context.zig").TypeContext;
const ids = @import("../ids.zig");
const engine_mod = @import("../engine.zig");
const scan = @import("divide_by_zero/scan.zig");
const OptionalUnwrapEngineChecker = @import("optional_unwrap_engine.zig").OptionalUnwrapEngineChecker;
const StoreViolationsEngineChecker = @import("store_violations_engine.zig").StoreViolationsEngineChecker;
const SliceBoundsEngineChecker = @import("slice_bounds_engine.zig").SliceBoundsEngineChecker;

pub const DivideByZeroEngineChecker = struct {
    pub const checker: Checker = .{
        .name = "divide-by-zero-engine",
        .default_severity = .err,
        .type_requirement = .optional,
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

        var reported: std.AutoHashMap(u32, void) = std.AutoHashMap(u32, void).init(allocator);
        defer reported.deinit();

        for (0..tags.len) |i| {
            if (tags[i] == .fn_decl or tags[i] == .test_decl) {
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
        reported: *std.AutoHashMap(u32, void),
    ) CheckerError!void {
        var cfg_handle = (context.getOrBuildCfg(allocator, src, fn_node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.InvalidAst => return,
        }) orelse return;
        defer cfg_handle.deinit();

        var analysis = try context.getOrAnalyze(allocator, src, &cfg_handle, checker.name, .configured);
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

        if (!analysis.complete) return;

        const tree = try src.ast();
        try scan.scanForZeroDivisors(src, allocator, diagnostics, tree, engine, cfg_handle.cfg, fn_node, reported);
    }
};

const DivisorExpectation = enum { none, definite, possible };

/// Consumer findings for a divide-by-zero site, keyed by the branch shape of the
/// denominator. Every entry is a fixture body verbatim, so the expectation here
/// and the pinned fixture expectation cannot drift apart.
const divisor_cases = [_]struct { name: []const u8, code: [:0]const u8, expectation: DivisorExpectation }{
    .{ .name = "branch may reach zero", .expectation = .possible, .code = 
    \\pub fn warn(flag: bool) i32 {
    \\    var d: i32 = 2;
    \\    if (flag) {
    \\        d = 0;
    \\    }
    \\    return @divTrunc(20, d);
    \\}
    },
    .{ .name = "shifted range may reach zero", .expectation = .possible, .code = 
    \\pub fn warn(flag: bool) i32 {
    \\    var x: i32 = 0;
    \\    if (flag) {
    \\        x = -1;
    \\    }
    \\    return @divTrunc(10, x + 1);
    \\}
    },
    // The join sits in front of a loop, so a widening rule that treats "can reach
    // a loop" as "is in a loop" merges the arms here and loses the zero path. The
    // division is between the join and the loop, so the loop header never gets
    // to merge the arms either: what the checker reads is decided by the join.
    .{ .name = "branch join in front of a loop", .expectation = .possible, .code = 
    \\pub fn warn(flag: bool) i32 {
    \\    var d: i32 = 2;
    \\    if (flag) {
    \\        d = 0;
    \\    }
    \\    const first = @divTrunc(20, d);
    \\    var i: i32 = 0;
    \\    while (i < 4) : (i += 1) {
    \\        i += 1;
    \\    }
    \\    return first;
    \\}
    },
    .{ .name = "literal zero", .expectation = .definite, .code = 
    \\pub fn bad() i32 {
    \\    return @divTrunc(10, 0);
    \\}
    },
    .{ .name = "guard keeps it non-zero", .expectation = .none, .code = 
    \\pub fn ok(x: i32) i32 {
    \\    if (x != 0) {
    \\        return @divTrunc(10, x);
    \\    }
    \\    return 0;
    \\}
    },
    .{ .name = "float denominator", .expectation = .none, .code = 
    \\pub fn ok() f64 {
    \\    var denominator: f64 = 0;
    \\    denominator += 1;
    \\    return 1.0 / denominator;
    \\}
    },
};

test "divide_by_zero_engine findings survive the CLI widening default" {
    // The CLI turns widening on; the fixtures pin the widened-off behaviour.
    // Both must agree. A denominator that is zero on only one path is decided by
    // the states kept at the branch join, so widening that join collapses the
    // per-path denominators into a single `unknown` and the warning is lost.
    const testing = std.testing;
    const allocator = testing.allocator;

    for (divisor_cases) |case| {
        for ([_]bool{ false, true }) |with_types| {
            var narrow = Source.init(allocator, "divisor-widening.zig", case.code);
            defer narrow.deinit();
            var narrow_types = TypeContext.init(allocator, &narrow);
            defer narrow_types.deinit();
            var narrow_diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer narrow_diagnostics.deinit(allocator);
            defer for (narrow_diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);

            var wide = Source.init(allocator, "divisor-widening.zig", case.code);
            defer wide.deinit();
            var wide_types = TypeContext.init(allocator, &wide);
            defer wide_types.deinit();
            var wide_diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer wide_diagnostics.deinit(allocator);
            defer for (wide_diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);

            try DivideByZeroEngineChecker.checker.checkAst(&narrow, allocator, &narrow_diagnostics, .{
                .build_metadata = null,
                .type_context = if (with_types) &narrow_types else null,
                .analysis_limits = .{ .use_widening = false },
            });
            try DivideByZeroEngineChecker.checker.checkAst(&wide, allocator, &wide_diagnostics, .{
                .build_metadata = null,
                .type_context = if (with_types) &wide_types else null,
                .analysis_limits = .{ .use_widening = true },
            });

            const narrow_items = narrow_diagnostics.items;
            switch (case.expectation) {
                .none => try testing.expectEqual(@as(usize, 0), narrow_items.len),
                .definite => {
                    try testing.expectEqual(@as(usize, 1), narrow_items.len);
                    try testing.expectEqual(checker_mod.Severity.err, narrow_items[0].severity);
                    try testing.expectEqualStrings("division by zero can panic at runtime", narrow_items[0].message);
                },
                .possible => {
                    try testing.expectEqual(@as(usize, 1), narrow_items.len);
                    try testing.expectEqual(checker_mod.Severity.warning, narrow_items[0].severity);
                    try testing.expectEqualStrings("possible division by zero can panic at runtime", narrow_items[0].message);
                },
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

test "labeled break unwinds defers through a deep scope chain" {
    // The labeled break crosses seventy nested scopes to reach the defer that
    // owns the zero. Scope tracking borrows the caller's frames, so depth costs
    // nothing and the write survives; an analyzer that keeps only a bounded
    // prefix of scopes drops the innermost defer, and the division after the
    // block then keeps seeing the pre-block value and reads as safe.

    const testing = std.testing;
    const allocator = testing.allocator;

    const depth = 70;
    var code_buf: std.ArrayList(u8) = .empty;
    defer code_buf.deinit(allocator);
    try code_buf.appendSlice(allocator,
        \\pub fn deep() i64 {
        \\    var denominator: i64 = 3;
        \\    outer: {
        \\
    );
    for (0..depth) |_| try code_buf.appendSlice(allocator, "        {\n");
    try code_buf.appendSlice(allocator,
        \\            defer denominator = 0;
        \\            break :outer;
        \\
    );
    for (0..depth) |_| try code_buf.appendSlice(allocator, "        }\n");
    try code_buf.appendSlice(allocator,
        \\    }
        \\    return @divTrunc(1, denominator);
        \\}
        \\
    );
    const code = try code_buf.toOwnedSliceSentinel(allocator, 0);
    defer allocator.free(code);

    var source = Source.init(allocator, "deep-scope-chain.zig", code);
    defer source.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try DivideByZeroEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{ .build_metadata = null });

    // Lines: three header lines, `depth` openings, the defer and the break,
    // `depth` closings, the outer block's own close, then the division.
    const division_line: usize = 3 + 2 * depth + 4;
    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqual(checker_mod.Severity.err, diagnostics.items[0].severity);
    try testing.expectEqual(division_line, diagnostics.items[0].range.start.line);
    try testing.expectEqualStrings("division by zero can panic at runtime", diagnostics.items[0].message);
}

test "configured checker leases preserve standalone diagnostics" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const checkers = [_]*const Checker{
        &OptionalUnwrapEngineChecker.checker,
        &StoreViolationsEngineChecker.checker,
        &DivideByZeroEngineChecker.checker,
        &SliceBoundsEngineChecker.checker,
    };
    const expected_lines = [_]usize{ 7, 6, 8, 10 };
    const code: [:0]const u8 =
        \\extern fn acquire() usize;
        \\extern fn release(handle: usize) void;
        \\fn hazards(value: ?u8) void {
        \\    const handle = acquire();
        \\    release(handle);
        \\    release(handle);
        \\    _ = value.?;
        \\    _ = @divTrunc(10, 0);
        \\    const items = [_]u8{ 1, 2, 3 };
        \\    _ = items[5];
        \\}
    ;

    // Check type-free fallback and typed scans against cold and reused leases.
    for ([_]bool{ false, true }) |with_types| {
        var source = Source.init(allocator, "checker-leases.zig", code);
        defer source.deinit();
        var types = checker_mod.TypeContext.init(allocator, &source);
        defer types.deinit();
        const config: checker_mod.Config = .{
            .rule_filter = .none,
            .resource_models = &.{
                .{ .kind = .alloc, .method_name = "acquire" },
                .{ .kind = .free, .method_name = "release" },
            },
        };
        var artifacts = checker_mod.CachedArtifacts.init(allocator);
        defer artifacts.deinit();
        var cache = checker_mod.AnalysisCache.init(allocator);
        defer cache.deinit();

        for ([_]?usize{ null, 0 }) |max_steps| {
            const context: checker_mod.CheckerContext = .{
                .build_metadata = null,
                .type_context = if (with_types) &types else null,
                .config = &config,
                .analysis_limits = .{ .max_worklist_steps = max_steps },
            };
            var standalone = checker_mod.AnalysisResult.init();
            defer standalone.deinit(allocator);
            for (checkers, expected_lines, 0..) |checker, expected_line, index| {
                try checker.checkAst(&source, allocator, &standalone.diagnostics, context);
                if (max_steps == null) {
                    try testing.expectEqual(index + 1, standalone.diagnostics.items.len);
                    const diagnostic = standalone.diagnostics.items[index];
                    try testing.expectEqualStrings(checker.name, diagnostic.rule_id);
                    try testing.expectEqual(expected_line, diagnostic.range.start.line);
                } else {
                    try testing.expectEqual(@as(usize, 0), standalone.diagnostics.items.len);
                }
            }

            for (0..2) |pass| {
                var shared = checker_mod.AnalysisResult.init();
                defer shared.deinit(allocator);
                var shared_context = context;
                shared_context.cached_artifacts = &artifacts;
                shared_context.analysis_cache = &cache;
                shared_context.analysis_stats = &shared.stats;
                for (checkers) |checker| {
                    try checker.checkAst(&source, allocator, &shared.diagnostics, shared_context);
                }
                try testing.expectEqual(standalone.diagnostics.items.len, shared.diagnostics.items.len);
                for (standalone.diagnostics.items, shared.diagnostics.items) |expected, actual| {
                    try testing.expectEqualStrings(expected.file_path, actual.file_path);
                    try testing.expectEqualStrings(expected.rule_id, actual.rule_id);
                    try testing.expectEqualStrings(expected.message, actual.message);
                    try testing.expectEqual(expected.severity, actual.severity);
                    try testing.expectEqual(expected.range, actual.range);
                    try testing.expectEqual(expected.related_range, actual.related_range);
                }
                try testing.expectEqual(@as(u64, if (pass == 0) 1 else 0), shared.stats.total_runs);
            }
        }
    }
}

test "numeric checkers propagate AST allocation failures" {
    const Harness = struct {
        fn run(allocator: std.mem.Allocator, checker: *const Checker) !void {
            var source = Source.init(allocator, "numeric-ast-oom.zig", "fn foo() void {}");
            defer source.deinit();
            var result = checker_mod.AnalysisResult.init();
            defer result.deinit(std.testing.allocator);

            try checker.checkAst(&source, std.testing.allocator, &result.diagnostics, .{
                .build_metadata = null,
            });
            try std.testing.expectEqual(@as(usize, 0), result.diagnostics.items.len);
        }
    };
    const checkers = [_]*const Checker{
        &DivideByZeroEngineChecker.checker,
        &SliceBoundsEngineChecker.checker,
    };
    for (checkers) |checker| {
        try std.testing.checkAllAllocationFailures(std.testing.allocator, Harness.run, .{checker});
    }
}

test "numeric checkers propagate CFG allocation failures" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const checkers = [_]*const Checker{
        &DivideByZeroEngineChecker.checker,
        &SliceBoundsEngineChecker.checker,
    };
    var source = Source.init(allocator, "numeric-cfg-oom.zig", "fn foo() void {}");
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = ids.astId(@intFromEnum(tree.rootDecls()[0]));

    for ([_]bool{ false, true }) |shared| {
        // Limit failure injection to CFG creation, before analysis allocations.
        var baseline = testing.FailingAllocator.init(allocator, .{});
        {
            var artifacts = checker_mod.CachedArtifacts.init(baseline.allocator());
            defer artifacts.deinit();
            const context: checker_mod.CheckerContext = .{
                .build_metadata = null,
                .cached_artifacts = if (shared) &artifacts else null,
            };
            var cfg = (try context.getOrBuildCfg(baseline.allocator(), &source, fn_node)) orelse
                return error.TestUnexpectedResult;
            defer cfg.deinit();
        }
        try testing.expectEqual(baseline.allocated_bytes, baseline.freed_bytes);

        for (checkers) |checker| {
            for (0..baseline.alloc_index) |fail_index| {
                var failing = testing.FailingAllocator.init(allocator, .{ .fail_index = fail_index });
                {
                    var artifacts = checker_mod.CachedArtifacts.init(failing.allocator());
                    defer artifacts.deinit();
                    const context: checker_mod.CheckerContext = .{
                        .build_metadata = null,
                        .cached_artifacts = if (shared) &artifacts else null,
                    };
                    const checker_allocator = if (shared) allocator else failing.allocator();
                    var result = checker_mod.AnalysisResult.init();
                    defer result.deinit(checker_allocator);
                    try testing.expectError(error.OutOfMemory, checker.checkAst(
                        &source,
                        checker_allocator,
                        &result.diagnostics,
                        context,
                    ));
                    try testing.expectEqual(@as(usize, 0), result.diagnostics.items.len);
                }
                try testing.expectEqual(failing.allocated_bytes, failing.freed_bytes);
            }
        }
    }
}

test "configured checker leases propagate analysis allocation failures" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const checkers = [_]*const Checker{
        &OptionalUnwrapEngineChecker.checker,
        &StoreViolationsEngineChecker.checker,
        &DivideByZeroEngineChecker.checker,
        &SliceBoundsEngineChecker.checker,
    };
    var source = Source.init(allocator, "checker-lease-oom.zig", "fn foo() void {}");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    const context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .cached_artifacts = &artifacts,
    };
    const tree = try source.ast();
    const fn_node = ids.astId(@intFromEnum(tree.rootDecls()[0]));
    var cfg = (try context.getOrBuildCfg(allocator, &source, fn_node)) orelse
        return error.TestUnexpectedResult;
    defer cfg.deinit();
    var result = checker_mod.AnalysisResult.init();
    defer result.deinit(allocator);

    // Prebuild the CFG so failure occurs at the analysis lease, not CFG creation.
    for (checkers) |checker| {
        for ([_]bool{ false, true }) |shared| {
            var unavailable = testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
            var cache = checker_mod.AnalysisCache.init(unavailable.allocator());
            defer cache.deinit();
            var failing_context = context;
            failing_context.analysis_cache = if (shared) &cache else null;
            const checker_allocator = if (shared) allocator else unavailable.allocator();
            try testing.expectError(error.OutOfMemory, checker.checkAst(
                &source,
                checker_allocator,
                &result.diagnostics,
                failing_context,
            ));
        }
    }
}
