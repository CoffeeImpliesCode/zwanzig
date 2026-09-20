const std = @import("std");
const checker_mod = @import("../checker.zig");
const Checker = checker_mod.Checker;
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const Source = @import("../source.zig").Source;
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
