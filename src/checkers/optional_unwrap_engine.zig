const std = @import("std");
const scan = @import("optional_unwrap/scan.zig");
const checker_mod = @import("../checker.zig");
const Checker = checker_mod.Checker;
const TypeContext = checker_mod.TypeContext;
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const Source = @import("../source.zig").Source;
const ids = @import("../ids.zig");
const engine_mod = @import("../engine.zig");
const AnalysisEngine = engine_mod.AnalysisEngine;

/// Engine-based checker that detects forced optional unwraps (.?) that may panic at runtime.
/// Uses CFG analysis to track when optionals have been checked for null.
///
/// Safe patterns (no warning):
/// - `if (x != null) { x.? }` - null check guards the unwrap
/// - `if (x) |val| { ... }` - payload capture pattern
/// - `orelse` - provides fallback value
///
/// Warned patterns:
/// - `x.?` without prior null check on the same path
pub const OptionalUnwrapEngineChecker = struct {
    pub const checker: Checker = .{
        .name = "optional-unwrap",
        .default_severity = .warning,
        .checkAstFn = checkAst,
    };

    fn checkAst(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        context: checker_mod.CheckerContext,
    ) CheckerError!void {
        const tree = src.ast() catch return;
        const tags = tree.nodes.items(.tag);

        // Track reported AST nodes across all functions to avoid duplicates
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
        var cfg_handle = (context.getOrBuildCfg(allocator, src, fn_node) catch return) orelse return;
        defer cfg_handle.deinit();

        var engine = AnalysisEngine.initWithSource(allocator, cfg_handle.cfg, src);
        defer engine.deinit();
        engine.setCheckerName("optional-unwrap");
        if (context.type_context) |type_ctx| {
            engine.setTypeContext(type_ctx);
        }
        if (context.cached_artifacts) |artifacts| {
            engine.setCachedArtifacts(artifacts);
        }
        if (context.build_metadata) |metadata| {
            engine.setBuildMetadata(metadata);
        }
        if (context.config) |config| {
            engine.setConfig(config);
        }
        if (context.analysis_limits.max_worklist_steps) |steps| {
            engine.setMaxWorklistSteps(steps);
        }
        if (context.analysis_limits.max_states_per_point) |max| {
            engine.setMaxStatesPerPoint(max);
        }
        if (context.analysis_limits.use_widening) |use_w| {
            engine.setUseWidening(use_w);
        }
        var run_ok = true;
        engine.run() catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            error.AnalysisLimitExceeded => run_ok = false,
        };
        if (context.analysis_stats) |stats| {
            stats.recordRun();
            stats.recordWidening(engine.getGraph().getWidenedNodeCount(), engine.getGraph().getWideningConvergedCount());
        }

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

        if (!run_ok) return;

        // Scan AST for unwrap_optional nodes and check nullability
        const tree = src.ast() catch return;
        try scan.scanForUnsafeUnwraps(src, allocator, diagnostics, tree, &engine, cfg_handle.cfg, reported, fn_node, context.type_context);
    }
};

// Tests
test "OptionalUnwrapEngineChecker initialization" {
    const testing = std.testing;
    try testing.expectEqualStrings("optional-unwrap", OptionalUnwrapEngineChecker.checker.name);
    try testing.expectEqual(checker_mod.Severity.warning, OptionalUnwrapEngineChecker.checker.default_severity);
}

fn expectOptionalUnwrapDiagnosticLines(
    code: [:0]const u8,
    expected_lines: []const usize,
) !void {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "skript-residual.zig", code);
    defer source.deinit();
    var type_context = TypeContext.init(allocator, &source);
    defer type_context.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try OptionalUnwrapEngineChecker.checker.checkAst(&source, allocator, &diagnostics, .{
        .build_metadata = null,
        .type_context = &type_context,
    });
    try std.testing.expectEqual(expected_lines.len, diagnostics.items.len);
    for (diagnostics.items) |diagnostic| {
        try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
    for (expected_lines) |expected_line| {
        var found = false;
        for (diagnostics.items) |diagnostic| {
            if (diagnostic.range.start.line == expected_line) {
                found = true;
                break;
            }
        }
        try std.testing.expect(found);
    }
}

test "skript residual: direct non-null field assignments dominate unwraps" {
    const code: [:0]const u8 =
        \\const State = struct {
        \\    field: ?u32 = null,
        \\};
        \\
        \\fn literalAssignment(state: *State) u32 {
        \\    state.field = 1;
        \\    return state.field.?;
        \\}
        \\
        \\fn typedAssignment(state: *State, value: u32) u32 {
        \\    state.field = value;
        \\    return state.field.?;
        \\}
        \\
        \\fn derefAssignment(slot: *?u32, value: u32) u32 {
        \\    slot.* = value;
        \\    return slot.*.?;
        \\}
        \\
        \\fn branchOnly(state: *State, take_branch: bool) u32 {
        \\    if (take_branch) state.field = 2;
        \\    return state.field.?;
        \\}
        \\
        \\fn optionalAssignment(state: *State, value: ?u32) u32 {
        \\    state.field = value;
        \\    return state.field.?;
        \\}
        \\
        \\fn reassignedNull(state: *State) u32 {
        \\    state.field = 3;
        \\    state.field = null;
        \\    return state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 22, 27, 33 });
}

test "skript residual: prior unwrap facts require an unchanged storage path" {
    const code: [:0]const u8 =
        \\const State = struct {
        \\    field: ?u32 = null,
        \\};
        \\
        \\fn touch(state: *State) void {
        \\    state.field = null;
        \\}
        \\
        \\fn retained(state: *State) u32 {
        \\    state.field = 1;
        \\    const first = state.field.?;
        \\    return first + state.field.?;
        \\}
        \\
        \\fn unknownMutation(state: *State) u32 {
        \\    state.field = 1;
        \\    const first = state.field.?;
        \\    touch(state);
        \\    return first + state.field.?;
        \\}
        \\
        \\fn reassignedNull(state: *State) u32 {
        \\    state.field = 1;
        \\    const first = state.field.?;
        \\    state.field = null;
        \\    return first + state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 19, 26 });
}

test "skript residual: try preserves optional payload nullability" {
    const code: [:0]const u8 =
        \\const State = struct {
        \\    field: ?u32 = null,
        \\};
        \\
        \\fn maybe() !?u32 {
        \\    return null;
        \\}
        \\
        \\fn definite() !u32 {
        \\    return 1;
        \\}
        \\
        \\fn use(state: *State) !u32 {
        \\    state.field = try maybe();
        \\    return state.field.?;
        \\}
        \\
        \\fn useDefinite(state: *State) !u32 {
        \\    state.field = try definite();
        \\    return state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{15});
}

test "prior unwrap proof rejects conditional evaluation" {
    const code: [:0]const u8 =
        \\const State = struct {
        \\    field: ?u32 = null,
        \\};
        \\
        \\fn conditionalIf(state: *State, take: bool) u32 {
        \\    if (take) _ = state.field.?;
        \\    return state.field.?;
        \\}
        \\
        \\fn conditionalAnd(state: *State, take: bool) u32 {
        \\    _ = take and state.field.? != 0;
        \\    return state.field.?;
        \\}
        \\
        \\fn conditionalOrelse(state: *State, fallback: ?u32) u32 {
        \\    _ = fallback orelse state.field.?;
        \\    return state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 6, 7, 11, 12, 16, 17 });
}

test "prior unwrap proof rejects later same-statement mutation" {
    const code: [:0]const u8 =
        \\const State = struct {
        \\    field: ?u32 = null,
        \\};
        \\
        \\fn use(state: *State) u32 {
        \\    const first = blk: {
        \\        if (state.field == null) return 0;
        \\        const value = state.field.?;
        \\        state.field = null;
        \\        break :blk value;
        \\    };
        \\    return first + state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{12});
}

test "prior unwrap proof rejects root replacement" {
    const code: [:0]const u8 =
        \\const State = struct {
        \\    field: ?u32 = null,
        \\};
        \\
        \\fn use(original: *State, replacement: *State) u32 {
        \\    var state = original;
        \\    if (state.field == null) return 0;
        \\    const first = state.field.?;
        \\    state = replacement;
        \\    return first + state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{10});
}

test "prior unwrap proof rejects writable alias mutation" {
    const code: [:0]const u8 =
        \\const State = struct {
        \\    field: ?u32 = null,
        \\};
        \\
        \\fn use(state: *State) u32 {
        \\    if (state.field == null) return 0;
        \\    const first = state.field.?;
        \\    const alias = &state.field;
        \\    alias.* = null;
        \\    return first + state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{10});
}

test "compound short-circuit guards require dominating unchanged facts" {
    const code: [:0]const u8 =
        \\fn clear(value: *?u8) bool {
        \\    value.* = null;
        \\    return true;
        \\}
        \\
        \\fn safe(a: ?u8, b: ?u8, x: u8) bool {
        \\    return a != null and b != null and a.? + b.? == x;
        \\}
        \\
        \\fn mutated(a: ?u8, x: u8) bool {
        \\    var value = a;
        \\    return value != null and clear(&value) and value.? == x;
        \\}
        \\
        \\fn wrongOr(a: ?u8, b: ?u8, x: u8) bool {
        \\    return a != null or b != null or a.? + b.? == x;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 12, 16, 16 });
}

test "lazy init proof requires definite assignment and unchanged storage" {
    const code: [:0]const u8 =
        \\const State = struct {
        \\    field: ?u32 = null,
        \\};
        \\
        \\fn safe(state: *State) u32 {
        \\    if (state.field == null) {
        \\        state.field = 1;
        \\    }
        \\    return state.field.?;
        \\}
        \\
        \\fn nullableAssignment(state: *State, value: ?u32) u32 {
        \\    if (state.field == null) {
        \\        state.field = value;
        \\    }
        \\    return state.field.?;
        \\}
        \\
        \\fn rootMutation(original: *State, replacement: *State) u32 {
        \\    var state = original;
        \\    if (state.field == null) {
        \\        state.field = 1;
        \\    }
        \\    state = replacement;
        \\    return state.field.?;
        \\}
        \\
        \\fn aliasMutation(state: *State) u32 {
        \\    if (state.field == null) {
        \\        state.field = 1;
        \\    }
        \\    const alias = &state.field;
        \\    alias.* = null;
        \\    return state.field.?;
        \\}
        \\
        \\fn overwrittenInBranch(state: *State) u32 {
        \\    if (state.field == null) {
        \\        state.field = 1;
        \\        state.field = null;
        \\    }
        \\    return state.field.?;
        \\}
        \\
        \\fn branchOnly(state: *State, take: bool) u32 {
        \\    if (state.field == null) {
        \\        if (take) state.field = 1;
        \\    }
        \\    return state.field.?;
        \\}
        \\
        \\fn elseMutation(state: *State) u32 {
        \\    if (state.field == null) {
        \\        state.field = 1;
        \\    } else {
        \\        state.field = null;
        \\    }
        \\    return state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 16, 25, 34, 42, 49, 58 });
}

test "field assignment proofs respect evaluation order and overlapping storage" {
    const code: [:0]const u8 =
        \\const State = struct { first: ?u32 = null, second: ?u32 = null };
        \\fn identity(value: u32) u32 { return value; }
        \\fn clear(state: *State) u32 { state.first = null; return 0; }
        \\fn use(_: *u32, _: *u32) void {}
        \\fn safe(state: *State) void {
        \\    state.first = 1;
        \\    state.second = 2;
        \\    use(&state.first.?, &state.second.?);
        \\}
        \\fn future(state: *State) void {
        \\    state.first = identity(state.first.?);
        \\}
        \\fn sideEffect(state: *State) u32 {
        \\    state.first = 1;
        \\    state.second = clear(state);
        \\    return state.first.?;
        \\}
        \\const Overlap = union { first: ?u32, second: ?u32 };
        \\fn overlap(state: *Overlap) u32 {
        \\    state.first = 1;
        \\    state.second = null;
        \\    return state.first.?;
        \\}
    ;
    try expectOptionalUnwrapDiagnosticLines(code, &.{ 11, 16, 22 });
}

test "false OR guards dominate nested expression branches" {
    const code: [:0]const u8 =
        \\const Span = struct { low: i32, high: i32 };
        \\const Summary = struct { span: ?Span = null };
        \\const Case = enum { same, before };
        \\
        \\fn compare(case: Case, first: Summary, second: Summary, identical: bool) bool {
        \\    return switch (case) {
        \\        .same => if (identical)
        \\            if (first.span == null and second.span == null)
        \\                false
        \\            else
        \\                true
        \\        else if (first.span == null or second.span == null)
        \\            false
        \\        else if (first.span.?.high < second.span.?.low or
        \\            second.span.?.high < first.span.?.low)
        \\            false
        \\        else if (first.span.?.low == first.span.?.high and
        \\            second.span.?.low == second.span.?.high and
        \\            first.span.?.low == second.span.?.low)
        \\            true
        \\        else
        \\            false,
        \\        .before => if (identical)
        \\            false
        \\        else if (first.span == null or second.span == null)
        \\            false
        \\        else if (first.span.?.high < second.span.?.low)
        \\            true
        \\        else if (first.span.?.low >= second.span.?.high)
        \\            false
        \\        else
        \\            true,
        \\    };
        \\}
        \\
        \\fn negatedGuard(first: Summary, second: Summary) i32 {
        \\    return if (!(first.span == null or second.span == null))
        \\        first.span.?.low
        \\    else
        \\        0;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{});
}

test "false branch proofs reject wrong polarity and incomplete guards" {
    const code: [:0]const u8 =
        \\const Span = struct { low: i32, high: i32 };
        \\const Summary = struct { span: ?Span = null };
        \\
        \\fn wrongThen(first: Summary, second: Summary) bool {
        \\    return if (first.span == null or second.span == null)
        \\        first.span.?.low < second.span.?.high
        \\    else
        \\        false;
        \\}
        \\
        \\fn insufficientElse(first: Summary, second: Summary) bool {
        \\    return if (first.span == null and second.span == null)
        \\        false
        \\    else
        \\        first.span.?.low < second.span.?.high;
        \\}
        \\
        \\fn invertedElse(first: Summary, second: Summary) bool {
        \\    return if (first.span != null or second.span != null)
        \\        false
        \\    else
        \\        first.span.?.low < second.span.?.high;
        \\}
        \\
        \\fn negatedUnsafe(first: Summary, second: Summary) bool {
        \\    return if (!(first.span != null and second.span != null))
        \\        first.span.?.low < second.span.?.high
        \\    else
        \\        false;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 6, 6, 15, 15, 22, 22, 27, 27 });
}

test "false branch proofs reject intervening writes and strict unknown assignments" {
    const code: [:0]const u8 =
        \\const Span = struct { low: i32, high: i32 };
        \\const Summary = struct { span: ?Span = null };
        \\
        \\fn mutated(first: *Summary, second: *Summary) bool {
        \\    return if (first.span == null or second.span == null)
        \\        false
        \\    else blk: {
        \\        first.span = null;
        \\        break :blk first.span.?.low < second.span.?.high;
        \\    };
        \\}
        \\
        \\fn strictUnknown(input: anytype) i32 {
        \\    var state: Summary = .{};
        \\    state.span = input;
        \\    return state.span.?.low;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 9, 9, 16 });
}

test "compound early exits prove only required null facts" {
    const code: [:0]const u8 =
        \\const State = struct { field: ?u32 = null };
        \\
        \\fn safeOr(state: *State, reject: bool) u32 {
        \\    if (reject or state.field == null) return 0;
        \\    return state.field.?;
        \\}
        \\
        \\fn safeGrouped(state: *State, reject: bool) u32 {
        \\    if ((reject or state.field == null)) return 0;
        \\    return state.field.?;
        \\}
        \\
        \\fn unsafeAnd(state: *State, reject: bool) u32 {
        \\    if (reject and state.field == null) return 0;
        \\    return state.field.?;
        \\}
        \\
        \\fn wrongPolarity(state: *State, reject: bool) u32 {
        \\    if (reject or state.field != null) return 0;
        \\    return state.field.?;
        \\}
        \\
        \\fn interveningMutation(state: *State, reject: bool) u32 {
        \\    if (reject or state.field == null) return 0;
        \\    state.field = null;
        \\    return state.field.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 15, 20, 26 });
}
test "repeated optional calls cannot assume a stable result" {
    const code: [:0]const u8 =
        \\var calls: u32 = 0;
        \\const Gate = struct {
        \\    fn next(_: Gate) ?u8 {
        \\        calls += 1;
        \\        return if (calls == 1) 1 else null;
        \\    }
        \\};
        \\fn unsafeRepeated(gate: Gate) u8 {
        \\    if (gate.next() == null) return 0;
        \\    return gate.next().?;
        \\}
    ;
    try expectOptionalUnwrapDiagnosticLines(code, &.{10});
}

test "catch switch assignment joins success and fallback nullability" {
    const code: [:0]const u8 =
        \\const Task = struct {};
        \\const Failure = error{Unavailable};
        \\const State = struct { task: ?Task = null };
        \\
        \\fn primary() Failure!Task { return .{}; }
        \\fn fallback() Task { return .{}; }
        \\fn maybeFallback() ?Task { return null; }
        \\
        \\fn safe(state: *State) Task {
        \\    const task = primary() catch |err| switch (err) {
        \\        error.Unavailable => fallback(),
        \\    };
        \\    state.task = task;
        \\    return state.task.?;
        \\}
        \\
        \\fn nullableFallback(state: *State) Task {
        \\    const task = primary() catch |err| switch (err) {
        \\        error.Unavailable => maybeFallback(),
        \\    };
        \\    state.task = task;
        \\    return state.task.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{22});
}

test "verified std.Io Future catch assignment proves non-null result" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const State = struct { future: ?std.Io.Future(void) = null };
        \\const A = struct {};
        \\const FakeState = struct { future: ?A = null };
        \\fn work() void {}
        \\const FakeIo = struct {
        \\    fn concurrent(_: FakeIo) error{Unavailable}!A { return error.Unavailable; }
        \\    fn async(_: FakeIo) ?A { return null; }
        \\};
        \\
        \\fn safe(state: *State, io: std.Io) void {
        \\    const task = io.concurrent(work, .{}) catch |err| switch (err) {
        \\        error.ConcurrencyUnavailable => io.async(work, .{}),
        \\    };
        \\    state.future = task;
        \\    _ = state.future.?;
        \\}
        \\
        \\fn control(state: *FakeState, io: FakeIo) void {
        \\    const task = io.concurrent() catch |err| switch (err) {
        \\        error.Unavailable => io.async(),
        \\    };
        \\    state.future = task;
        \\    _ = state.future.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{24});
}

test "contextual shorthand constructor uses its resolved return type" {
    const code: [:0]const u8 =
        \\const Safe = struct { fn init() Safe { return .{}; } };
        \\const Maybe = struct { fn init() ?Maybe { return null; } };
        \\const State = struct { safe: ?Safe = null, maybe: ?Maybe = null };
        \\
        \\fn safe(state: *State) Safe {
        \\    state.safe = .init();
        \\    return state.safe.?;
        \\}
        \\
        \\fn nullable(state: *State) Maybe {
        \\    state.maybe = .init();
        \\    return state.maybe.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{12});
}

test "outer try assignment dominates nested unwrap until mutation" {
    const code: [:0]const u8 =
        \\const Value = struct { number: u8 };
        \\fn definite() !Value { return .{ .number = 1 }; }
        \\fn maybe() !?Value { return null; }
        \\fn clear(value: *?Value) void { value.* = null; }
        \\fn consume(_: Value) void {}
        \\
        \\fn safe(nested: bool) !void {
        \\    var prototype: ?Value = null;
        \\    prototype = try definite();
        \\    if (nested) {
        \\        consume(prototype.?);
        \\    }
        \\}
        \\
        \\fn nullable(nested: bool) !void {
        \\    var prototype: ?Value = null;
        \\    prototype = try maybe();
        \\    if (nested) {
        \\        consume(prototype.?);
        \\    }
        \\}
        \\
        \\fn mutated(nested: bool) !void {
        \\    var prototype: ?Value = null;
        \\    prototype = try definite();
        \\    if (nested) {
        \\        clear(&prototype);
        \\        consume(prototype.?);
        \\    }
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 19, 28 });
}

test "unknown calls preserve const values but invalidate pointer storage" {
    const code: [:0]const u8 =
        \\const Item = struct { value: ?u8 = null };
        \\fn unrelated(_: anytype) void {}
        \\fn consume(_: u8) void {}
        \\
        \\fn stable(input: Item, reject: bool) void {
        \\    const item = input;
        \\    if (reject or item.value == null) return;
        \\    unrelated(item);
        \\    consume(item.value.?);
        \\}
        \\
        \\fn mutablePointer(input: *Item, reject: bool) void {
        \\    const item = input;
        \\    if (reject or item.value == null) return;
        \\    unrelated(item);
        \\    consume(item.value.?);
        \\}
        \\fn generic(input: anytype) void {
        \\    if (input.value == null) return;
        \\    clear(input);
        \\    consume(input.value.?);
        \\}
        \\fn clear(input: *Item) void { input.value = null; }
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 16, 21 });
}

test "switch arm bindings remain distinct through nested calls" {
    const code: [:0]const u8 =
        \\const Kind = enum { tensor_get, reshape };
        \\const Value = struct { class: bool, prototype: ?u8 = null };
        \\fn consume(_: u8) void {}
        \\fn wrap(value: u8) anyerror!u8 { return value; }
        \\fn consumeMany(_: []const u8) anyerror!void {}
        \\
        \\fn use(kind: Kind, first: Value, second: Value) !void {
        \\    switch (kind) {
        \\        .tensor_get => {
        \\            const tensor = first;
        \\            if (!tensor.class or tensor.prototype == null) return;
        \\            consume(tensor.prototype.?);
        \\        },
        \\        .reshape => {
        \\            const tensor = second;
        \\            if (!tensor.class or tensor.prototype == null) return;
        \\            try consumeMany(&.{ 0, try wrap(try wrap(tensor.prototype.?)) });
        \\        },
        \\    }
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{});
}

test "uncalled local methods do not establish outer unwrap facts" {
    const code: [:0]const u8 =
        \\var shared: ?u8 = null;
        \\
        \\fn outer() void {
        \\    const Local = struct {
        \\        fn hidden() void {
        \\            _ = shared.?;
        \\        }
        \\    };
        \\    _ = Local;
        \\    _ = shared.?;
        \\}
    ;

    try expectOptionalUnwrapDiagnosticLines(code, &.{ 6, 10 });
}

test "file-struct return values retain optional assignment proofs" {
    const code: [:0]const u8 =
        \\const Context = @This();
        \\const State = struct { context: ?Context = null };
        \\fn enter(self: *const Context) anyerror!Context { return self.*; }
        \\fn maybe(_: *const Context) anyerror!?Context { return null; }
        \\fn safe(state: *State, parent: *const Context) !void {
        \\    state.context = try parent.enter();
        \\    const child = &state.context.?;
        \\    _ = child;
        \\}
        \\fn nullable(state: *State, parent: *const Context) !void {
        \\    state.context = try parent.maybe();
        \\    _ = state.context.?;
        \\}
    ;
    try expectOptionalUnwrapDiagnosticLines(code, &.{12});
}

test "unrelated pointer writes preserve unescaped local optional slots" {
    const code: [:0]const u8 =
        \\const Value = struct { number: u8 };
        \\fn definite() anyerror!Value { return .{ .number = 1 }; }
        \\fn safe(other: *Value, nested: bool) !void {
        \\    var prototype: ?Value = null;
        \\    prototype = try definite();
        \\    if (nested) {
        \\        other.* = .{ .number = 2 };
        \\        _ = prototype.?;
        \\    }
        \\}
        \\fn aliased(nested: bool) !void {
        \\    var prototype: ?Value = null;
        \\    const alias = &prototype;
        \\    prototype = try definite();
        \\    if (nested) {
        \\        alias.* = null;
        \\        _ = prototype.?;
        \\    }
        \\}
    ;
    try expectOptionalUnwrapDiagnosticLines(code, &.{17});
}

test "dereferenced snapshots remain distinct from pointer aliases" {
    const code: [:0]const u8 =
        \\const Item = struct { value: ?u8 };
        \\fn snapshot(pointer: *Item) void {
        \\    const item = pointer.*;
        \\    if (item.value == null) return;
        \\    pointer.value = null;
        \\    _ = item.value.?;
        \\}
        \\fn alias(pointer: *Item) void {
        \\    const item = pointer;
        \\    if (item.value == null) return;
        \\    pointer.value = null;
        \\    _ = item.value.?;
        \\}
    ;
    try expectOptionalUnwrapDiagnosticLines(code, &.{12});
}

test "labeled block flag proves non-null until mutation" {
    const code: [:0]const u8 =
        \\const Terminal = struct { value: u32 };
        \\const Session = struct { terminal: ?Terminal = null };
        \\fn handleEvent(session: Session) bool {
        \\    const should_forward = blk: {
        \\        const terminal = session.terminal orelse break :blk false;
        \\        break :blk terminal.value > 0;
        \\    };
        \\    if (should_forward) {
        \\        const terminal = session.terminal.?;
        \\        return terminal.value > 10;
        \\    }
        \\    return false;
        \\}
    ;
    try expectOptionalUnwrapDiagnosticLines(code, &.{});
}

test "labeled block without null guard still diagnoses" {
    const code: [:0]const u8 =
        \\const Session = struct { terminal: ?u32 = null };
        \\fn handleEvent(session: Session, flag: bool) u32 {
        \\    const should_forward = blk: {
        \\        break :blk flag;
        \\    };
        \\    if (should_forward) {
        \\        return session.terminal.?;
        \\    }
        \\    return 0;
        \\}
    ;
    try expectOptionalUnwrapDiagnosticLines(code, &.{7});
}

test "labeled flag killed by intervening write still diagnoses" {
    const code: [:0]const u8 =
        \\const Terminal = struct { value: u32 };
        \\const Session = struct { terminal: ?Terminal = null };
        \\fn handleEvent(session: *Session) bool {
        \\    const should_forward = blk: {
        \\        const terminal = session.terminal orelse break :blk false;
        \\        break :blk terminal.value > 0;
        \\    };
        \\    session.terminal = null;
        \\    if (should_forward) {
        \\        const terminal = session.terminal.?;
        \\        return terminal.value > 10;
        \\    }
        \\    return false;
        \\}
    ;
    try expectOptionalUnwrapDiagnosticLines(code, &.{10});
}
