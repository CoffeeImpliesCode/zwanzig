const std = @import("std");
const checker_mod = @import("checker.zig");
const Source = @import("source.zig").Source;
const Cfg = @import("cfg.zig").Cfg;
const AnalysisEngine = @import("engine.zig").AnalysisEngine;
const BuildMetadata = @import("build_metadata.zig").BuildMetadata;
const CountingAllocator = @import("counting_allocator.zig").CountingAllocator;
const ids = @import("ids.zig");

pub const AnalysisMode = enum { configured, plain };

/// A function whose analysis engine stopped at a configured budget. Findings
/// that need a complete dataflow analysis of that function are missing, not
/// absent, so the report has to say so instead of leaving the gap implicit.
pub const limit_rule_id = "analysis-limit-exceeded";

fn reportLimitExceeded(
    allocator: std.mem.Allocator,
    diagnostics: *std.ArrayList(checker_mod.Diagnostic),
    source: *Source,
    cfg: *const Cfg,
    engine: *const AnalysisEngine,
) std.mem.Allocator.Error!void {
    const Budget = struct { name: []const u8, value: u64, remedy: []const u8 };
    // Both budgets abort `run` with one error, and `run` records the one that
    // fired, so this only names the configured ceiling that was reached.
    const budget: Budget = switch (engine.limit_kind orelse .worklist_steps) {
        .worklist_steps => .{
            .name = "worklist step",
            .value = engine.max_worklist_steps,
            .remedy = "--max-steps or max_worklist_steps",
        },
        .states_per_point => .{
            .name = "per-point state",
            .value = engine.getGraph().max_states_per_point,
            .remedy = "--max-states-per-point or max_states_per_point",
        },
    };
    const message = try std.fmt.allocPrint(
        allocator,
        "analysis limit exceeded: {s} limit {d} reached while analyzing `{s}`; " ++
            "findings that require a complete dataflow analysis of this function were not produced. Raise {s}.",
        .{ budget.name, budget.value, cfg.fn_name orelse "<anonymous>", budget.remedy },
    );
    errdefer allocator.free(message);

    var location: checker_mod.Location = .init(1, 1);
    if (cfg.fn_ast_node) |fn_node| {
        const token = (try source.ast()).nodes.items(.main_token)[ids.astIndex(fn_node)];
        location = try source.tokenLocation(token);
    }
    const diagnostic: checker_mod.Diagnostic = .{
        .file_path = source.getFilePath(),
        .rule_id = limit_rule_id,
        .severity = .err,
        .message = message,
        .range = .fromSingleLocation(location),
    };
    try diagnostics.append(allocator, diagnostic);
}

/// An exclusive lease. Do not copy it or keep engine pointers after deinit.
/// Graph results remain read-only, but lazy engine query caches may grow.
/// The source, CFGs, type context, and optional cache must outlive the lease.
pub const AnalysisHandle = struct {
    engine: *AnalysisEngine,
    complete: bool,
    entry: *Entry,
    cache: ?*AnalysisCache,

    pub fn deinit(self: *AnalysisHandle) void {
        if (self.cache) |cache| {
            cache.release(self.entry);
        } else {
            self.entry.deinit();
        }
        self.* = undefined;
    }
};

const Key = struct {
    source: *Source,
    cfg: *const Cfg,
    type_context: ?*checker_mod.TypeContext,
    config: ?*const checker_mod.Config,
    build_metadata: ?*const BuildMetadata,
    artifacts: ?*checker_mod.CachedArtifacts,
    limits: checker_mod.AnalysisLimits,
};

/// The counting allocator must not move while an engine allocation is live.
const Entry = struct {
    counting: CountingAllocator,
    engine: *AnalysisEngine,
    key: Key,
    complete: bool = true,

    fn create(allocator: std.mem.Allocator, key: Key) std.mem.Allocator.Error!*Entry {
        const entry = try allocator.create(Entry);
        errdefer allocator.destroy(entry);
        entry.* = .{
            .counting = CountingAllocator.init(allocator),
            .engine = undefined,
            .key = key,
        };
        const engine_allocator = entry.counting.allocator();
        entry.engine = try engine_allocator.create(AnalysisEngine);
        entry.engine.* = AnalysisEngine.initWithSource(engine_allocator, key.cfg, key.source);
        return entry;
    }

    fn deinit(self: *Entry) void {
        const allocator = self.counting.backing;
        self.engine.deinit();
        self.counting.allocator().destroy(self.engine);
        std.debug.assert(self.counting.live_bytes == 0);
        allocator.destroy(self);
    }
};

/// Per-file, first-fit cache. No entry is evicted to admit another result.
/// Checked-out engines are absent from the cache and are charged on return.
/// Destroy all handles first, then this cache, then its borrowed source, CFGs,
/// type contexts, configurations, metadata, and allocator. Their semantic
/// contents must remain unchanged while results are retained.
pub const AnalysisCache = struct {
    allocator: std.mem.Allocator,
    entries: [max_entries]*Entry = undefined,
    entry_count: usize = 0,
    retained_bytes: usize = 0,
    active_leases: usize = 0,
    /// May be lowered before use. It never raises the fixed retention limit.
    byte_budget: usize = max_retained_bytes,

    pub const max_entries: usize = 64;
    pub const max_retained_bytes: usize = 16 * 1024 * 1024;

    pub fn init(allocator: std.mem.Allocator) AnalysisCache {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *AnalysisCache) void {
        std.debug.assert(self.active_leases == 0);
        for (self.entries[0..self.entry_count]) |entry| entry.deinit();
        self.* = undefined;
    }

    fn find(self: *const AnalysisCache, key: Key) ?usize {
        for (self.entries[0..self.entry_count], 0..) |entry, index| {
            if (std.meta.eql(entry.key, key)) return index;
        }
        return null;
    }

    fn take(self: *AnalysisCache, key: Key) ?*Entry {
        const index = self.find(key) orelse return null;
        const entry = self.entries[index];
        self.entry_count -= 1;
        self.entries[index] = self.entries[self.entry_count];
        self.retained_bytes -= entry.counting.live_bytes;
        return entry;
    }

    fn lease(self: *AnalysisCache, entry: *Entry) AnalysisHandle {
        self.active_leases += 1;
        return .{
            .engine = entry.engine,
            .complete = entry.complete,
            .entry = entry,
            .cache = self,
        };
    }

    fn release(self: *AnalysisCache, entry: *Entry) void {
        std.debug.assert(self.active_leases > 0);
        self.active_leases -= 1;
        const budget = @min(self.byte_budget, max_retained_bytes);
        const bytes = entry.counting.live_bytes;
        if (self.entry_count == max_entries or self.retained_bytes > budget or
            bytes > budget - self.retained_bytes or self.find(entry.key) != null)
        {
            entry.deinit();
            return;
        }
        self.entries[self.entry_count] = entry;
        self.entry_count += 1;
        self.retained_bytes += bytes;
    }
};

/// Everything a run reads off the key to configure its engine.
///
/// The run collects these as one value instead of unwrapping each optional
/// where it is used. Seven independent unwraps are seven independent branches,
/// so the state that reaches the end of a run is the product of them rather
/// than a handful of cases: a run whose key names some inputs and not others
/// has one state per combination, and the dataflow analysis cannot merge
/// them. Deciding what to configure once, here, keeps the run itself linear.
const EngineSources = struct {
    type_context: ?*checker_mod.TypeContext,
    config: ?*const checker_mod.Config,
    build_metadata: ?*const BuildMetadata,
    artifacts: ?*checker_mod.CachedArtifacts,
    max_worklist_steps: ?usize,
    max_states_per_point: ?u32,
    use_widening: ?bool,

    /// Configure the engine with exactly the inputs the key carries. An input
    /// the key does not name leaves the engine's own default in place.
    fn apply(self: EngineSources, engine: *AnalysisEngine) void {
        if (self.type_context) |types| engine.setTypeContext(types);
        if (self.config) |config| engine.setConfig(config);
        if (self.build_metadata) |metadata| engine.setBuildMetadata(metadata);
        if (self.artifacts) |artifacts| engine.setCachedArtifacts(artifacts);
        if (self.max_worklist_steps) |steps| engine.setMaxWorklistSteps(steps);
        if (self.max_states_per_point) |states| engine.setMaxStatesPerPoint(states);
        if (self.use_widening) |enabled| engine.setUseWidening(enabled);
    }
};

pub fn getOrAnalyze(
    context: *const checker_mod.CheckerContext,
    allocator: std.mem.Allocator,
    source: *Source,
    cfg_handle: *const checker_mod.CfgHandle,
    checker_name: []const u8,
    mode: AnalysisMode,
) std.mem.Allocator.Error!AnalysisHandle {
    const key: Key = .{
        .source = source,
        .cfg = cfg_handle.cfg,
        .type_context = if (mode == .configured) context.type_context else null,
        .config = if (mode == .configured) context.config else null,
        .build_metadata = context.build_metadata,
        .artifacts = context.cached_artifacts,
        .limits = context.analysis_limits,
    };
    const cache: ?*AnalysisCache = eligible: {
        if (mode == .plain or cfg_handle.owned) break :eligible null;
        const artifacts = context.cached_artifacts orelse break :eligible null;
        const fn_node = cfg_handle.cfg.fn_ast_node orelse break :eligible null;
        if (artifacts.getCfg(ids.astIndex(fn_node)) != cfg_handle.cfg) break :eligible null;
        break :eligible context.analysis_cache;
    };
    if (cache) |owner| {
        if (owner.take(key)) |entry| return owner.lease(entry);
    }

    const entry = try Entry.create(if (cache) |owner| owner.allocator else allocator, key);
    errdefer entry.deinit();
    const engine = entry.engine;
    engine.setCheckerName(checker_name);
    // The log label is not semantic and may be a short-lived caller buffer.
    defer engine.checker_name = null;
    const sources: EngineSources = .{
        .type_context = key.type_context,
        .config = key.config,
        .build_metadata = key.build_metadata,
        .artifacts = key.artifacts,
        .max_worklist_steps = key.limits.max_worklist_steps,
        .max_states_per_point = key.limits.max_states_per_point,
        .use_widening = key.limits.use_widening,
    };
    sources.apply(engine);

    if (context.analysis_stats) |stats| stats.recordRun();
    defer if (context.analysis_stats) |stats| {
        stats.recordWidening(
            engine.getGraph().getWidenedNodeCount(),
            engine.getGraph().getWideningConvergedCount(),
        );
    };
    engine.run() catch |err| switch (err) {
        error.OutOfMemory => return error.OutOfMemory,
        error.AnalysisLimitExceeded => {
            entry.complete = false;
            // Consumers of this handle drop everything that needs a complete
            // analysis, so report the gap where the error is swallowed rather
            // than letting an unanalyzed function read as a clean one.
            if (context.diagnostics) |list| {
                try reportLimitExceeded(allocator, list, key.source, key.cfg, engine);
            }
        },
    };
    if (cache) |owner| return owner.lease(entry);
    return .{ .engine = engine, .complete = entry.complete, .entry = entry, .cache = null };
}

test "AnalysisCache reuse preserves graph states and store diagnostics" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "reuse.zig", "const std = @import(\"std\");\n" ++
        "fn foo(allocator: std.mem.Allocator) !void {\n" ++
        "    const ptr = try allocator.alloc(u8, 1);\n" ++
        "    allocator.free(ptr);\n" ++
        "    allocator.free(ptr);\n" ++
        "}\n");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    var stats: checker_mod.AnalysisStats = .{};
    const context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .cached_artifacts = &artifacts,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    var baseline = AnalysisEngine.initWithSource(allocator, cfg.cfg, &source);
    defer baseline.deinit();
    baseline.setCachedArtifacts(&artifacts);
    try baseline.run();

    const first_engine = first_run: {
        var first = try context.getOrAnalyze(allocator, &source, &cfg, "first", .configured);
        defer first.deinit();
        try std.testing.expect(first.complete);
        try expectSameGraph(&baseline, first.engine);
        try std.testing.expect(hasViolation(first.engine, .double_free));
        break :first_run first.engine;
    };
    var reused = try context.getOrAnalyze(allocator, &source, &cfg, "other", .configured);
    defer reused.deinit();
    try std.testing.expect(reused.engine == first_engine);
    try expectSameGraph(&baseline, reused.engine);
    try std.testing.expect(hasViolation(reused.engine, .double_free));
    try std.testing.expectEqual(@as(u64, 1), stats.total_runs);
    try std.testing.expectEqual(
        @as(u64, baseline.getGraph().getWidenedNodeCount()),
        stats.widened_nodes,
    );
    try std.testing.expectEqual(
        @as(u64, baseline.getGraph().getWideningConvergedCount()),
        stats.widening_converged,
    );
}

test "AnalysisCache keeps configured models separate from plain analysis" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "models.zig", "extern fn acquire() usize;\n" ++
        "extern fn release(handle: usize) void;\n" ++
        "fn foo() void {\n" ++
        "    const handle = acquire();\n" ++
        "    release(handle);\n" ++
        "    release(handle);\n" ++
        "}\n");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var types = checker_mod.TypeContext.init(allocator, &source);
    defer types.deinit();
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    const configured: checker_mod.Config = .{
        .rule_filter = .none,
        .resource_models = &.{
            .{ .kind = .alloc, .method_name = "acquire" },
            .{ .kind = .free, .method_name = "release" },
        },
    };
    const unconfigured: checker_mod.Config = .{ .rule_filter = .none };
    var stats: checker_mod.AnalysisStats = .{};
    var context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .type_context = &types,
        .config = &configured,
        .cached_artifacts = &artifacts,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    const modeled_engine = modeled_run: {
        var modeled = try context.getOrAnalyze(allocator, &source, &cfg, "modeled", .configured);
        defer modeled.deinit();
        try std.testing.expect(modeled.complete);
        try std.testing.expect(hasViolation(modeled.engine, .double_free));
        break :modeled_run modeled.engine;
    };

    var plain = try context.getOrAnalyze(allocator, &source, &cfg, "plain", .plain);
    defer plain.deinit();
    var plain_again = try context.getOrAnalyze(allocator, &source, &cfg, "plain", .plain);
    defer plain_again.deinit();
    try std.testing.expect(plain.complete and plain_again.complete);
    try std.testing.expect(!hasViolation(plain.engine, .double_free));
    try std.testing.expect(plain.engine.type_context == null);
    try std.testing.expect(plain.engine.config == null);
    try std.testing.expect(plain.engine != plain_again.engine);
    try expectSameGraph(plain.engine, plain_again.engine);

    context.config = &unconfigured;
    var unmodeled = try context.getOrAnalyze(allocator, &source, &cfg, "unmodeled", .configured);
    defer unmodeled.deinit();
    try std.testing.expect(!hasViolation(unmodeled.engine, .double_free));
    context.config = &configured;
    var reused = try context.getOrAnalyze(allocator, &source, &cfg, "reused", .configured);
    defer reused.deinit();
    try std.testing.expect(reused.engine == modeled_engine);
    try std.testing.expectEqual(@as(u64, 4), stats.total_runs);
}

test "AnalysisCache separates limits and retains incomplete results" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "limits.zig", "fn foo() void {}");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    var stats: checker_mod.AnalysisStats = .{};
    var context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .cached_artifacts = &artifacts,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
        .analysis_limits = .{ .max_worklist_steps = 0 },
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    const limited_engine = limited_run: {
        var limited = try context.getOrAnalyze(allocator, &source, &cfg, "limited", .configured);
        defer limited.deinit();
        try std.testing.expect(!limited.complete);
        break :limited_run limited.engine;
    };
    const limited_size = limited_hit_run: {
        var limited_hit = try context.getOrAnalyze(allocator, &source, &cfg, "other", .configured);
        defer limited_hit.deinit();
        try std.testing.expect(!limited_hit.complete);
        try std.testing.expect(limited_engine == limited_hit.engine);
        break :limited_hit_run limited_hit.engine.getGraph().nodeCount();
    };
    try std.testing.expectEqual(@as(u64, 1), stats.total_runs);

    context.analysis_limits = .{};
    {
        var complete = try context.getOrAnalyze(allocator, &source, &cfg, "complete", .configured);
        defer complete.deinit();
        try std.testing.expect(complete.complete);
        try std.testing.expect(complete.engine.getGraph().nodeCount() > limited_size);
    }
    context.analysis_limits = .{ .max_states_per_point = 0 };
    {
        var capped = try context.getOrAnalyze(allocator, &source, &cfg, "capped", .configured);
        defer capped.deinit();
        try std.testing.expect(!capped.complete);
        try std.testing.expectEqual(@as(usize, 0), capped.engine.getGraph().nodeCount());
    }
    context.analysis_limits = .{ .use_widening = true };
    var widened = try context.getOrAnalyze(allocator, &source, &cfg, "widened", .configured);
    defer widened.deinit();
    try std.testing.expect(widened.complete);
    try std.testing.expectEqual(@as(u64, 4), stats.total_runs);
}

test "AnalysisCache reports an exhausted budget once per incomplete analysis" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "reported.zig", "fn foo() void {}");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    var stats: checker_mod.AnalysisStats = .{};
    var diagnostics: std.ArrayList(checker_mod.Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    var context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .cached_artifacts = &artifacts,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
        .diagnostics = &diagnostics,
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();

    // A function analyzed to a fixed point must not look like a truncated one.
    {
        var complete = try context.getOrAnalyze(allocator, &source, &cfg, "complete", .configured);
        defer complete.deinit();
        try std.testing.expect(complete.complete);
    }
    try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);

    context.analysis_limits = .{ .max_worklist_steps = 0 };
    {
        var limited = try context.getOrAnalyze(allocator, &source, &cfg, "limited", .configured);
        defer limited.deinit();
        try std.testing.expect(!limited.complete);
    }
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    {
        const reported = diagnostics.items[0];
        try std.testing.expectEqualStrings(limit_rule_id, reported.rule_id);
        try std.testing.expectEqual(checker_mod.Severity.err, reported.severity);
        try std.testing.expectEqualStrings("reported.zig", reported.file_path);
    }

    // A second consumer leasing the same engine reuses the first report rather
    // than claiming the same gap again.
    {
        var again = try context.getOrAnalyze(allocator, &source, &cfg, "other", .configured);
        defer again.deinit();
        try std.testing.expect(!again.complete);
    }
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);

    context.analysis_limits = .{ .max_states_per_point = 0 };
    {
        var capped = try context.getOrAnalyze(allocator, &source, &cfg, "capped", .configured);
        defer capped.deinit();
        try std.testing.expect(!capped.complete);
    }
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
}

test "AnalysisCache keys borrowed source type metadata and artifact identities" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "identity.zig", "fn foo() void {}");
    defer source.deinit();
    var other_source = Source.init(allocator, "identity.zig", "fn foo() void {}");
    defer other_source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var other_artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer other_artifacts.deinit();
    var types = checker_mod.TypeContext.init(allocator, &source);
    defer types.deinit();
    var other_types = checker_mod.TypeContext.init(allocator, &source);
    defer other_types.deinit();
    const metadata = BuildMetadata.fromNative();
    const other_metadata = BuildMetadata.fromNative();
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    var stats: checker_mod.AnalysisStats = .{};
    var context: checker_mod.CheckerContext = .{
        .build_metadata = &metadata,
        .type_context = &types,
        .cached_artifacts = &artifacts,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    const first_engine = first_run: {
        var first = try context.getOrAnalyze(allocator, &source, &cfg, "first", .configured);
        defer first.deinit();
        break :first_run first.engine;
    };
    context.type_context = &other_types;
    var new_types = try context.getOrAnalyze(allocator, &source, &cfg, "types", .configured);
    new_types.deinit();
    context.type_context = &types;
    context.build_metadata = &other_metadata;
    var new_metadata = try context.getOrAnalyze(allocator, &source, &cfg, "metadata", .configured);
    new_metadata.deinit();
    context.build_metadata = &metadata;
    var new_source = try context.getOrAnalyze(allocator, &other_source, &cfg, "source", .configured);
    new_source.deinit();
    context.cached_artifacts = &other_artifacts;
    var foreign = try context.getOrAnalyze(allocator, &source, &cfg, "foreign", .configured);
    defer foreign.deinit();
    try std.testing.expect(foreign.cache == null);
    var other_cfg = try buildTestCfg(&source, context);
    defer other_cfg.deinit();
    var new_artifacts = try context.getOrAnalyze(allocator, &source, &other_cfg, "artifacts", .configured);
    defer new_artifacts.deinit();
    try std.testing.expect(new_artifacts.complete);
    context.cached_artifacts = &artifacts;
    var hit = try context.getOrAnalyze(allocator, &source, &cfg, "hit", .configured);
    defer hit.deinit();
    try std.testing.expect(first_engine == hit.engine);
    try std.testing.expectEqual(@as(u64, 6), stats.total_runs);
}

test "AnalysisCache zero and tiny budgets never truncate analysis" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "budget.zig", "fn foo() void {}");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    const base: checker_mod.CheckerContext = .{ .build_metadata = null, .cached_artifacts = &artifacts };
    var cfg = try buildTestCfg(&source, base);
    defer cfg.deinit();
    var baseline = try base.getOrAnalyze(allocator, &source, &cfg, "baseline", .configured);
    defer baseline.deinit();
    for ([_]usize{ 0, 1 }) |budget| {
        var cache = AnalysisCache.init(allocator);
        defer cache.deinit();
        cache.byte_budget = budget;
        var stats: checker_mod.AnalysisStats = .{};
        var context = base;
        context.analysis_cache = &cache;
        context.analysis_stats = &stats;
        for (0..2) |_| {
            var result = try context.getOrAnalyze(allocator, &source, &cfg, "uncached", .configured);
            defer result.deinit();
            try std.testing.expect(result.complete);
            try expectSameGraph(baseline.engine, result.engine);
        }
        try std.testing.expectEqual(@as(u64, 2), stats.total_runs);
        try std.testing.expectEqual(@as(usize, 0), cache.retained_bytes);
        try std.testing.expectEqual(@as(usize, 0), cache.entry_count);
    }
}

test "AnalysisCache retains first fitting entries without eviction" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "first-fit.zig", "fn foo() void {}");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    var stats: checker_mod.AnalysisStats = .{};
    var context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .cached_artifacts = &artifacts,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    const first_engine = first_run: {
        var first = try context.getOrAnalyze(allocator, &source, &cfg, "first", .configured);
        defer first.deinit();
        break :first_run first.engine;
    };
    cache.byte_budget = cache.retained_bytes;
    context.analysis_limits.max_worklist_steps = 1000;
    {
        var overflow = try context.getOrAnalyze(allocator, &source, &cfg, "overflow", .configured);
        defer overflow.deinit();
        try std.testing.expect(overflow.complete);
    }
    try std.testing.expectEqual(@as(usize, 1), cache.entry_count);
    context.analysis_limits = .{};
    {
        var hit = try context.getOrAnalyze(allocator, &source, &cfg, "hit", .configured);
        defer hit.deinit();
        try std.testing.expect(hit.engine == first_engine);
    }
    try std.testing.expectEqual(@as(u64, 2), stats.total_runs);

    cache.byte_budget = AnalysisCache.max_retained_bytes;
    for (0..AnalysisCache.max_entries) |index| {
        context.analysis_limits.max_worklist_steps = 1000 + index;
        {
            var next = try context.getOrAnalyze(allocator, &source, &cfg, "fill", .configured);
            defer next.deinit();
            try std.testing.expect(next.complete);
        }
        try std.testing.expectEqual(@min(index + 2, AnalysisCache.max_entries), cache.entry_count);
    }
    try std.testing.expectEqual(AnalysisCache.max_entries, cache.entry_count);
    context.analysis_limits = .{};
    var final_hit = try context.getOrAnalyze(allocator, &source, &cfg, "final-hit", .configured);
    defer final_hit.deinit();
    try std.testing.expect(final_hit.engine == first_engine);
    try std.testing.expectEqual(@as(u64, 2 + AnalysisCache.max_entries), stats.total_runs);
}

test "AnalysisCache rejects owned CFGs and contexts without artifact ownership" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "owned.zig", "fn foo() void {}");
    defer source.deinit();
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    var stats: checker_mod.AnalysisStats = .{};
    var context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    try std.testing.expect(cfg.owned);
    var first = try context.getOrAnalyze(allocator, &source, &cfg, "owned", .configured);
    defer first.deinit();
    var borrowed = cfg;
    borrowed.owned = false;
    var second = try context.getOrAnalyze(allocator, &source, &borrowed, "borrowed", .configured);
    defer second.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    context.cached_artifacts = &artifacts;
    var third = try context.getOrAnalyze(allocator, &source, &cfg, "owned-artifacts", .configured);
    defer third.deinit();
    try std.testing.expect(first.complete and second.complete and third.complete);
    try std.testing.expect(first.cache == null and second.cache == null and third.cache == null);
    try std.testing.expectEqual(@as(u64, 3), stats.total_runs);
    try std.testing.expectEqual(@as(usize, 0), cache.entry_count);
}

test "AnalysisCache teardown leaves artifact CFGs and borrowed types alive" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "lifetime.zig", "fn helper() void {}\nfn foo() void { helper(); }");
    defer source.deinit();
    var artifact_memory = CountingAllocator.init(allocator);
    var artifacts = checker_mod.CachedArtifacts.init(artifact_memory.allocator());
    defer artifacts.deinit();
    var types = checker_mod.TypeContext.init(allocator, &source);
    defer types.deinit();
    var cache_memory = CountingAllocator.init(allocator);
    {
        var cache = AnalysisCache.init(cache_memory.allocator());
        defer cache.deinit();
        var unavailable = std.testing.FailingAllocator.init(allocator, .{ .fail_index = 0 });
        const context: checker_mod.CheckerContext = .{
            .build_metadata = null,
            .type_context = &types,
            .cached_artifacts = &artifacts,
            .analysis_cache = &cache,
        };
        const tree = try source.ast();
        const fn_node = ids.astId(@intFromEnum(tree.rootDecls()[1]));
        var cfg = (try context.getOrBuildCfg(unavailable.allocator(), &source, fn_node)) orelse
            return error.TestUnexpectedResult;
        defer cfg.deinit();
        var result = try context.getOrAnalyze(unavailable.allocator(), &source, &cfg, "lifetime", .configured);
        defer result.deinit();
        try std.testing.expect(result.complete);
        try std.testing.expect(!unavailable.has_induced_failure);
    }
    try std.testing.expectEqual(@as(usize, 0), cache_memory.live_bytes);
    const tree = try source.ast();
    const helper = artifacts.getCfg(@intFromEnum(tree.rootDecls()[0])) orelse
        return error.TestUnexpectedResult;
    try std.testing.expectEqualStrings("helper", helper.fn_name.?);
    try std.testing.expectEqual(@import("cfg.zig").IrTag.fn_exit, helper.getNode(helper.exit).?.ir_node.tag);
    try std.testing.expect(types.isDeclFunction("foo"));
}

test "AnalysisCache excludes checked-out leases and retains only one result per key" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "nested.zig", "fn foo() void {}");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    var stats: checker_mod.AnalysisStats = .{};
    const context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .cached_artifacts = &artifacts,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    const retained_engine = nested_run: {
        var first = try context.getOrAnalyze(allocator, &source, &cfg, "first", .configured);
        defer first.deinit();
        var nested = try context.getOrAnalyze(allocator, &source, &cfg, "nested", .configured);
        defer nested.deinit();
        try std.testing.expect(first.engine != nested.engine);
        try expectSameGraph(first.engine, nested.engine);
        try std.testing.expectEqual(@as(usize, 0), cache.retained_bytes);
        break :nested_run nested.engine;
    };
    try std.testing.expectEqual(@as(usize, 1), cache.entry_count);
    var hit = try context.getOrAnalyze(allocator, &source, &cfg, "hit", .configured);
    defer hit.deinit();
    try std.testing.expect(hit.engine == retained_engine);
    try std.testing.expectEqual(@as(usize, 0), cache.retained_bytes);
    try std.testing.expectEqual(@as(u64, 2), stats.total_runs);
}

test "AnalysisCache charges lazy query growth when a lease returns" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "lazy.zig", "fn foo() void {}");
    defer source.deinit();
    var foreign_source = Source.init(allocator, "foreign.zig", "fn query() void {}");
    defer foreign_source.deinit();
    const foreign_tree = try foreign_source.ast();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var cache_memory = CountingAllocator.init(allocator);
    var cache = AnalysisCache.init(cache_memory.allocator());
    defer cache.deinit();
    var stats: checker_mod.AnalysisStats = .{};
    const context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .cached_artifacts = &artifacts,
        .analysis_cache = &cache,
        .analysis_stats = &stats,
    };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    {
        var first = try context.getOrAnalyze(allocator, &source, &cfg, "first", .configured);
        defer first.deinit();
        cache.byte_budget = first.entry.counting.live_bytes;
    }
    try std.testing.expectEqual(cache.byte_budget, cache.retained_bytes);
    {
        var hit = try context.getOrAnalyze(allocator, &source, &cfg, "hit", .configured);
        defer hit.deinit();
        try std.testing.expectEqual(@as(usize, 0), cache.retained_bytes);
        const parent_map = try hit.engine.getParentMap(foreign_tree);
        try std.testing.expectEqual(foreign_tree.nodes.len, parent_map.len);
        try std.testing.expect(hit.entry.counting.live_bytes > cache.byte_budget);
    }
    try std.testing.expectEqual(@as(u64, 1), stats.total_runs);
    try std.testing.expectEqual(@as(usize, 0), cache.entry_count);
    try std.testing.expectEqual(@as(usize, 0), cache.retained_bytes);
    try std.testing.expectEqual(@as(usize, 0), cache_memory.live_bytes);
    {
        var rerun = try context.getOrAnalyze(allocator, &source, &cfg, "rerun", .configured);
        defer rerun.deinit();
        try std.testing.expect(rerun.complete);
        _ = try rerun.engine.getParentMap(foreign_tree);
    }
    try std.testing.expectEqual(@as(u64, 2), stats.total_runs);
    try std.testing.expectEqual(@as(usize, 0), cache.entry_count);
    try std.testing.expectEqual(@as(usize, 0), cache_memory.live_bytes);
}

test "AnalysisCache cleans entry and engine allocation failures" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "oom.zig", "fn foo() void {}");
    defer source.deinit();
    var artifacts = checker_mod.CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    const context: checker_mod.CheckerContext = .{ .build_metadata = null, .cached_artifacts = &artifacts };
    var cfg = try buildTestCfg(&source, context);
    defer cfg.deinit();
    var baseline = std.testing.FailingAllocator.init(allocator, .{});
    try exerciseAllocationFailure(baseline.allocator(), &source, &cfg, &artifacts);
    try std.testing.expectEqual(baseline.allocated_bytes, baseline.freed_bytes);
    for (0..baseline.alloc_index) |fail_index| {
        var failing = std.testing.FailingAllocator.init(allocator, .{ .fail_index = fail_index });
        exerciseAllocationFailure(failing.allocator(), &source, &cfg, &artifacts) catch |err| switch (err) {
            error.OutOfMemory => {},
            else => return err,
        };
        try std.testing.expect(failing.has_induced_failure);
        try std.testing.expectEqual(failing.allocated_bytes, failing.freed_bytes);
    }
}

fn exerciseAllocationFailure(
    allocator: std.mem.Allocator,
    source: *Source,
    cfg: *const checker_mod.CfgHandle,
    artifacts: *checker_mod.CachedArtifacts,
) !void {
    var cache = AnalysisCache.init(allocator);
    defer cache.deinit();
    const context: checker_mod.CheckerContext = .{
        .build_metadata = null,
        .cached_artifacts = artifacts,
        .analysis_cache = &cache,
    };
    var result = try context.getOrAnalyze(allocator, source, cfg, "oom", .configured);
    defer result.deinit();
    try std.testing.expect(result.complete);
    try std.testing.expectEqual(@as(usize, 4), result.engine.getGraph().nodeCount());
}

fn buildTestCfg(source: *Source, context: checker_mod.CheckerContext) !checker_mod.CfgHandle {
    const tree = try source.ast();
    const decls = tree.rootDecls();
    const fn_node = ids.astId(@intFromEnum(decls[decls.len - 1]));
    return (try context.getOrBuildCfg(std.testing.allocator, source, fn_node)) orelse
        error.TestUnexpectedResult;
}

fn expectSameGraph(expected: *const AnalysisEngine, actual: *const AnalysisEngine) !void {
    const expected_graph = expected.getGraph();
    const actual_graph = actual.getGraph();
    try std.testing.expectEqual(expected_graph.nodeCount(), actual_graph.nodeCount());
    for (expected_graph.nodes.items, actual_graph.nodes.items) |*left, *right| {
        try std.testing.expect(left.point.eql(right.point));
        try std.testing.expect(left.state.eql(&right.state));
        try std.testing.expectEqualSlices(u32, left.predecessors.items, right.predecessors.items);
        try std.testing.expectEqualSlices(u32, left.successors.items, right.successors.items);
    }
    try std.testing.expectEqual(expected.getPrunedPathCount(), actual.getPrunedPathCount());
}

fn hasViolation(engine: *const AnalysisEngine, kind: @import("engine/store.zig").StoreViolationKind) bool {
    for (engine.getGraph().nodes.items) |node| {
        for (node.state.getStoreViolations()) |violation| {
            if (violation.kind == kind) return true;
        }
    }
    return false;
}
