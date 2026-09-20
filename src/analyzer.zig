const std = @import("std");
const compat = @import("compat.zig");
const Rule = @import("rule.zig").Rule;
const Diagnostic = @import("rule.zig").Diagnostic;
const Source = @import("source.zig").Source;
const RuleFilter = @import("rule_filter.zig").RuleFilter;
const checker_mod = @import("checker.zig");
const Checker = checker_mod.Checker;
const CheckerManagerWithRules = checker_mod.CheckerManagerWithRules;
const TypeContext = checker_mod.TypeContext;
const AnalysisCache = @import("analysis_cache.zig").AnalysisCache;
const Config = checker_mod.Config;
pub const AnalysisResult = checker_mod.AnalysisResult;
pub const AnalysisStats = checker_mod.AnalysisStats;
const BuildMetadata = @import("build_metadata.zig").BuildMetadata;
const cache_mod = @import("cache.zig");
const Cache = cache_mod.Cache;
const CacheKey = cache_mod.CacheKey;
const cached_artifacts_mod = @import("cached_artifacts.zig");
const CachedArtifacts = cached_artifacts_mod.CachedArtifacts;
const ConsoleFormatter = @import("formatters/console.zig").ConsoleFormatter;
const SarifFormatter = @import("formatters/sarif.zig").SarifFormatter;
const log = std.log.scoped(.analyzer);
const diagnostic_mod = @import("diagnostic.zig");
const suppression = @import("suppression.zig");
const ProjectSources = @import("project_sources.zig").ProjectSources;
const project_unused_decl = @import("project_unused_decl.zig");
const DupeImportRule = @import("rules/dupe_import.zig").DupeImportRule;
const UnusedDeclRule = @import("rules/unused_decl.zig").UnusedDeclRule;
const OptionalUnwrapEngineChecker = @import("checkers/optional_unwrap_engine.zig").OptionalUnwrapEngineChecker;

pub const Analyzer = struct {
    allocator: std.mem.Allocator,
    checker_manager: CheckerManagerWithRules,
    diagnostics: std.ArrayList(Diagnostic),
    rule_filter: RuleFilter,
    tool_version: []const u8 = "unknown",
    build_metadata: ?BuildMetadata = null,
    cache: ?Cache = null,
    use_cache: bool = false,
    analysis_stats: checker_mod.AnalysisStats = .{},
    max_worklist_steps: ?usize = null,
    max_states_per_point: ?u32 = null,
    use_widening: ?bool = null,
    config: ?Config = null,
    dump_cfg_dir: ?[]const u8 = null,
    dump_exploded_graph_dir: ?[]const u8 = null,
    dump_annotated_cfg_dir: ?[]const u8 = null,
    dump_path_trace_dir: ?[]const u8 = null,
    io_context: ?*compat.Context = null,
    project_sources: ?ProjectSources = null,

    pub fn init(allocator: std.mem.Allocator) Analyzer {
        return Analyzer{
            .allocator = allocator,
            .checker_manager = CheckerManagerWithRules.init(allocator),
            .diagnostics = .empty,
            .rule_filter = .none,
        };
    }

    pub fn initWithContext(allocator: std.mem.Allocator, io_context: *compat.Context) Analyzer {
        var analyzer = init(allocator);
        analyzer.io_context = io_context;
        return analyzer;
    }

    pub fn setIoContext(self: *Analyzer, io_context: *compat.Context) void {
        self.io_context = io_context;
    }

    pub fn getIoContext(self: *Analyzer) *compat.Context {
        return self.io_context orelse compat.defaultContext();
    }

    pub fn deinit(self: *Analyzer) void {
        self.checker_manager.deinit();
        for (self.diagnostics.items) |*diag| {
            diag.deinit(self.allocator);
        }
        self.diagnostics.deinit(self.allocator);
        if (self.project_sources) |*project| {
            project.deinit();
            self.project_sources = null;
        }
        if (self.build_metadata) |*meta| {
            var meta_mut = meta.*;
            meta_mut.deinit(self.allocator);
        }
        if (self.cache) |*c| {
            c.deinit();
        }
    }

    /// Enable incremental caching.
    pub fn enableCache(self: *Analyzer) !void {
        self.use_cache = true;
        if (self.cache == null) {
            self.cache = try Cache.init(self.allocator, self.getIoContext());
        }
    }

    /// Register a legacy Rule with the analyzer.
    /// The rule will be wrapped and run through the CheckerManager.
    pub fn registerRule(self: *Analyzer, rule: *const Rule) !void {
        try self.checker_manager.registerRule(rule);
    }

    /// Register a new-style Checker with the analyzer.
    pub fn registerChecker(self: *Analyzer, chkr: *const Checker) !void {
        try self.checker_manager.registerChecker(chkr);
    }

    pub fn setRuleFilter(self: *Analyzer, filter: RuleFilter) void {
        self.rule_filter = filter;
    }

    pub fn setToolVersion(self: *Analyzer, version: []const u8) void {
        self.tool_version = version;
    }

    pub fn setBuildMetadata(self: *Analyzer, metadata: BuildMetadata) !void {
        if (self.build_metadata) |*meta| {
            var meta_mut = meta.*;
            meta_mut.deinit(self.allocator);
        }
        self.build_metadata = try metadata.clone(self.allocator);
    }

    pub fn setMaxWorklistSteps(self: *Analyzer, steps: usize) void {
        self.max_worklist_steps = steps;
    }

    pub fn setMaxStatesPerPoint(self: *Analyzer, max: u32) void {
        self.max_states_per_point = max;
    }

    pub fn setUseWidening(self: *Analyzer, use_w: bool) void {
        self.use_widening = use_w;
    }

    pub fn setDumpCfgDir(self: *Analyzer, dir: []const u8) void {
        self.dump_cfg_dir = dir;
    }

    pub fn setDumpExplodedGraphDir(self: *Analyzer, dir: []const u8) void {
        self.dump_exploded_graph_dir = dir;
    }

    pub fn setDumpAnnotatedCfgDir(self: *Analyzer, dir: []const u8) void {
        self.dump_annotated_cfg_dir = dir;
    }

    pub fn setDumpPathTraceDir(self: *Analyzer, dir: []const u8) void {
        self.dump_path_trace_dir = dir;
    }

    /// Set the config for resource models and other settings.
    pub fn setConfig(self: *Analyzer, cfg: Config) void {
        self.config = cfg;
    }

    /// Get the config if set.
    pub fn getConfig(self: *const Analyzer) ?*const Config {
        if (self.config) |*cfg| {
            return cfg;
        }
        return null;
    }

    pub fn getBuildMetadata(self: *const Analyzer) ?*const BuildMetadata {
        if (self.build_metadata) |*meta| {
            return meta;
        }
        return null;
    }

    pub fn logAnalysisStats(self: *const Analyzer) void {
        if (self.analysis_stats.widened_nodes > 0 or self.analysis_stats.widening_converged > 0) {
            log.info("widening: {d} node(s) widened, {d} converged across {d} engine run(s)", .{
                self.analysis_stats.widened_nodes,
                self.analysis_stats.widening_converged,
                self.analysis_stats.total_runs,
            });
        }
    }

    pub fn isRuleEnabled(self: *const Analyzer, rule_name: []const u8) bool {
        switch (self.rule_filter) {
            .none => return true,
            .allowlist => |list| {
                return containsRuleName(list, rule_name);
            },
            .blocklist => |list| {
                for (list) |blocked| {
                    if (std.mem.eql(u8, rule_name, blocked)) {
                        return false;
                    }
                }
                return true;
            },
        }
    }

    fn containsRuleName(list: []const []const u8, rule_name: []const u8) bool {
        for (list) |item| {
            if (std.mem.eql(u8, rule_name, item)) return true;
        }
        return false;
    }

    fn ruleNameLess(a: []const u8, b: []const u8) bool {
        const min_len = if (a.len < b.len) a.len else b.len;
        var i: usize = 0;
        while (i < min_len) : (i += 1) {
            if (a[i] < b[i]) return true;
            if (a[i] > b[i]) return false;
        }
        return a.len < b.len;
    }

    fn sortRuleNames(names: [][]const u8) void {
        var i: usize = 0;
        while (i < names.len) : (i += 1) {
            var j: usize = i + 1;
            while (j < names.len) : (j += 1) {
                if (ruleNameLess(names[j], names[i])) {
                    const tmp = names[i];
                    names[i] = names[j];
                    names[j] = tmp;
                }
            }
        }
    }

    fn needsTypeInformation(self: *const Analyzer) bool {
        for (self.checker_manager.checkers.items) |chkr| {
            if (self.isRuleEnabled(chkr.name) and chkr.type_requirement != .none) return true;
        }
        return false;
    }

    pub fn prepareProject(self: *Analyzer, files: []const []const u8) !void {
        if (self.project_sources) |*project| {
            project.deinit();
            self.project_sources = null;
        }
        if (!self.needsTypeInformation() and !self.shouldRunProjectUnusedDecls()) return;
        self.project_sources = try ProjectSources.init(
            self.getIoContext(),
            self.allocator,
            files,
        );
    }

    pub fn shouldRunProjectUnusedDecls(self: *const Analyzer) bool {
        if (!self.isRuleEnabled("unused-decl")) return false;
        for (self.checker_manager.adapted_rules.items) |rule| {
            if (std.mem.eql(u8, rule.name, "unused-decl")) return true;
        }
        return false;
    }

    pub fn analyzeProjectUnusedDecls(self: *Analyzer) !void {
        if (!self.shouldRunProjectUnusedDecls()) return;
        if (self.project_sources) |*project| {
            try project_unused_decl.analyze(project, self.allocator, &self.diagnostics);
        } else {
            return error.ProjectNotPrepared;
        }
        std.mem.sort(Diagnostic, self.diagnostics.items, {}, Diagnostic.lessThan);
    }

    pub fn analyzeFile(self: *Analyzer, file_path: []const u8) !void {
        var result = try self.analyzeFileResult(file_path);
        errdefer result.deinit(self.allocator);
        try self.mergeResult(&result);
    }

    pub fn mergeResult(self: *Analyzer, result: *AnalysisResult) !void {
        // Reserve before changing statistics or transferring diagnostic ownership.
        // On allocation failure the caller can retry or free the unchanged result.
        try self.diagnostics.ensureUnusedCapacity(self.allocator, result.diagnostics.items.len);
        self.analysis_stats.merge(result.stats);
        for (result.diagnostics.items) |diag| {
            self.diagnostics.appendAssumeCapacity(diag);
        }
        // Only free the backing array, not the diagnostics (now owned by self)
        result.diagnostics.deinit(self.allocator);
        result.diagnostics = .empty;
    }

    /// Analyze a single file and return an isolated AnalysisResult.
    /// This method does not mutate any shared state in the Analyzer,
    /// making it safe to call in parallel (once thread-safety is added).
    pub fn analyzeFileResult(self: *Analyzer, file_path: []const u8) !AnalysisResult {
        return self.analyzeFileResultWithScratchAllocator(file_path, self.allocator);
    }

    /// Analyze a single file using a scratch allocator for temporary data.
    /// The scratch_allocator is used for heavy temporary allocations (file content,
    /// AST parsing, etc.) while self.allocator is used for persistent data like
    /// diagnostic strings. This enables efficient parallel analysis by allowing
    /// each worker thread to use its own arena allocator for scratch memory.
    pub fn analyzeFileResultWithScratchAllocator(
        self: *Analyzer,
        file_path: []const u8,
        scratch_allocator: std.mem.Allocator,
    ) !AnalysisResult {
        log.debug("analyzeResult: start {s}", .{file_path});

        var owned_content: ?[:0]u8 = null;
        defer if (owned_content) |content| {
            scratch_allocator.free(content.ptr[0 .. content.len + 1]);
        };

        const registered_source = if (self.project_sources) |*project|
            project.sourceForPath(file_path)
        else
            null;
        var source = if (registered_source) |parsed| blk: {
            break :blk Source.initParsed(scratch_allocator, parsed.path, parsed.tree);
        } else blk: {
            // Sentinel needed for Source.init; free accounts for sentinel byte below.
            // zwanzig-disable-next-line: sentinel-alloc
            const content = try compat.readFileAlloc(
                self.getIoContext(),
                scratch_allocator,
                file_path,
                10 * 1024 * 1024,
            );
            owned_content = content;
            break :blk Source.init(scratch_allocator, file_path, content);
        };
        defer source.deinit();
        const content = source.getContent();
        var result = AnalysisResult.init();
        errdefer result.deinit(self.allocator);

        const tree = try source.ast();
        if (tree.errors.len != 0) {
            try appendParseErrors(&source, tree, self.allocator, &result.diagnostics);
            return result;
        }

        const type_info_available = if (self.needsTypeInformation()) available: {
            _ = source.requireZirBridge() catch |err| {
                if (err == error.OutOfMemory) return err;
                break :available false;
            };
            break :available true;
        } else false;

        var cached_artifacts: ?CachedArtifacts = null;
        defer if (cached_artifacts) |*ca| ca.deinit();

        var cache_key: ?CacheKey = null;
        var enabled_rules_buf: std.ArrayList([]const u8) = .empty;
        defer enabled_rules_buf.deinit(scratch_allocator);

        if (self.use_cache) {
            for (self.checker_manager.checkers.items) |chkr| {
                if (self.isRuleEnabled(chkr.name)) {
                    try enabled_rules_buf.append(scratch_allocator, chkr.name);
                }
            }
            for (self.checker_manager.adapted_rules.items) |rule| {
                if (self.isRuleEnabled(rule.name)) {
                    try enabled_rules_buf.append(scratch_allocator, rule.name);
                }
            }

            sortRuleNames(enabled_rules_buf.items);
            const project_fingerprint = if (self.project_sources) |*project|
                project.fingerprint()
            else
                null;
            const key = CacheKey.init(
                content,
                self.getBuildMetadata(),
                self.tool_version,
                type_info_available,
                enabled_rules_buf.items,
                project_fingerprint,
            );
            cache_key = key;
            if (self.cache) |*c| {
                if (try c.get(key)) |cached_data| {
                    defer self.allocator.free(cached_data);
                    log.debug("analyzeResult: cache hit {s}, loading artifacts", .{file_path});

                    cached_artifacts = CachedArtifacts.deserialize(scratch_allocator, cached_data) catch |err| blk: {
                        log.debug("analyzeResult: failed to deserialize cached artifacts: {}", .{err});
                        break :blk null;
                    };
                }
            }
        }

        if (cached_artifacts == null) {
            cached_artifacts = CachedArtifacts.init(scratch_allocator);
            if (cached_artifacts) |*artifacts| {
                artifacts.had_type_info = type_info_available;
            }
        }

        // Use a temporary list for diagnostics created with scratch allocator
        var scratch_diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            // Free diagnostic messages before freeing the list
            for (scratch_diagnostics.items) |*diag| {
                diag.deinit(scratch_allocator);
            }
            scratch_diagnostics.deinit(scratch_allocator);
        }

        if (cached_artifacts) |*artifacts| {
            try self.runChecksOnSource(&source, scratch_allocator, artifacts, &scratch_diagnostics, &result.stats);
        }

        try filterDiagnosticsWithSuppressions(scratch_allocator, content, &scratch_diagnostics);

        // Transfer diagnostics from scratch allocator to persistent allocator
        for (scratch_diagnostics.items) |diag| {
            var cloned = try diag.clone(self.allocator);
            errdefer cloned.deinit(self.allocator);
            try result.diagnostics.append(self.allocator, cloned);
        }

        if (self.use_cache and cache_key != null) {
            if (self.cache) |*c| {
                if (cached_artifacts) |*artifacts| {
                    const serialized = artifacts.serialize(scratch_allocator) catch |err| {
                        log.debug("analyzeResult: failed to serialize artifacts: {}", .{err});
                        return result;
                    };
                    defer scratch_allocator.free(serialized);

                    c.put(cache_key.?, serialized) catch |err| {
                        log.debug("analyzeResult: failed to cache artifacts: {}", .{err});
                    };
                }
            }
        }

        log.debug("analyzeResult: done {s}", .{file_path});
        return result;
    }

    fn appendParseErrors(
        source: *Source,
        tree: *const std.zig.Ast,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
    ) !void {
        var message: std.Io.Writer.Allocating = .init(allocator);
        defer message.deinit();
        for (tree.errors) |parse_error| {
            message.writer.end = 0;
            tree.renderError(parse_error, &message.writer) catch return error.OutOfMemory;
            const offset = tree.tokens.items(.start)[parse_error.token] + tree.errorOffset(parse_error);
            const location = try source.byteToLocation(offset);
            var diagnostic = try Diagnostic.initAtLocation(
                allocator,
                source.getFilePath(),
                "parse-error",
                if (parse_error.is_note) .hint else .err,
                message.written(),
                location.line,
                location.column,
            );
            errdefer diagnostic.deinit(allocator);
            try diagnostics.append(allocator, diagnostic);
        }
    }

    /// Filter suppressed diagnostics in a standalone list.
    fn filterDiagnosticsWithSuppressions(
        allocator: std.mem.Allocator,
        content: []const u8,
        diagnostics: *std.ArrayList(Diagnostic),
    ) !void {
        var sup_map = try suppression.parseSuppressions(allocator, content);
        defer sup_map.deinit();

        var write_index: usize = 0;
        for (diagnostics.items) |*diag| {
            if (!sup_map.isSuppressed(diag.range.start.line, diag.rule_id)) {
                diagnostics.items[write_index] = diag.*;
                write_index += 1;
            } else {
                diag.deinit(allocator);
            }
        }
        diagnostics.shrinkRetainingCapacity(write_index);
    }

    /// Internal method to run checks on a source with the analyzer's filter.
    /// Accepts explicit diagnostics and stats parameters for isolation.
    /// The scratch_allocator is used for temporary allocations during analysis.
    fn runChecksOnSource(
        self: *Analyzer,
        source: *Source,
        scratch_allocator: std.mem.Allocator,
        cached_artifacts: *CachedArtifacts,
        diagnostics: *std.ArrayList(Diagnostic),
        analysis_stats: *checker_mod.AnalysisStats,
    ) !void {
        var type_ctx: ?TypeContext = if (self.needsTypeInformation())
            TypeContext.init(scratch_allocator, source)
        else
            null;
        defer if (type_ctx) |*ctx| ctx.deinit();

        var types_available = false;
        if (type_ctx) |*ctx| {
            if (self.project_sources) |*project| {
                ctx.project_resolver = project.resolverForPath(source.getFilePath());
            }
            types_available = available: {
                ctx.ensureAvailable() catch |err| {
                    if (err == error.OutOfMemory) return err;
                    const message = try std.fmt.allocPrint(
                        scratch_allocator,
                        "Type information is unavailable with embedded Zig {s}: {s}. " ++
                            "Required typed checks are skipped; optional checks use AST fallback.",
                        .{ @import("builtin").zig_version_string, @errorName(err) },
                    );
                    defer scratch_allocator.free(message);
                    var diagnostic = try Diagnostic.initAtLocation(
                        scratch_allocator,
                        source.getFilePath(),
                        "frontend-error",
                        .err,
                        message,
                        1,
                        1,
                    );
                    errdefer diagnostic.deinit(scratch_allocator);
                    try diagnostics.append(scratch_allocator, diagnostic);
                    break :available false;
                };
                break :available true;
            };

            var builder = checker_mod.CfgBuilder.initWithTypes(scratch_allocator, ctx);
            var cfgs = cached_artifacts.cfgs.valueIterator();
            while (cfgs.next()) |cfg| {
                checker_mod.CfgBuilder.TypeAnnotation.restoreDeclarationTypes(&builder, cfg.*, source);
            }
        }

        // Cached engines borrow the context and CFGs, so they must be released first.
        var analysis_cache = AnalysisCache.init(scratch_allocator);
        defer analysis_cache.deinit();

        const context = checker_mod.CheckerContext{
            .build_metadata = self.getBuildMetadata(),
            .type_context = if (type_ctx) |*ctx| ctx else null,
            .analysis_cache = &analysis_cache,
            .analysis_stats = analysis_stats,
            .analysis_limits = .{
                .max_worklist_steps = self.max_worklist_steps,
                .max_states_per_point = self.max_states_per_point,
                .use_widening = self.use_widening,
            },
            .config = self.getConfig(),
            .cached_artifacts = cached_artifacts,
            .dump_cfg_dir = self.dump_cfg_dir,
            .dump_exploded_graph_dir = self.dump_exploded_graph_dir,
            .dump_annotated_cfg_dir = self.dump_annotated_cfg_dir,
            .dump_path_trace_dir = self.dump_path_trace_dir,
            .io_context = self.getIoContext(),
        };

        // Run native checkers with one annotation mode for the shared CFG artifacts.
        for (self.checker_manager.checkers.items) |chkr| {
            if (self.isRuleEnabled(chkr.name)) {
                if (chkr.type_requirement == .required and !types_available) continue;
                log.debug("checker: start {s} ({s})", .{ source.getFilePath(), chkr.name });
                try chkr.checkAst(source, scratch_allocator, diagnostics, context);
                log.debug("checker: done {s} ({s})", .{ source.getFilePath(), chkr.name });
            }
        }

        // Run adapted rules
        for (self.checker_manager.adapted_rules.items) |rule| {
            if (self.isRuleEnabled(rule.name)) {
                log.debug("rule: start {s} ({s})", .{ source.getFilePath(), rule.name });
                try rule.check(source, scratch_allocator, diagnostics);
                log.debug("rule: done {s} ({s})", .{ source.getFilePath(), rule.name });
            }
        }
    }

    pub const OutputFormat = enum {
        text,
        json,
        sarif,
    };

    pub fn printResults(self: *Analyzer, format: OutputFormat) !void {
        var stdout: compat.OutputWriter = undefined;
        stdout.init(self.getIoContext(), false);
        defer stdout.deinit();
        const writer = stdout.writer();

        switch (format) {
            .json => try self.printJsonResults(writer),
            .text => {
                var formatter = ConsoleFormatter.init(self.allocator, self.getIoContext());
                try formatter.write(writer, self.diagnostics.items);
            },
            .sarif => {
                var formatter = SarifFormatter.init(
                    self.allocator,
                    &self.checker_manager,
                    self.tool_version,
                    self.diagnostics.items,
                );
                try formatter.write(writer);
            },
        }
        try stdout.flush();
    }

    fn printJsonResults(self: *Analyzer, writer: *std.Io.Writer) !void {
        var alloc_writer: std.Io.Writer.Allocating = .init(self.allocator);
        defer alloc_writer.deinit();

        var jw: std.json.Stringify = .{
            .writer = &alloc_writer.writer,
            .options = .{ .whitespace = .indent_2 },
        };

        try jw.beginObject();
        try jw.objectField("diagnostics");
        try jw.beginArray();
        for (self.diagnostics.items) |diag| {
            try diag.writeJsonValue(&jw);
        }
        try jw.endArray();
        try jw.objectField("total");
        try jw.write(self.diagnostics.items.len);
        try jw.endObject();

        try writer.writeAll(alloc_writer.written());
        try writer.writeByte('\n');
    }

    pub fn hasDiagnostics(self: *Analyzer) bool {
        return self.diagnostics.items.len > 0;
    }

    /// Get the total number of registered checkers and rules.
    pub fn totalCheckerCount(self: *const Analyzer) usize {
        return self.checker_manager.totalCount();
    }
};

test "Analyzer JSON output format" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const diagnostic = diagnostic_mod;
    const Location = diagnostic.Location;
    const SourceRange = diagnostic.SourceRange;

    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();

    const diag1 = try Diagnostic.init(
        allocator,
        "test1.zig",
        "test-rule",
        .err,
        "Test error",
        SourceRange.init(Location.init(1, 1), Location.init(1, 5)),
    );

    const diag2 = try Diagnostic.init(
        allocator,
        "test2.zig",
        "other-rule",
        .warning,
        "Test warning",
        SourceRange.init(Location.init(2, 3), Location.init(2, 8)),
    );

    try analyzer.diagnostics.append(allocator, diag1);
    try analyzer.diagnostics.append(allocator, diag2);

    var buffer: [1024]u8 = undefined;
    var writer: std.Io.Writer = .fixed(&buffer);
    try analyzer.printJsonResults(&writer);

    const output = writer.buffered();
    try testing.expect(std.mem.indexOf(u8, output, "\"diagnostics\":") != null);
    try testing.expect(std.mem.indexOf(u8, output, "\"total\": 2") != null);
    try testing.expect(std.mem.indexOf(u8, output, "test1.zig") != null);
    try testing.expect(std.mem.indexOf(u8, output, "test2.zig") != null);
    try testing.expect(std.mem.indexOf(u8, output, "test-rule") != null);
    try testing.expect(std.mem.indexOf(u8, output, "other-rule") != null);
}

test "Analyzer.isRuleEnabled: no filter" {
    const allocator = std.testing.allocator;
    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();

    try std.testing.expect(analyzer.isRuleEnabled("empty-catch"));
    try std.testing.expect(analyzer.isRuleEnabled("any-rule"));
}

test "Analyzer.isRuleEnabled: allowlist" {
    const allocator = std.testing.allocator;
    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();

    const allowlist = [_][]const u8{ "empty-catch", "unused-var" };
    analyzer.setRuleFilter(.{ .allowlist = &allowlist });

    try std.testing.expect(analyzer.isRuleEnabled("empty-catch"));
    try std.testing.expect(analyzer.isRuleEnabled("unused-var"));
    try std.testing.expect(!analyzer.isRuleEnabled("other-rule"));
}

test "Analyzer.isRuleEnabled: blocklist" {
    const allocator = std.testing.allocator;
    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();

    const blocklist = [_][]const u8{ "empty-catch", "unused-var" };
    analyzer.setRuleFilter(.{ .blocklist = &blocklist });

    try std.testing.expect(!analyzer.isRuleEnabled("empty-catch"));
    try std.testing.expect(!analyzer.isRuleEnabled("unused-var"));
    try std.testing.expect(analyzer.isRuleEnabled("other-rule"));
}

test "Analyzer.shouldRunProjectUnusedDecls requires registration and follows rule filter" {
    const allocator = std.testing.allocator;
    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();

    try std.testing.expect(!analyzer.shouldRunProjectUnusedDecls());
    try analyzer.registerRule(&UnusedDeclRule.rule);
    try std.testing.expect(analyzer.shouldRunProjectUnusedDecls());

    const allowlist = [_][]const u8{"todo"};
    analyzer.setRuleFilter(.{ .allowlist = &allowlist });
    try std.testing.expect(!analyzer.shouldRunProjectUnusedDecls());

    const project_allowlist = [_][]const u8{"unused-decl"};
    analyzer.setRuleFilter(.{ .allowlist = &project_allowlist });
    try std.testing.expect(analyzer.shouldRunProjectUnusedDecls());

    const blocklist = [_][]const u8{"unused-decl"};
    analyzer.setRuleFilter(.{ .blocklist = &blocklist });
    try std.testing.expect(!analyzer.shouldRunProjectUnusedDecls());
}

test "Analyzer text output format" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const diagnostic = diagnostic_mod;
    const Location = diagnostic.Location;
    const SourceRange = diagnostic.SourceRange;

    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();

    const diag = try Diagnostic.init(
        allocator,
        "test.zig",
        "test-rule",
        .err,
        "Test error",
        SourceRange.init(Location.init(1, 1), Location.init(1, 5)),
    );

    try analyzer.diagnostics.append(allocator, diag);

    var buffer: [512]u8 = undefined;
    var writer: std.Io.Writer = .fixed(&buffer);
    var formatter = ConsoleFormatter.init(allocator, analyzer.getIoContext());
    try formatter.write(&writer, analyzer.diagnostics.items);

    const output = writer.buffered();
    try testing.expect(std.mem.indexOf(u8, output, "Found 1 issue(s):") != null);
    try testing.expect(std.mem.indexOf(u8, output, "test.zig:1:1") != null);
}

test "Analyzer SARIF output format" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const diagnostic = diagnostic_mod;
    const Location = diagnostic.Location;
    const SourceRange = diagnostic.SourceRange;

    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();

    const diag1 = try Diagnostic.init(
        allocator,
        "test1.zig",
        "test-rule",
        .err,
        "Test error",
        SourceRange.init(Location.init(1, 1), Location.init(1, 5)),
    );

    const diag2 = try Diagnostic.init(
        allocator,
        "test2.zig",
        "other-rule",
        .warning,
        "Test warning",
        SourceRange.init(Location.init(2, 3), Location.init(2, 8)),
    );

    try analyzer.diagnostics.append(allocator, diag1);
    try analyzer.diagnostics.append(allocator, diag2);

    var output: std.Io.Writer.Allocating = .init(allocator);
    defer output.deinit();
    var formatter = SarifFormatter.init(allocator, &analyzer.checker_manager, analyzer.tool_version, analyzer.diagnostics.items);
    try formatter.write(&output.writer);

    const result = output.written();
    try testing.expect(std.mem.indexOf(u8, result, "\"version\": \"2.1.0\"") != null);
    try testing.expect(std.mem.indexOf(u8, result, "\"$schema\":") != null);
    try testing.expect(std.mem.indexOf(u8, result, "\"runs\":") != null);
    try testing.expect(std.mem.indexOf(u8, result, "\"tool\":") != null);
    try testing.expect(std.mem.indexOf(u8, result, "\"driver\":") != null);
    try testing.expect(std.mem.indexOf(u8, result, "\"name\": \"Zwanzig\"") != null);
    try testing.expect(std.mem.indexOf(u8, result, "\"rules\":") != null);
    try testing.expect(std.mem.indexOf(u8, result, "\"results\":") != null);
    try testing.expect(std.mem.indexOf(u8, result, "test1.zig") != null);
    try testing.expect(std.mem.indexOf(u8, result, "test2.zig") != null);
    try testing.expect(std.mem.indexOf(u8, result, "test-rule") != null);
    try testing.expect(std.mem.indexOf(u8, result, "other-rule") != null);
}

test "Analyzer cache enabled" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    try compat.makePath(&io_context, ".zwanzig-cache");
    defer compat.deleteTree(&io_context, ".zwanzig-cache") catch |err| {
        log.warn("failed to clean up test directory: {}", .{err});
    };

    var analyzer = Analyzer.initWithContext(allocator, &io_context);
    defer analyzer.deinit();

    try analyzer.enableCache();
    try testing.expect(analyzer.use_cache);
    try testing.expect(analyzer.cache != null);
}

test "Analyzer cache hit still produces diagnostics" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var tmp_dir = compat.TestDir.init();
    defer tmp_dir.cleanup();

    // File with duplicate imports to trigger a diagnostic
    const test_file_content =
        \\const std = @import("std");
        \\const std2 = @import("std");
    ;
    try tmp_dir.writeFile("test.zig", test_file_content);

    var path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const test_file_path = try std.fmt.bufPrint(&path_buf, "{s}/test.zig", .{tmp_dir.path()});

    var first_run_diag_count: usize = 0;

    // First run - populates cache
    {
        var analyzer1 = Analyzer.initWithContext(allocator, &io_context);
        defer analyzer1.deinit();
        try analyzer1.enableCache();
        try analyzer1.registerRule(&DupeImportRule.rule);

        try analyzer1.analyzeFile(test_file_path);
        first_run_diag_count = analyzer1.diagnostics.items.len;
        try testing.expect(first_run_diag_count > 0);
    }

    // Second run - should hit cache but still produce same diagnostics
    {
        var analyzer2 = Analyzer.initWithContext(allocator, &io_context);
        defer analyzer2.deinit();
        try analyzer2.enableCache();
        try analyzer2.registerRule(&DupeImportRule.rule);

        try analyzer2.analyzeFile(test_file_path);
        try testing.expectEqual(first_run_diag_count, analyzer2.diagnostics.items.len);
    }
}

test "Analyzer reports parse errors and continues valid project siblings" {
    const testing = std.testing;
    const allocator = testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();
    try temp_dir.writeFile("invalid.zig", "const broken = ;\n");
    try temp_dir.writeFile("valid.zig", "const first = @import(\"std\");\nconst second = @import(\"std\");\n");
    const invalid_path = try std.fmt.allocPrint(allocator, "{s}/invalid.zig", .{temp_dir.path()});
    defer allocator.free(invalid_path);
    const valid_path = try std.fmt.allocPrint(allocator, "{s}/valid.zig", .{temp_dir.path()});
    defer allocator.free(valid_path);
    var analyzer = Analyzer.initWithContext(allocator, &io_context);
    defer analyzer.deinit();
    try analyzer.registerRule(&DupeImportRule.rule);
    try analyzer.registerRule(&UnusedDeclRule.rule);
    try analyzer.prepareProject(&.{ invalid_path, valid_path });
    try analyzer.analyzeFile(invalid_path);
    try analyzer.analyzeFile(valid_path);
    try analyzer.analyzeProjectUnusedDecls();

    var parse_errors: usize = 0;
    var duplicate_imports: usize = 0;
    for (analyzer.diagnostics.items) |diagnostic| {
        if (std.mem.eql(u8, diagnostic.file_path, invalid_path)) {
            try testing.expectEqualStrings("parse-error", diagnostic.rule_id);
            try testing.expectEqual(@as(usize, 1), diagnostic.range.start.line);
            if (diagnostic.severity == .err) parse_errors += 1;
        }
        if (std.mem.eql(u8, diagnostic.rule_id, "dupe-import")) {
            try testing.expectEqualStrings(valid_path, diagnostic.file_path);
            duplicate_imports += 1;
        }
    }
    try testing.expect(parse_errors != 0);
    try testing.expectEqual(@as(usize, 1), duplicate_imports);
}

test "Analyzer gates frontend failures by checker type requirements" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const SyntaxChecker = @import("checkers/unreachable_code_checker.zig").UnreachableCodeChecker;
    const cases = [_]struct {
        requirement: checker_mod.TypeRequirement,
        frontend_failure: bool,
        reports_unreachable: bool,
    }{
        .{ .requirement = .optional, .frontend_failure = true, .reports_unreachable = true },
        .{ .requirement = .required, .frontend_failure = true, .reports_unreachable = false },
        .{ .requirement = .required, .frontend_failure = false, .reports_unreachable = true },
    };
    for (cases) |case| {
        const code: [:0]const u8 = if (case.frontend_failure)
            "const x = @zwanzigUnsupportedBuiltin();\nfn foo() void { if (false) {} }"
        else
            "fn foo() void { if (false) {} }";
        var source = Source.init(allocator, "frontend.zig", code);
        defer source.deinit();
        var artifacts = CachedArtifacts.init(allocator);
        defer artifacts.deinit();
        var result = AnalysisResult.init();
        defer result.deinit(allocator);
        var checker = SyntaxChecker.checker;
        checker.type_requirement = case.requirement;
        var analyzer = Analyzer.init(allocator);
        defer analyzer.deinit();
        try analyzer.registerChecker(&checker);
        try analyzer.runChecksOnSource(&source, allocator, &artifacts, &result.diagnostics, &result.stats);

        var frontend_errors: usize = 0;
        var unreachable_reports: usize = 0;
        for (result.diagnostics.items) |diagnostic| {
            if (std.mem.eql(u8, diagnostic.rule_id, "frontend-error")) frontend_errors += 1;
            if (std.mem.eql(u8, diagnostic.rule_id, "unreachable-code-engine")) unreachable_reports += 1;
        }
        try testing.expectEqual(@as(usize, @intFromBool(case.frontend_failure)), frontend_errors);
        try testing.expectEqual(@as(usize, @intFromBool(case.reports_unreachable)), unreachable_reports);
    }
}

test "Analyzer disabled typed checkers leave AST-only CFG analysis lazy" {
    const testing = std.testing;
    const allocator = testing.allocator;
    var ast_only = OptionalUnwrapEngineChecker.checker;
    ast_only.type_requirement = .none;
    const disabled = Checker{ .name = "disabled-typed", .type_requirement = .required };
    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();
    try analyzer.registerChecker(&ast_only);
    try analyzer.registerChecker(&disabled);
    analyzer.setRuleFilter(.{ .allowlist = &.{"optional-unwrap"} });
    try analyzer.prepareProject(&.{"missing-file-must-not-be-read.zig"});
    try testing.expect(analyzer.project_sources == null);

    var source = Source.init(allocator, "ast-only.zig", "const Bad = @zwanzigUnsupportedBuiltin();\n" ++
        "fn foo() u8 { const value: ?u8 = null; return value.?; }");
    defer source.deinit();
    var artifacts = CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    var result = AnalysisResult.init();
    defer result.deinit(allocator);
    try analyzer.runChecksOnSource(&source, allocator, &artifacts, &result.diagnostics, &result.stats);
    try testing.expect(!source.zir_load_attempted);
    try testing.expectEqual(@as(usize, 1), result.diagnostics.items.len);
    try testing.expectEqualStrings("optional-unwrap", result.diagnostics.items[0].rule_id);
}

test "Analyzer failed diagnostic insertion releases its persistent clone" {
    const testing = std.testing;
    const allocator = testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();
    try temp_dir.writeFile("duplicate.zig", "const first = @import(\"std\");\nconst second = @import(\"std\");\n");
    const path = try std.fmt.allocPrint(allocator, "{s}/duplicate.zig", .{temp_dir.path()});
    defer allocator.free(path);
    var failing = testing.FailingAllocator.init(allocator, .{});
    var analyzer = Analyzer.initWithContext(failing.allocator(), &io_context);
    defer analyzer.deinit();
    try analyzer.registerRule(&DupeImportRule.rule);
    // Allow the message clone, then fail growth of the persistent diagnostic list.
    failing.fail_index = failing.alloc_index + 1;
    try testing.expectError(error.OutOfMemory, analyzer.analyzeFileResultWithScratchAllocator(path, allocator));
}

test "Analyzer.mergeResult preserves diagnostics and statistics on allocation failure" {
    const testing = std.testing;
    const allocator = testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();
    try temp_dir.writeFile("first.zig", "fn first() u8 { const value: ?u8 = null; return value.?; }\n");
    try temp_dir.writeFile("second.zig", "fn second() u8 { const value: ?u8 = null; return value.?; }\n");
    var first_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const first_path = try std.fmt.bufPrint(
        &first_path_buffer,
        "{s}/first.zig",
        .{temp_dir.path()},
    );
    var second_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const second_path = try std.fmt.bufPrint(
        &second_path_buffer,
        "{s}/second.zig",
        .{temp_dir.path()},
    );

    var failing = testing.FailingAllocator.init(allocator, .{ .resize_fail_index = 0 });
    {
        var analyzer = Analyzer.initWithContext(failing.allocator(), &io_context);
        defer analyzer.deinit();
        try analyzer.registerChecker(&OptionalUnwrapEngineChecker.checker);
        try analyzer.diagnostics.ensureTotalCapacityPrecise(analyzer.allocator, 1);
        var first = try analyzer.analyzeFileResultWithScratchAllocator(first_path, allocator);
        defer first.deinit(analyzer.allocator);
        var second = try analyzer.analyzeFileResultWithScratchAllocator(second_path, allocator);
        defer second.deinit(analyzer.allocator);
        try testing.expectEqual(@as(usize, 1), first.diagnostics.items.len);
        try testing.expectEqual(@as(usize, 1), second.diagnostics.items.len);
        try testing.expect(first.stats.total_runs > 0);
        try testing.expect(second.stats.total_runs > 0);
        const first_stats = first.stats;
        const second_stats = second.stats;
        var first_diagnostic = try first.diagnostics.items[0].clone(allocator);
        defer first_diagnostic.deinit(allocator);
        var second_diagnostic = try second.diagnostics.items[0].clone(allocator);
        defer second_diagnostic.deinit(allocator);

        try analyzer.mergeResult(&first);
        try testing.expectEqual(@as(usize, 0), first.diagnostics.items.len);
        try testing.expectEqualDeep(first_stats, first.stats);
        try testing.expectEqualDeep(first_stats, analyzer.analysis_stats);

        // Fail growth after one committed result; both owners must remain unchanged.
        failing.fail_index = failing.alloc_index;
        try testing.expectError(error.OutOfMemory, analyzer.mergeResult(&second));
        try testing.expect(failing.has_induced_failure);
        try testing.expectEqualDeep(first_stats, analyzer.analysis_stats);
        try testing.expectEqual(@as(usize, 1), analyzer.diagnostics.items.len);
        try testing.expectEqualDeep(first_diagnostic, analyzer.diagnostics.items[0]);
        try testing.expectEqual(@as(usize, 1), second.diagnostics.items.len);
        try testing.expectEqualDeep(second_diagnostic, second.diagnostics.items[0]);
        try testing.expectEqualDeep(second_stats, second.stats);

        failing.fail_index = std.math.maxInt(usize);
        try analyzer.mergeResult(&second);
        var expected_stats = first_stats;
        expected_stats.merge(second_stats);
        try testing.expectEqualDeep(expected_stats, analyzer.analysis_stats);
        try testing.expectEqualDeep(second_stats, second.stats);
        try testing.expectEqual(@as(usize, 0), second.diagnostics.items.len);
        try testing.expectEqual(@as(usize, 2), analyzer.diagnostics.items.len);
        try testing.expectEqualDeep(first_diagnostic, analyzer.diagnostics.items[0]);
        try testing.expectEqualDeep(second_diagnostic, analyzer.diagnostics.items[1]);
    }
    try testing.expectEqual(failing.allocated_bytes, failing.freed_bytes);
}

test "Analyzer restores cached declaration types from the live source" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const Cfg = checker_mod.Cfg;
    const CfgBuilder = checker_mod.CfgBuilder;
    const IrNode = @import("cfg.zig").IrNode;
    const TypeInfo = checker_mod.TypeInfo;
    const content: [:0]const u8 = "const data: []const u8 = \"hello\";";
    var cold_source = Source.init(allocator, "types.zig", content);
    defer cold_source.deinit();
    var cold_types = TypeContext.init(allocator, &cold_source);
    defer cold_types.deinit();
    try cold_types.ensureAvailable();
    const cold_tree = try cold_source.ast();
    const declaration: u32 = @intFromEnum(cold_tree.rootDecls()[0]);
    var builder = CfgBuilder.initWithTypes(allocator, &cold_types);
    var cold_artifacts = CachedArtifacts.init(allocator);
    defer cold_artifacts.deinit();
    const cold_cfg = owned: {
        const cfg = try allocator.create(Cfg);
        cfg.* = Cfg.init(allocator);
        errdefer {
            cfg.deinit();
            allocator.destroy(cfg);
        }
        cfg.entry = try cfg.addNode(IrNode.init(.fn_entry));
        _ = try cfg.addNode(CfgBuilder.TypeAnnotation.annotateWithType(
            &builder,
            IrNode.initWithAst(.var_decl, declaration),
            &cold_source,
            declaration,
        ));
        _ = try cfg.addNode(IrNode.initWithAst(.try_expr, declaration).withType(TypeInfo.initErrorUnion()));
        _ = try cfg.addNode(IrNode.initWithAst(.catch_expr, declaration).withType(TypeInfo.initErrorUnion()));
        cfg.exit = try cfg.addNode(IrNode.init(.fn_exit));
        try cold_artifacts.addCfg(declaration, cfg);
        break :owned cfg;
    };
    const cold_type = cold_cfg.nodes.items[1].ir_node.type_info orelse return error.TestUnexpectedResult;
    try testing.expectEqual(TypeInfo.TypeKind.slice, cold_type.kind);
    try testing.expect(cold_type.payload_node != null);
    const encoded = try cold_artifacts.serialize(allocator);
    defer allocator.free(encoded);

    var warm_source = Source.init(allocator, "types.zig", content);
    defer warm_source.deinit();
    var warm_artifacts = try CachedArtifacts.deserialize(allocator, encoded);
    defer warm_artifacts.deinit();
    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();
    try analyzer.registerChecker(&OptionalUnwrapEngineChecker.checker);
    var result = AnalysisResult.init();
    defer result.deinit(allocator);
    try analyzer.runChecksOnSource(&warm_source, allocator, &warm_artifacts, &result.diagnostics, &result.stats);
    const warm_cfg = warm_artifacts.getCfg(declaration) orelse return error.TestUnexpectedResult;
    const warm_type = warm_cfg.nodes.items[1].ir_node.type_info orelse return error.TestUnexpectedResult;
    var expected = cold_type;
    expected.type_ast = try warm_source.ast();
    try testing.expectEqualDeep(expected.type_str, warm_type.type_str);
    expected.type_str = warm_type.type_str;
    try testing.expectEqual(expected, warm_type);
    try testing.expect(warm_type.type_ast.? != cold_type.type_ast.?);
    try testing.expectEqual(TypeInfo.TypeKind.error_union, warm_cfg.nodes.items[2].ir_node.type_info.?.kind);
    try testing.expectEqual(TypeInfo.TypeKind.error_union, warm_cfg.nodes.items[3].ir_node.type_info.?.kind);
}

test "Analyzer project cache invalidates imported source changes" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var tmp_dir = compat.TestDir.init();
    defer tmp_dir.cleanup();

    const main_content =
        \\const api = @import("api.zig");
        \\const State = struct { value: ?u8 };
        \\
        \\pub fn read() u8 {
        \\    var state: State = .{ .value = null };
        \\    state.value = api.make();
        \\    return state.value.?;
        \\}
    ;
    try tmp_dir.writeFile("main.zig", main_content);
    try tmp_dir.writeFile("api.zig", "pub fn make() u8 { return 1; }\n");

    var main_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const main_path = try std.fmt.bufPrint(
        &main_path_buf,
        "{s}/main.zig",
        .{tmp_dir.path()},
    );
    var api_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const api_path = try std.fmt.bufPrint(
        &api_path_buf,
        "{s}/api.zig",
        .{tmp_dir.path()},
    );
    var cache_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const cache_path = try std.fmt.bufPrint(
        &cache_path_buf,
        "{s}/cache",
        .{tmp_dir.path()},
    );
    const files = [_][]const u8{ main_path, api_path };

    {
        var analyzer = Analyzer.initWithContext(allocator, &io_context);
        defer analyzer.deinit();
        analyzer.cache = try Cache.initAt(allocator, &io_context, cache_path);
        analyzer.use_cache = true;
        try analyzer.registerChecker(&OptionalUnwrapEngineChecker.checker);
        try analyzer.prepareProject(&files);
        try analyzer.analyzeFile(main_path);
        try testing.expectEqual(@as(usize, 0), analyzer.diagnostics.items.len);
    }

    try tmp_dir.writeFile("api.zig", "pub fn make() ?u8 { return null; }\n");

    {
        var analyzer = Analyzer.initWithContext(allocator, &io_context);
        defer analyzer.deinit();
        analyzer.cache = try Cache.initAt(allocator, &io_context, cache_path);
        analyzer.use_cache = true;
        try analyzer.registerChecker(&OptionalUnwrapEngineChecker.checker);
        try analyzer.prepareProject(&files);
        try analyzer.analyzeFile(main_path);
        try testing.expectEqual(@as(usize, 1), analyzer.diagnostics.items.len);
        try testing.expectEqualStrings(
            "optional-unwrap",
            analyzer.diagnostics.items[0].rule_id,
        );
    }
}
