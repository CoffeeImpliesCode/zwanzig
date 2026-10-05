const std = @import("std");
const builtin = @import("builtin");
const compat = @import("../compat.zig");
const analyzer_mod = @import("../analyzer.zig");
const Diagnostic = @import("../diagnostic.zig").Diagnostic;
const file_discovery = @import("../file_discovery.zig");
const build_options = @import("build_options");
const config = @import("../config.zig");
const build_metadata = @import("../build_metadata.zig");
const args_mod = @import("args.zig");
const merge_mod = @import("config_merge.zig");
const registry = @import("registry.zig");

const Analyzer = analyzer_mod.Analyzer;
const AnalysisResult = analyzer_mod.AnalysisResult;
pub const CliArgs = args_mod.CliArgs;
const CliError = args_mod.CliError;
const BuildMetadata = build_metadata.BuildMetadata;
const MergedConfig = merge_mod.MergedConfig;
const TargetConfig = build_metadata.TargetConfig;
const log = std.log.scoped(.zwanzig);

/// The rule the tests below register to produce a known diagnostic. Imported
/// once at file scope because `dupe-import` is a rule this analyzer reports on
/// its own sources, so a second `@import` of the same module is itself a
/// duplicate.
const test_dupe_import = @import("../rules/dupe_import.zig");

const WorkerContext = struct {
    analyzer: *Analyzer,
    files: []const []const u8,
    results: []?AnalysisResult,
    errors: []?anyerror,
};

fn workerTask(file_index: usize, ctx: *WorkerContext) void {
    // Use libc's allocator for per-task scratch. The engine eagerly frees its
    // temporaries (~1M allocations per file on a 3500-line input), so an arena
    // ends up retaining all of that churn until file-end, which on
    // engine-heavy files inflates peak RSS by an order of magnitude. libc
    // malloc has thread-local caches, so per-task usage doesn't contend.
    const file_path = ctx.files[file_index];
    const result = ctx.analyzer.analyzeFileResultWithScratchAllocator(file_path, std.heap.c_allocator);
    if (result) |r| {
        ctx.results[file_index] = r;
        ctx.errors[file_index] = null;
    } else |err| {
        ctx.results[file_index] = null;
        ctx.errors[file_index] = err;
    }
}

fn workerTaskAdapter(file_index: usize, context: *anyopaque) void {
    const ctx: *WorkerContext = @ptrCast(@alignCast(context));
    workerTask(file_index, ctx);
}

/// What the parallel pass produced: the outcome of every file it was given.
/// A file that failed is carried here rather than raised as an error, because
/// an error returned before `printResults` throws away the findings from every
/// file that did analyze.
const FileAnalysis = struct {
    allocator: std.mem.Allocator,
    /// The analyzed files, borrowed from the caller.
    files: []const []const u8,
    /// Indexed like `files`: the error that file failed with, or null when it
    /// analyzed.
    errors: []?anyerror,

    fn deinit(self: FileAnalysis) void {
        self.allocator.free(self.errors);
    }

    /// Whether every file analyzed. False means the findings cover only part
    /// of the selection, which the run has to say out loud.
    fn isEmpty(self: FileAnalysis) bool {
        for (self.errors) |file_error| {
            if (file_error != null) return false;
        }
        return true;
    }

    /// How many files failed to analyze.
    fn failureCount(self: FileAnalysis) usize {
        var total: usize = 0;
        for (self.errors) |file_error| {
            if (file_error != null) total += 1;
        }
        return total;
    }
};

fn analyzeFilesParallel(
    analyzer: *Analyzer,
    files: []const []const u8,
    thread_count: usize,
    allocator: std.mem.Allocator,
    io_context: *compat.Context,
) !FileAnalysis {
    if (files.len == 0) {
        return .{
            .allocator = allocator,
            .files = files,
            .errors = try allocator.alloc(?anyerror, 0),
        };
    }

    const results = try allocator.alloc(?AnalysisResult, files.len);
    @memset(results, null);
    defer {
        // The executor's later defer drains tasks before these slots are inspected.
        for (results) |*slot| {
            if (slot.*) |*result| result.deinit(analyzer.allocator);
        }
        allocator.free(results);
    }

    const errors = try allocator.alloc(?anyerror, files.len);
    // Ownership passes to the caller, which reports the failures after the
    // report is printed; an error return here frees them instead.
    errdefer allocator.free(errors);
    @memset(errors, null);

    var ctx = WorkerContext{
        .analyzer = analyzer,
        .files = files,
        .results = results,
        .errors = errors,
    };

    var executor = try compat.Executor.init(io_context, allocator, thread_count);
    defer executor.deinit();

    for (0..files.len) |i| {
        try executor.spawn(workerTaskAdapter, i, @ptrCast(&ctx));
    }
    try executor.wait();

    // A worker records either a result or an error, never both, so merging
    // every result here keeps the findings of the files that analyzed without
    // waiting on the ones that did not.
    for (0..files.len) |i| {
        if (results[i]) |*result| try analyzer.mergeResult(result);
    }

    // Sort diagnostics for deterministic output ordering
    std.mem.sort(Diagnostic, analyzer.diagnostics.items, {}, Diagnostic.lessThan);

    return .{ .allocator = allocator, .files = files, .errors = errors };
}

/// One line per file whose analysis failed, naming the file and the error that
/// stopped it, so a report that is missing files says which ones.
fn writeFailureLines(
    writer: *std.Io.Writer,
    files: []const []const u8,
    analysis: FileAnalysis,
) !void {
    for (files, analysis.errors) |path, file_error| {
        const failure = file_error orelse continue;
        try writer.print("Error: Failed to analyze {s}: {s}\n", .{
            path,
            @errorName(failure),
        });
    }
}

/// Names the files the analysis could not read. Called after the report is
/// printed: a file that failed does not retract the findings from the files
/// that did analyze, but the run is not a complete analysis of the selection
/// and must not read as one.
fn reportFileFailures(
    io_context: *compat.Context,
    files: []const []const u8,
    analysis: FileAnalysis,
) void {
    var stderr: compat.OutputWriter = undefined;
    stderr.init(io_context, true);
    defer stderr.deinit();
    // Already an error path; a stderr that cannot be written must not replace
    // the reason with a crash or disturb the report already on stdout.
    // zwanzig-disable-next-line: empty-catch-engine
    _ = writeFailureLines(stderr.writer(), files, analysis) catch {};
    // zwanzig-disable-next-line: empty-catch-engine
    _ = stderr.flush() catch {};
}

/// Whether the run can be called a complete analysis of its selection. Both a
/// file that failed to analyze and a reported diagnostic make it incomplete,
/// and an incomplete run must exit non-zero even though it still printed a
/// report. Returned rather than exiting so both cases are testable.
fn runFails(analyzer: *Analyzer, analysis: FileAnalysis) bool {
    return !analysis.isEmpty() or analyzer.hasDiagnostics();
}

fn printUsage(io_context: *compat.Context) !void {
    var stdout: compat.OutputWriter = undefined;
    stdout.init(io_context, false);
    defer stdout.deinit();
    const writer = stdout.writer();
    try writer.writeAll("Usage: zwanzig [options] [path...]\n");
    try writer.writeAll("\nA static analyzer for Zig code.\n");
    try writer.writeAll("\nOptions:\n");
    try writer.writeAll("  -h, --help        Show this help message and exit\n");
    try writer.writeAll("  --version         Show version and exit\n");
    try writer.writeAll("  --file <path>     Specify a file or directory to analyze (can be repeated)\n");
    try writer.writeAll("  --do <rule>       Only run the specified rule (can be repeated)\n");
    try writer.writeAll("  --skip <rule>     Skip the specified rule (can be repeated)\n");
    try writer.writeAll("  --target <triple> Specify target triple (e.g., x86_64-linux-gnu)\n");
    try writer.writeAll("  --config <path>   Path to config file (default: .zwanzig.json)\n");
    try writer.writeAll("  --format <format> Output format: 'text', 'json', or 'sarif' (default: text)\n");
    try writer.writeAll("  --max-steps <n>   Max worklist steps per engine run\n");
    try writer.writeAll("  --max-states-per-point <n> Max unique states per CFG point\n");
    try writer.writeAll("  --use-widening    Enable widening for convergence (default: on)\n");
    try writer.writeAll("  --cache           Enable incremental caching\n");
    try writer.writeAll("  --threads <n>     Number of threads for parallel analysis (default: CPU count)\n");
    try writer.writeAll("  --dump-cfg <dir>  Dump CFG DOT files to directory for visualization\n");
    try writer.writeAll("  --dump-exploded-graph <dir>  Dump exploded graph (all states) as DOT\n");
    try writer.writeAll("  --dump-annotated-cfg <dir>   Dump CFG with state annotations as DOT\n");
    try writer.writeAll("  --dump-path-trace <dir>      Dump path traces to violations as DOT\n");
    try writer.writeAll("\n  Note: --do and --skip are mutually exclusive and override config file.\n");
    try writer.writeAll("\nArguments:\n");
    try writer.writeAll("  [path...]         Files or directories to analyze (default: current directory)\n");
    try writer.writeAll("\nIgnored directories (exact names, skipped while recursing):\n");
    try writer.writeAll("  zig-cache/, .zig-cache/, .zig-global-cache/, zig-out/, .zigmod/, .gyro/,\n");
    try writer.writeAll("  zig-pkg/, third_party/, .git/, .jj/\n");
    try writer.writeAll("  Other hidden directories are scanned. A path given on the command line or\n");
    try writer.writeAll("  with --file is always analyzed, even inside a skipped directory.\n");
    try stdout.flush();
}

fn printVersion(io_context: *compat.Context) !void {
    var buffer: [128]u8 = undefined;
    const message = try std.fmt.bufPrint(
        &buffer,
        "zwanzig {s} (Zig frontend {s})\n",
        .{ build_options.version, builtin.zig_version_string },
    );
    var stdout: compat.OutputWriter = undefined;
    stdout.init(io_context, false);
    defer stdout.deinit();
    try stdout.writer().writeAll(message);
    try stdout.flush();
}

fn writeError(io_context: *compat.Context, message: []const u8) void {
    var stderr: compat.OutputWriter = undefined;
    stderr.init(io_context, true);
    defer stderr.deinit();
    // This is already an error-reporting path; preserving the original error
    // is more useful than replacing it with a failure to write stderr.
    // Discarding each result through a binding settles the arm it decided. A
    // `catch` whose value nothing reads leaves that arm pending on every state
    // below it, so these two writes held four pending arms where one would do,
    // and a caller reaching this function from several places multiplied that
    // by one calling context each until a single point carried more states
    // than the engine's per-point budget allows.
    // zwanzig-disable-next-line: empty-catch-engine
    _ = stderr.writer().writeAll(message) catch {};
    // zwanzig-disable-next-line: empty-catch-engine
    _ = stderr.flush() catch {};
}

/// Which flag ended the run before any other argument was parsed.
const EarlyExit = enum { help, version };

/// The first argument that stops the run before parsing, or null when none
/// does. `--help` and `-h` print usage, `--version` prints the version, and
/// whichever of them comes first on the command line wins, so the scan stops
/// at the first match instead of looking for a preferred one.
fn findEarlyExit(args: []const []const u8) ?EarlyExit {
    for (args[1..]) |arg| {
        if (std.mem.eql(u8, arg, "--help") or std.mem.eql(u8, arg, "-h")) return .help;
        if (std.mem.eql(u8, arg, "--version")) return .version;
    }
    return null;
}

pub fn parseCliArgs(io_context: *compat.Context, allocator: std.mem.Allocator, args: []const []const u8) CliArgs {
    // `--help` and `--version` are answered before any other argument is
    // parsed, so the scan for them is a pass of its own and not a step of the
    // parse: a handler that only reports binds no value, and a `catch` in
    // statement position leaves the arm it decided pending on the states below
    // it. `writeError` says what that costs and settles its own arms.
    if (findEarlyExit(args)) |early_exit| {
        switch (early_exit) {
            .help => printUsage(io_context) catch |err| {
                std.debug.print("Failed to print usage: {s}\n", .{@errorName(err)});
            },
            .version => printVersion(io_context) catch |err| {
                std.debug.print("Failed to print version: {s}\n", .{@errorName(err)});
            },
        }
        std.process.exit(0);
    }

    return args_mod.parseArgs(allocator, args) catch |err| {
        // zwanzig-disable: empty-catch-engine
        // We are on an error-exit path; failing to write to stderr (e.g. closed
        // pipe) must not mask the original error or crash the process.
        // One call site reports the chosen text: a call per message gave the
        // engine a calling context per message to keep apart, so a state the
        // switch cannot tell apart was carried into the report once per
        // message.
        const message: []const u8 = switch (err) {
            CliError.MutuallyExclusiveFlags => "Error: --do and --skip are mutually exclusive\n",
            CliError.MissingFlagValue => "Error: Flag requires a value\n",
            CliError.OutOfMemory => "Error: Out of memory\n",
            CliError.InvalidTargetTriple => "Error: Invalid target triple format\n",
            CliError.InvalidOutputFormat => "Error: Invalid output format (use 'text', 'json', or 'sarif')\n",
            CliError.InvalidNumericValue => "Error: Invalid numeric value for limit\n",
            CliError.UnknownFlag => "Error: Unknown option. Options take a separate value " ++
                "(for example --format json); run 'zwanzig --help' for the full list.\n",
        };
        writeError(io_context, message);
        // zwanzig-enable: empty-catch-engine
        std.process.exit(1);
    };
}

/// A selection that resolves to no `.zig` files analyzed nothing at all. That
/// is not the same as analyzing code and finding nothing, so it is reported as
/// a failure instead of a clean run.
fn requireInputSelection(files: []const []const u8) error{NoInputFiles}!void {
    if (files.len == 0) return error.NoInputFiles;
}

fn loadMergedConfig(io_context: *compat.Context, allocator: std.mem.Allocator, cli_args: CliArgs) MergedConfig {
    return merge_mod.mergeConfig(io_context, allocator, cli_args) catch |err| {
        // zwanzig-disable: empty-catch-engine
        switch (err) {
            config.ConfigError.InvalidJson => {
                writeError(io_context, "Error: Invalid JSON in config file\n");
            },
            config.ConfigError.InvalidConfigFormat => {
                writeError(io_context, "Error: Invalid config file format\n");
            },
            config.ConfigError.MutuallyExclusiveFields => {
                writeError(io_context, "Error: Config file has both enabled_rules and disabled_rules\n");
            },
            config.ConfigError.FileNotFound => {
                writeError(io_context, "Error: Config file not found\n");
            },
            config.ConfigError.OutOfMemory => {
                writeError(io_context, "Error: Out of memory\n");
            },
        }
        // zwanzig-enable: empty-catch-engine
        std.process.exit(1);
    };
}

/// The message for a rule or checker name that no registered rule or checker
/// answers to. It names the offending name so a reader can tell a mistyped
/// rule apart from a mistyped option, which is reported differently.
fn unknownRuleNameMessage(allocator: std.mem.Allocator, name: []const u8) std.mem.Allocator.Error![]u8 {
    return std.fmt.allocPrint(
        allocator,
        "Error: Unknown rule '{s}'. No rule or checker is registered under that name; " ++
            "see docs/RULES.md for the registered names.\n",
        .{name},
    );
}

/// A rule or checker name the user supplied for `--do`, `--skip`, or a config
/// file's `enabled_rules`/`disabled_rules` that matches nothing registered.
///
/// This is checked here rather than where the names are read because this is
/// the first point the vocabulary exists: `registry.registerDefaults` runs
/// inside `configureAnalyzer`. One check there covers all three ways of naming
/// a rule, instead of three copies of the name list that could each drift from
/// the registry.
///
/// Ignoring such a name is not a smaller analysis, it is a different one. An
/// allowlist of only unknown names enables no rule at all, and the run would
/// print a clean report for an analysis that never ran, so the name is
/// reported the way an unknown option is and the run stops.
fn requireKnownRuleNames(analyzer: *const Analyzer, allocator: std.mem.Allocator, io_context: *compat.Context) void {
    const unknown = analyzer.unknownRuleName() orelse return;
    const message = unknownRuleNameMessage(allocator, unknown) catch {
        // Already failing; a report that cannot be formatted must not replace
        // the reason with a crash.
        writeError(io_context, "Error: Unknown rule name\n");
        std.process.exit(1);
    };
    writeError(io_context, message);
    allocator.free(message);
    std.process.exit(1);
}

fn discoverInputFiles(io_context: *compat.Context, allocator: std.mem.Allocator, cli_args: CliArgs) []const []const u8 {
    return file_discovery.discoverFiles(io_context, allocator, cli_args.paths) catch |err| {
        // zwanzig-disable: empty-catch-engine
        switch (err) {
            file_discovery.FileDiscoveryError.FileNotFound => {
                writeError(io_context, "Error: File or directory not found\n");
            },
            file_discovery.FileDiscoveryError.AccessDenied => {
                writeError(io_context, "Error: Access denied\n");
            },
            else => {
                writeError(io_context, "Error: Failed to discover files\n");
            },
        }
        // zwanzig-enable: empty-catch-engine
        std.process.exit(1);
    };
}

fn configureBuildMetadata(analyzer: *Analyzer, metadata: ?BuildMetadata) !void {
    if (metadata) |value| {
        try analyzer.setBuildMetadata(value);
    }
}

fn configureAnalyzer(analyzer: *Analyzer, cli_args: CliArgs, final_config: MergedConfig) !void {
    analyzer.setToolVersion(build_options.version);
    try registry.registerDefaults(analyzer);

    analyzer.setRuleFilter(final_config.rule_filter);
    if (final_config.max_worklist_steps) |steps| {
        analyzer.setMaxWorklistSteps(steps);
    }
    if (final_config.max_states_per_point) |max| {
        analyzer.setMaxStatesPerPoint(max);
    }
    if (final_config.use_widening) |use_w| {
        analyzer.setUseWidening(use_w);
    }
    const has_settings = final_config.resource_models.len > 0 or final_config.escape_models.len > 0 or
        final_config.escape_max_depth != null or final_config.optional_unwrap_test_severity != null;
    if (has_settings) {
        analyzer.setConfig(.{
            .rule_filter = .none,
            .resource_models = final_config.resource_models,
            .escape_models = final_config.escape_models,
            .escape_max_depth = final_config.escape_max_depth,
            .optional_unwrap_test_severity = final_config.optional_unwrap_test_severity,
        });
    }

    try configureBuildMetadata(analyzer, cli_args.build_metadata);

    if (cli_args.use_cache) {
        try analyzer.enableCache();
    }

    if (cli_args.dump_cfg_dir) |dir| {
        analyzer.setDumpCfgDir(dir);
    }
    if (cli_args.dump_exploded_graph_dir) |dir| {
        analyzer.setDumpExplodedGraphDir(dir);
    }
    if (cli_args.dump_annotated_cfg_dir) |dir| {
        analyzer.setDumpAnnotatedCfgDir(dir);
    }
    if (cli_args.dump_path_trace_dir) |dir| {
        analyzer.setDumpPathTraceDir(dir);
    }
}

pub fn runParsed(allocator: std.mem.Allocator, cli_args: CliArgs, io_context: *compat.Context) !void {
    const final_config = loadMergedConfig(io_context, allocator, cli_args);
    defer merge_mod.freeMergedConfig(allocator, cli_args, final_config);

    const files = discoverInputFiles(io_context, allocator, cli_args);
    defer file_discovery.freeDiscoveredFiles(allocator, files);
    log.info("discovered {d} file(s)", .{files.len});

    requireInputSelection(files) catch {
        writeError(io_context, "Error: No .zig files found. Nothing was analyzed.\n");
        std.process.exit(1);
    };

    var analyzer = Analyzer.initWithContext(allocator, io_context);
    defer analyzer.deinit();

    try configureAnalyzer(&analyzer, cli_args, final_config);

    // The registry is complete here, so the names the user supplied can be
    // resolved. Checked before the project pass and the analysis so a name
    // that selects nothing cannot be reported as a clean run.
    requireKnownRuleNames(&analyzer, allocator, io_context);

    log.info("analyzing with {d} rule(s) using {d} thread(s)", .{ analyzer.totalCheckerCount(), cli_args.thread_count });
    try analyzer.prepareProject(files);
    const analysis = try analyzeFilesParallel(&analyzer, files, cli_args.thread_count, allocator, io_context);
    defer analysis.deinit();
    try analyzer.analyzeProjectUnusedDecls();
    log.info("analysis complete", .{});
    analyzer.logAnalysisStats();

    // The report is printed before anything says a file failed, so the
    // findings from the files that analyzed are never held back by the one
    // that did not.
    try analyzer.printResults(cli_args.output_format);

    if (!analysis.isEmpty()) {
        reportFileFailures(io_context, files, analysis);
    }

    // A run that could not analyze every file it was given is not a clean
    // analysis of the selection, so it exits non-zero like a run with
    // diagnostics does.
    if (runFails(&analyzer, analysis)) {
        std.process.exit(1);
    }
}

test "analyzeFilesParallel releases results across allocation failure boundaries" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const DupeImportRule = test_dupe_import.DupeImportRule;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();
    const content =
        \\const first = @import("std");
        \\const second = @import("std");
    ;
    try temp_dir.writeFile("first.zig", content);
    try temp_dir.writeFile("second.zig", content);
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
    const files = [_][]const u8{ first_path, second_path };

    var reference = Analyzer.initWithContext(allocator, &io_context);
    defer reference.deinit();
    try reference.registerRule(&DupeImportRule.rule);
    try reference.analyzeFile(first_path);
    try testing.expectEqual(@as(usize, 1), reference.diagnostics.items.len);

    const cases = [_]struct {
        fail_after: ?usize,
        merge_capacity: usize,
        retained_diagnostics: usize,
        // A failure inside a worker is reported per file and the run still
        // merges what the other files found; a failure merging into Analyzer
        // cannot be attributed to a file, so it still ends the pass.
        worker_failure: bool,
    }{
        // Each worker allocates one message and one result list. Let one finish,
        // then fail the other worker's list insertion after its message clone.
        .{
            .fail_after = 3,
            .merge_capacity = 1,
            .retained_diagnostics = 1,
            .worker_failure = true,
        },
        // Both workers finish, but neither result can be merged.
        .{
            .fail_after = 4,
            .merge_capacity = 0,
            .retained_diagnostics = 0,
            .worker_failure = false,
        },
        // The first result moves to Analyzer before the second merge fails.
        .{
            .fail_after = 4,
            .merge_capacity = 1,
            .retained_diagnostics = 1,
            .worker_failure = false,
        },
        .{
            .fail_after = null,
            .merge_capacity = 0,
            .retained_diagnostics = 2,
            .worker_failure = false,
        },
    };
    for (cases) |case| {
        var persistent = testing.FailingAllocator.init(allocator, .{ .resize_fail_index = 0 });
        var buffers = testing.FailingAllocator.init(allocator, .{});
        {
            var analyzer = Analyzer.initWithContext(persistent.allocator(), &io_context);
            defer analyzer.deinit();
            try analyzer.registerRule(&DupeImportRule.rule);
            try analyzer.diagnostics.ensureTotalCapacityPrecise(
                analyzer.allocator,
                case.merge_capacity,
            );
            if (case.fail_after) |count| persistent.fail_index = persistent.alloc_index + count;

            // Neither FailingAllocator is thread-safe; use one analysis worker.
            const outcome = analyzeFilesParallel(
                &analyzer,
                &files,
                1,
                buffers.allocator(),
                &io_context,
            );
            if (case.worker_failure) {
                // The failed file is reported instead of ending the pass, and
                // the result the other worker produced is still merged.
                const analysis = try outcome;
                defer analysis.deinit();
                try testing.expect(persistent.has_induced_failure);
                try testing.expectEqual(@as(usize, 1), analysis.failureCount());
                try testing.expect(!analysis.isEmpty());
            } else if (case.fail_after != null) {
                try testing.expectError(error.OutOfMemory, outcome);
                try testing.expect(persistent.has_induced_failure);
            } else {
                const analysis = try outcome;
                defer analysis.deinit();
                try testing.expect(analysis.isEmpty());
                try testing.expectEqual(@as(usize, 0), analysis.failureCount());
            }
            try testing.expectEqual(case.retained_diagnostics, analyzer.diagnostics.items.len);
            for (analyzer.diagnostics.items) |diagnostic| {
                try testing.expect(
                    std.mem.eql(u8, diagnostic.file_path, first_path) or
                        std.mem.eql(u8, diagnostic.file_path, second_path),
                );
                try testing.expectEqualStrings(
                    reference.diagnostics.items[0].message,
                    diagnostic.message,
                );
                try testing.expectEqualStrings("dupe-import", diagnostic.rule_id);
                try testing.expectEqual(@as(usize, 2), diagnostic.range.start.line);
            }
        }
        // Check both allocator domains, including diagnostics already moved to Analyzer.
        try testing.expectEqual(persistent.allocated_bytes, persistent.freed_bytes);
        try testing.expectEqual(buffers.allocated_bytes, buffers.freed_bytes);
    }
}

test "configureBuildMetadata borrows CLI metadata" {
    const allocator = std.testing.allocator;

    const target_config = try TargetConfig.fromTriple(allocator, "x86_64-linux-gnu");
    var metadata = BuildMetadata.init(target_config, null);
    defer metadata.deinit(allocator);

    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();

    try configureBuildMetadata(&analyzer, metadata);

    try std.testing.expectEqualStrings("gnu", metadata.target.abi.?);
    try std.testing.expectEqualStrings("gnu", analyzer.getBuildMetadata().?.target.abi.?);
}

test "requireInputSelection rejects an empty selection" {
    try std.testing.expectError(error.NoInputFiles, requireInputSelection(&.{}));
    try requireInputSelection(&[_][]const u8{"src/main.zig"});
}

test "every registered rule name passes the CLI check on all three paths" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // The registered set is the vocabulary the check resolves names against,
    // so the names under test come from it rather than from a hand-written
    // list that could drift from the registry.
    var catalog = Analyzer.init(allocator);
    defer catalog.deinit();
    try registry.registerDefaults(&catalog);

    var names: std.ArrayList([]const u8) = .empty;
    defer names.deinit(allocator);
    for (catalog.checker_manager.checkers.items) |chkr| {
        try names.append(allocator, chkr.name);
    }
    for (catalog.checker_manager.adapted_rules.items) |rule| {
        try names.append(allocator, rule.name);
    }
    try testing.expect(names.items.len > 0);

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    for (names.items) |name| {
        // `--do` and `--skip` reach the analyzer as the filter the args
        // module built.
        for ([_][]const u8{ "--do", "--skip" }) |flag| {
            const argv = [_][]const u8{ "zwanzig", flag, name, "file.zig" };
            const cli_args = try args_mod.parseArgs(allocator, &argv);
            defer args_mod.freeCliArgs(allocator, cli_args);

            var analyzer = Analyzer.init(allocator);
            defer analyzer.deinit();
            try registry.registerDefaults(&analyzer);
            analyzer.setRuleFilter(cli_args.rule_filter);
            try testing.expect(analyzer.unknownRuleName() == null);
        }

        // A config file's `enabled_rules` and `disabled_rules` reach it
        // through `mergeConfig`.
        for ([_][]const u8{ "enabled_rules", "disabled_rules" }) |key| {
            const content = try std.fmt.allocPrint(
                allocator,
                "{{\"{s}\": [\"{s}\"]}}",
                .{ key, name },
            );
            defer allocator.free(content);
            try temp_dir.writeFile(".zwanzig.json", content);

            const config_path = try std.fmt.allocPrint(
                allocator,
                "{s}/.zwanzig.json",
                .{temp_dir.path()},
            );
            defer allocator.free(config_path);

            const argv = [_][]const u8{ "zwanzig", "--config", config_path };
            const cli_args = try args_mod.parseArgs(allocator, &argv);
            defer args_mod.freeCliArgs(allocator, cli_args);

            const merged = try merge_mod.mergeConfig(&io_context, allocator, cli_args);
            defer merge_mod.freeMergedConfig(allocator, cli_args, merged);

            var analyzer = Analyzer.init(allocator);
            defer analyzer.deinit();
            try registry.registerDefaults(&analyzer);
            analyzer.setRuleFilter(merged.rule_filter);
            try testing.expect(analyzer.unknownRuleName() == null);
        }
    }
}

test "a mistyped rule name is reported on --do, --skip and a config file" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // `empty-catt` is close enough to `empty-catch-engine` to be the kind of
    // typo that reads as a selection rather than as a mistake.
    const mistyped = "empty-catt";

    for ([_][]const u8{ "--do", "--skip" }) |flag| {
        const argv = [_][]const u8{ "zwanzig", flag, mistyped, "file.zig" };
        const cli_args = try args_mod.parseArgs(allocator, &argv);
        defer args_mod.freeCliArgs(allocator, cli_args);

        var analyzer = Analyzer.init(allocator);
        defer analyzer.deinit();
        try registry.registerDefaults(&analyzer);
        analyzer.setRuleFilter(cli_args.rule_filter);
        try testing.expectEqualStrings(mistyped, analyzer.unknownRuleName().?);
    }

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();
    const content = try std.fmt.allocPrint(allocator, "{{\"enabled_rules\": [\"{s}\"]}}", .{mistyped});
    defer allocator.free(content);
    try temp_dir.writeFile(".zwanzig.json", content);
    const config_path = try std.fmt.allocPrint(allocator, "{s}/.zwanzig.json", .{temp_dir.path()});
    defer allocator.free(config_path);
    const argv = [_][]const u8{ "zwanzig", "--config", config_path };
    const cli_args = try args_mod.parseArgs(allocator, &argv);
    defer args_mod.freeCliArgs(allocator, cli_args);
    const merged = try merge_mod.mergeConfig(&io_context, allocator, cli_args);
    defer merge_mod.freeMergedConfig(allocator, cli_args, merged);

    var analyzer = Analyzer.init(allocator);
    defer analyzer.deinit();
    try registry.registerDefaults(&analyzer);
    analyzer.setRuleFilter(merged.rule_filter);
    try testing.expectEqualStrings(mistyped, analyzer.unknownRuleName().?);
}

test "the unknown-rule message names the rule and differs from the unknown-option report" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const message = try unknownRuleNameMessage(allocator, "empty-catt");
    defer allocator.free(message);

    // The name is in the message, so a reader is told which selection was
    // rejected rather than being left to search for the typo.
    try testing.expect(std.mem.indexOf(u8, message, "empty-catt") != null);
    // An unknown rule is not an unknown option, and the two reports have to
    // stay distinguishable.
    try testing.expect(std.mem.indexOf(u8, message, "Unknown option") == null);
    try testing.expect(std.mem.indexOf(u8, message, "Unknown rule") != null);
}

test "a file that fails to analyze keeps the findings of the files that succeeded" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const DupeImportRule = test_dupe_import.DupeImportRule;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();
    // The good file reports a diagnostic of its own, so the test can tell the
    // report for it apart from the failure notice.
    const content =
        \\const first = @import("std");
        \\const second = @import("std");
    ;
    try temp_dir.writeFile("good.zig", content);
    var good_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const good_path = try std.fmt.bufPrint(
        &good_path_buffer,
        "{s}/good.zig",
        .{temp_dir.path()},
    );
    var missing_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    // Never created, so reading it is the file-level failure the run has to
    // survive.
    const missing_path = try std.fmt.bufPrint(
        &missing_path_buffer,
        "{s}/missing.zig",
        .{temp_dir.path()},
    );
    const files = [_][]const u8{ good_path, missing_path };

    var analyzer = Analyzer.initWithContext(allocator, &io_context);
    defer analyzer.deinit();
    try analyzer.registerRule(&DupeImportRule.rule);

    // The pass completes rather than ending on the unreadable file.
    const analysis = try analyzeFilesParallel(&analyzer, &files, 1, allocator, &io_context);
    defer analysis.deinit();

    try testing.expectEqual(@as(usize, 1), analysis.failureCount());
    try testing.expect(!analysis.isEmpty());
    try testing.expectEqual(@as(?anyerror, null), analysis.errors[0]);
    // Compared by name: the slot holds the error the file analysis returned,
    // which is a member of that function's error set rather than the global
    // `error.FileNotFound` literal.
    try testing.expectEqualStrings("FileNotFound", @errorName(analysis.errors[1].?));

    // The file that analyzed still reports, which is the whole point: the
    // failure must not take its sibling's findings with it.
    try testing.expectEqual(@as(usize, 1), analyzer.diagnostics.items.len);
    try testing.expectEqualStrings(good_path, analyzer.diagnostics.items[0].file_path);
    try testing.expectEqualStrings("dupe-import", analyzer.diagnostics.items[0].rule_id);

    // The failed file is named, so the report says which file it is missing.
    var lines: std.Io.Writer.Allocating = .init(allocator);
    defer lines.deinit();
    try writeFailureLines(&lines.writer, &files, analysis);
    const notice = lines.written();
    try testing.expect(std.mem.indexOf(u8, notice, missing_path) != null);
    try testing.expect(std.mem.indexOf(u8, notice, "FileNotFound") != null);
    // The file that analyzed is not named as a failure.
    try testing.expect(std.mem.indexOf(u8, notice, good_path) == null);

    // Diagnostics or not, a run missing a file is not a clean run.
    try testing.expect(runFails(&analyzer, analysis));
}

test "a run where every file analyzes names no failure and fails only on diagnostics" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const DupeImportRule = test_dupe_import.DupeImportRule;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();
    const content =
        \\const first = @import("std");
        \\const second = @import("std");
    ;
    try temp_dir.writeFile("first.zig", content);
    try temp_dir.writeFile("second.zig", content);
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
    const files = [_][]const u8{ first_path, second_path };

    var analyzer = Analyzer.initWithContext(allocator, &io_context);
    defer analyzer.deinit();
    try analyzer.registerRule(&DupeImportRule.rule);

    const analysis = try analyzeFilesParallel(&analyzer, &files, 1, allocator, &io_context);
    defer analysis.deinit();

    // Nothing failed, so the run adds no stderr notice to its report and the
    // output stays what an all-success run always produced.
    try testing.expect(analysis.isEmpty());
    try testing.expectEqual(@as(usize, 0), analysis.failureCount());
    try testing.expectEqual(@as(?anyerror, null), analysis.errors[0]);
    try testing.expectEqual(@as(?anyerror, null), analysis.errors[1]);

    var lines: std.Io.Writer.Allocating = .init(allocator);
    defer lines.deinit();
    try writeFailureLines(&lines.writer, &files, analysis);
    try testing.expectEqualStrings("", lines.written());

    try testing.expectEqual(@as(usize, 2), analyzer.diagnostics.items.len);
    // Both files reported, and the findings are ordered deterministically.
    try testing.expectEqualStrings(first_path, analyzer.diagnostics.items[0].file_path);
    try testing.expectEqualStrings(second_path, analyzer.diagnostics.items[1].file_path);
    // Diagnostics still make the run fail, exactly as before.
    try testing.expect(runFails(&analyzer, analysis));
}

test "an empty selection reports no failure and fails on nothing" {
    const testing = std.testing;
    const allocator = testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();

    var analyzer = Analyzer.initWithContext(allocator, &io_context);
    defer analyzer.deinit();

    const analysis = try analyzeFilesParallel(&analyzer, &.{}, 1, allocator, &io_context);
    defer analysis.deinit();

    // No files means nothing failed, which must not be reported as a failure
    // of its own; an empty selection is caught before the analysis stage.
    try testing.expect(analysis.isEmpty());
    try testing.expect(!runFails(&analyzer, analysis));
}
