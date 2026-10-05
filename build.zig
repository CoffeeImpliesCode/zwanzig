const std = @import("std");
const builtin = @import("builtin");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const log_level = b.option(std.log.Level, "log-level", "Set log level") orelse .info;
    const version = readPackageVersion(b);
    const main_source = if (builtin.zig_version.minor == 16)
        b.path("src/main_0_16.zig")
    else
        b.path("src/main.zig");

    const options = b.addOptions();
    options.addOption(std.log.Level, "log_level", log_level);
    options.addOption([]const u8, "version", version);

    const public_module = b.addModule("zwanzig", .{
        .root_source_file = b.path("src/lib.zig"),
        .target = target,
        .optimize = optimize,
    });

    const exe_module = b.createModule(.{
        .root_source_file = main_source,
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });
    exe_module.addOptions("build_options", options);

    // Create the main executable
    const exe = b.addExecutable(.{
        .name = "zwanzig",
        .root_module = exe_module,
    });
    b.installArtifact(exe);

    // Create a run step
    const run_cmd = b.addRunArtifact(exe);
    run_cmd.step.dependOn(b.getInstallStep());
    if (b.args) |args| {
        run_cmd.addArgs(args);
    }

    const run_step = b.step("run", "Run the analyzer");
    run_step.dependOn(&run_cmd.step);

    const test_module = b.createModule(.{
        .root_source_file = main_source,
        .target = target,
        .optimize = optimize,
        .link_libc = true,
    });
    test_module.addOptions("build_options", options);

    // Create unit tests (tests embedded in source files)
    const tests = b.addTest(.{
        .root_module = test_module,
    });

    const run_tests = b.addRunArtifact(tests);
    const test_step = b.step("test", "Run unit tests");
    test_step.dependOn(&run_tests.step);

    // Create fixture tests
    const fixture_test_module = b.createModule(.{
        .root_source_file = b.path("test/fixture_tests.zig"),
        .target = target,
        .optimize = optimize,
    });
    fixture_test_module.addImport("src", public_module);

    const fixture_tests = b.addTest(.{
        .root_module = fixture_test_module,
    });

    const run_fixture_tests = b.addRunArtifact(fixture_tests);
    const fixture_test_step = b.step("test-fixtures", "Run fixture-based tests");
    fixture_test_step.dependOn(&run_fixture_tests.step);

    // Also run fixture tests as part of the main test step
    test_step.dependOn(&run_fixture_tests.step);

    // Compile every fixture on the running frontend. A fixture that names the
    // other pinned frontend in a marker line is skipped on this one.
    const check_fixtures_step = b.step("check-fixtures", "Verify all test fixtures compile on this frontend");
    addFixtureChecks(b, check_fixtures_step, target, optimize);
}

fn readPackageVersion(b: *std.Build) []const u8 {
    const zon_path = "build.zig.zon";
    const zon_contents: [:0]u8 = if (builtin.zig_version.minor == 16)
        std.Io.Dir.cwd().readFileAllocOptions(
            b.graph.io,
            zon_path,
            b.allocator,
            std.Io.Limit.limited(1024 * 1024),
            .of(u8),
            0,
        ) catch |err| {
            std.debug.panic("failed to read {s}: {s}", .{ zon_path, @errorName(err) });
        }
    else
        std.fs.cwd().readFileAllocOptions(
            b.allocator,
            zon_path,
            1024 * 1024,
            null,
            .of(u8),
            0,
        ) catch |err| {
            std.debug.panic("failed to read {s}: {s}", .{ zon_path, @errorName(err) });
        };

    defer b.allocator.free(zon_contents);

    const PackageMetadata = struct {
        version: []const u8,
    };

    const parsed = if (builtin.zig_version.minor == 16)
        std.zon.parse.fromSliceAlloc(
            PackageMetadata,
            b.allocator,
            zon_contents,
            null,
            .{ .ignore_unknown_fields = true },
        ) catch |err| {
            std.debug.panic("failed to parse {s}: {s}", .{ zon_path, @errorName(err) });
        }
    else
        std.zon.parse.fromSlice(
            PackageMetadata,
            b.allocator,
            zon_contents,
            null,
            .{ .ignore_unknown_fields = true },
        ) catch |err| {
            std.debug.panic("failed to parse {s}: {s}", .{ zon_path, @errorName(err) });
        };
    defer std.zon.parse.free(b.allocator, parsed);

    return b.allocator.dupe(u8, parsed.version) catch {
        std.debug.panic("failed to allocate package version", .{});
    };
}

const fixture_dir_prefix = "test/fixtures/";
const max_fixture_bytes = 1024 * 1024;

/// The frontends this repository pins. A fixture names one of them in a
/// marker line (`// Zig 0.15.2 fixture:` or `// Zig 0.16.0 fixture:`) and is
/// then compiled only by that frontend.
///
/// A fixture whose invalidity IS the rule's subject (an import of a module
/// that does not exist, a shadowed declaration, an unreachable statement)
/// cannot be compiled on any frontend. It instead carries the marker:
///   `// zwanzig: not a standalone program: <reason>`
/// which tells the gate to skip it everywhere. A fixture names at most one
/// frontend or the not-a-program marker; carrying both is a build error.
const FixtureFrontend = enum {
    zig_0_15_2,
    zig_0_16_0,

    fn marker(frontend: FixtureFrontend) []const u8 {
        return switch (frontend) {
            .zig_0_15_2 => "// Zig 0.15.2 fixture:",
            .zig_0_16_0 => "// Zig 0.16.0 fixture:",
        };
    }

    fn isCurrent(frontend: FixtureFrontend) bool {
        return switch (frontend) {
            .zig_0_15_2 => builtin.zig_version.minor == 15,
            .zig_0_16_0 => builtin.zig_version.minor == 16,
        };
    }
};

/// Marker line for a fixture that is intentionally not a standalone Zig
/// program on any frontend. The gate skips compiling these files entirely.
/// The marker must be followed by an explanation of why the file is not a
/// standalone program; an empty explanation is a build error.
const not_a_program_marker = "// zwanzig: not a standalone program:";

const FixtureTarget = union(enum) {
    every_frontend,
    only: FixtureFrontend,
    not_a_program,
};

const fixture_frontends = [_]FixtureFrontend{ .zig_0_15_2, .zig_0_16_0 };

fn fixturePath(b: *std.Build, dir_path: []const u8, entry_name: []const u8) []const u8 {
    const full_path = b.allocator.alloc(u8, dir_path.len + 1 + entry_name.len) catch
        std.debug.panic("out of memory while joining {s}/{s}", .{ dir_path, entry_name });
    @memcpy(full_path[0..dir_path.len], dir_path);
    full_path[dir_path.len] = '/';
    @memcpy(full_path[dir_path.len + 1 ..], entry_name);
    return full_path;
}

fn readFixtureText(b: *std.Build, full_path: []const u8) [:0]u8 {
    const contents = if (builtin.zig_version.minor == 16)
        std.Io.Dir.cwd().readFileAllocOptions(
            b.graph.io,
            full_path,
            b.allocator,
            std.Io.Limit.limited(max_fixture_bytes),
            .of(u8),
            0,
        ) catch |err| {
            std.debug.panic("failed to read fixture {s}: {s}", .{ full_path, @errorName(err) });
        }
    else
        std.fs.cwd().readFileAllocOptions(
            b.allocator,
            full_path,
            max_fixture_bytes,
            null,
            .of(u8),
            0,
        ) catch |err| {
            std.debug.panic("failed to read fixture {s}: {s}", .{ full_path, @errorName(err) });
        };
    return contents;
}

/// Returns what the compile gate must do with a fixture: compile it everywhere,
/// compile it on exactly one pinned frontend, or skip it because it is an
/// analyzer input rather than a standalone program.
///
/// A fixture carries at most one per-frontend marker or the not-a-program
/// marker; carrying both is a contradiction and fails the build.
fn fixtureTargetFrontend(full_path: []const u8, contents: []const u8) FixtureTarget {
    var target: ?FixtureFrontend = null;
    var not_a_program = false;
    var lines = std.mem.splitScalar(u8, contents, '\n');
    while (lines.next()) |line| {
        const trimmed = std.mem.trim(u8, line, " \t");
        if (std.mem.startsWith(u8, trimmed, not_a_program_marker)) {
            const reason = std.mem.trim(u8, trimmed[not_a_program_marker.len..], " \t");
            if (reason.len == 0) {
                std.debug.panic(
                    "{s} carries `{s}` with no reason; the marker must say why the fixture is not a program",
                    .{ full_path, not_a_program_marker },
                );
            }
            not_a_program = true;
        }
        for (fixture_frontends) |frontend| {
            if (!std.mem.startsWith(u8, trimmed, frontend.marker())) continue;
            if (target != null) {
                std.debug.panic(
                    "{s} names more than one frontend; a fixture targets exactly one",
                    .{full_path},
                );
            }
            target = frontend;
        }
    }
    if (not_a_program and target != null) {
        std.debug.panic(
            "{s} is marked as both a single-frontend fixture and not a standalone program; pick one",
            .{full_path},
        );
    }
    if (not_a_program) return .not_a_program;
    if (target) |frontend| return .{ .only = frontend };
    return .every_frontend;
}

fn fixtureTargetsCurrentFrontend(b: *std.Build, full_path: []const u8) bool {
    const contents = readFixtureText(b, full_path);
    return switch (fixtureTargetFrontend(full_path, contents)) {
        .every_frontend => true,
        .only => |frontend| frontend.isCurrent(),
        .not_a_program => false,
    };
}

fn addFixtureCheck(
    b: *std.Build,
    step: *std.Build.Step,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    full_path: []const u8,
    entry_name: []const u8,
) void {
    const check_module = b.createModule(.{
        .root_source_file = b.path(full_path),
        .target = target,
        .optimize = optimize,
    });

    const check = b.addObject(.{
        .name = entry_name,
        .root_module = check_module,
    });

    step.dependOn(&check.step);
}

/// Compiles one fixture unless it names the other pinned frontend.
fn addFixtureFileCheck(
    b: *std.Build,
    step: *std.Build.Step,
    target: std.Build.ResolvedTarget,
    optimize: std.builtin.OptimizeMode,
    dir_path: []const u8,
    entry_name: []const u8,
) void {
    const full_path = fixturePath(b, dir_path, entry_name);
    if (!fixtureTargetsCurrentFrontend(b, full_path)) return;
    addFixtureCheck(b, step, target, optimize, full_path, entry_name);
}

/// Every fixture directory the compile check covers. Add a new fixture
/// directory here; a directory missing from this list is never compiled.
const fixture_dirs = [_][]const u8{
    fixture_dir_prefix ++ "dupe_import",
    fixture_dir_prefix ++ "empty_defer",
    fixture_dir_prefix ++ "empty_errdefer",
    fixture_dir_prefix ++ "file_as_struct",
    fixture_dir_prefix ++ "todo_comment",
    fixture_dir_prefix ++ "unreachable_code",
    fixture_dir_prefix ++ "unused_decl",
    fixture_dir_prefix ++ "divide_by_zero_engine",
    fixture_dir_prefix ++ "identifier_style",
    fixture_dir_prefix ++ "optional_unwrap",
    fixture_dir_prefix ++ "store_violations_engine",
    fixture_dir_prefix ++ "swallowed_error",
    fixture_dir_prefix ++ "unreachable_code_engine",
    fixture_dir_prefix ++ "analyzer_identifier_style",
    fixture_dir_prefix ++ "deinit_lifecycle",
    fixture_dir_prefix ++ "sentinel_alloc",
    fixture_dir_prefix ++ "slice_bounds_engine",
    fixture_dir_prefix ++ "return_local_ptr",
    fixture_dir_prefix ++ "shadowed_variable",
    fixture_dir_prefix ++ "stack_escape_engine",
    fixture_dir_prefix ++ "unused_parameter",
    fixture_dir_prefix ++ "project_unused_decl",
};

fn addFixtureChecks(b: *std.Build, step: *std.Build.Step, target: std.Build.ResolvedTarget, optimize: std.builtin.OptimizeMode) void {
    const matrix_fixture = if (builtin.zig_version.minor == 16) "zig_0_16.zig" else "zig_0_15.zig";
    addFixtureCheck(
        b,
        step,
        target,
        optimize,
        fixturePath(b, fixture_dir_prefix ++ "frontend_matrix", "shared.zig"),
        "shared.zig",
    );
    addFixtureCheck(
        b,
        step,
        target,
        optimize,
        fixturePath(b, fixture_dir_prefix ++ "frontend_matrix", matrix_fixture),
        matrix_fixture,
    );

    for (fixture_dirs) |dir_path| {
        if (builtin.zig_version.minor == 16) {
            var dir = std.Io.Dir.cwd().openDir(b.graph.io, dir_path, .{ .iterate = true }) catch |err| {
                std.debug.panic("failed to open fixture directory {s}: {s}", .{ dir_path, @errorName(err) });
            };
            defer dir.close(b.graph.io);

            var iter = dir.iterate();
            while (iter.next(b.graph.io) catch |err| {
                std.debug.panic("failed to read fixture directory {s}: {s}", .{ dir_path, @errorName(err) });
            }) |entry| {
                if (entry.kind != .file) continue;
                if (!std.mem.endsWith(u8, entry.name, ".zig")) continue;
                addFixtureFileCheck(b, step, target, optimize, dir_path, entry.name);
            }
        } else {
            var dir = std.fs.cwd().openDir(dir_path, .{ .iterate = true }) catch |err| {
                std.debug.panic("failed to open fixture directory {s}: {s}", .{ dir_path, @errorName(err) });
            };
            defer dir.close();

            var iter = dir.iterate();
            while (iter.next() catch |err| {
                std.debug.panic("failed to read fixture directory {s}: {s}", .{ dir_path, @errorName(err) });
            }) |entry| {
                if (entry.kind != .file) continue;
                if (!std.mem.endsWith(u8, entry.name, ".zig")) continue;
                addFixtureFileCheck(b, step, target, optimize, dir_path, entry.name);
            }
        }
    }
}
