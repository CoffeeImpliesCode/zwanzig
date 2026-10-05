const std = @import("std");
const compat = @import("compat.zig");
const log = std.log.scoped(.file_discovery);

pub const FileDiscoveryError = error{
    OutOfMemory,
    AccessDenied,
    InvalidUtf8,
    NotDir,
    FileNotFound,
};

/// Directory names a recursive scan never descends into. The match is exact:
/// no other name is skipped, and hidden directories are not skipped as a class,
/// so first-party sources in a hidden directory are still analyzed. These names
/// only filter children found during the walk; a path named by the caller is
/// always selected, so a skipped directory - or a file inside one - can still be
/// requested explicitly.
const ignored_dirs = [_][]const u8{
    "zig-cache",
    ".zig-cache",
    ".zig-global-cache",
    "zig-out",
    ".zigmod",
    ".gyro",
    "zig-pkg",
    "third_party",
    ".git",
    ".jj",
};

/// Upper bound on how deep the recursive walk descends. A directory can never
/// contain itself, so a cycle can only enter through a symlink, and the compat
/// layer reports a symlink with the same `.other` as an untyped entry - see
/// `resolveUnknownKind`. This bound ends such a cycle instead of walking it
/// forever; no real source tree comes anywhere near it.
const max_walk_depth = 64;

/// Collects the `.zig` files selected by `paths`. A directory path is walked
/// recursively, skipping the subdirectories named in `ignored_dirs`. An entry
/// whose kind the filesystem did not report is resolved with a stat instead of
/// skipped, so a filesystem that answers `DT_UNKNOWN` still yields every file
/// (`resolveUnknownKind`). A file path is selected as given, even when it lies
/// inside a skipped directory. An empty `paths` scans the current directory.
pub fn discoverFiles(
    io_context: *compat.Context,
    allocator: std.mem.Allocator,
    paths: []const []const u8,
) FileDiscoveryError![]const []const u8 {
    var files: std.ArrayList([]const u8) = .empty;
    errdefer {
        for (files.items) |file| {
            allocator.free(file);
        }
        files.deinit(allocator);
    }

    if (paths.len == 0) {
        log.debug("discover: walking current directory", .{});
        try walkDirectory(io_context, allocator, &files, ".");
    } else {
        for (paths) |path| {
            log.debug("discover: input path {s}", .{path});
            const stat = compat.stat(io_context, path) catch |err| switch (err) {
                error.FileNotFound => return FileDiscoveryError.FileNotFound,
                error.AccessDenied => return FileDiscoveryError.AccessDenied,
                error.NotDir => return FileDiscoveryError.NotDir,
                else => return FileDiscoveryError.AccessDenied,
            };

            if (stat == .directory) {
                log.debug("discover: walking directory {s}", .{path});
                try walkDirectory(io_context, allocator, &files, path);
            } else if (isZigFile(path)) {
                log.debug("discover: adding file {s}", .{path});
                const owned = try allocator.dupe(u8, path);
                try files.append(allocator, owned);
            }
        }
    }

    return files.toOwnedSlice(allocator);
}

fn walkDirectory(
    io_context: *compat.Context,
    allocator: std.mem.Allocator,
    files: *std.ArrayList([]const u8),
    base_path: []const u8,
) FileDiscoveryError!void {
    try walkDirectoryRecursive(io_context, allocator, files, base_path, null, 0);
}

fn walkDirectoryRecursive(
    io_context: *compat.Context,
    allocator: std.mem.Allocator,
    files: *std.ArrayList([]const u8),
    base_path: []const u8,
    relative_path: ?[]const u8,
    depth: usize,
) FileDiscoveryError!void {
    const open_path = if (relative_path) |rel|
        std.fmt.allocPrint(allocator, "{s}/{s}", .{ base_path, rel }) catch return FileDiscoveryError.OutOfMemory
    else
        null;
    defer if (open_path) |p| allocator.free(p);

    const dir_to_open = open_path orelse base_path;
    log.debug("walk: open dir {s}", .{dir_to_open});

    var dir = compat.openDir(io_context, dir_to_open, true) catch |err| switch (err) {
        error.AccessDenied => return FileDiscoveryError.AccessDenied,
        error.FileNotFound => return FileDiscoveryError.FileNotFound,
        error.NotDir => return FileDiscoveryError.NotDir,
        else => return FileDiscoveryError.AccessDenied,
    };
    defer compat.closeDir(io_context, &dir);

    while (true) {
        const entry = compat.nextDir(io_context, &dir) catch return FileDiscoveryError.AccessDenied;
        if (entry) |e| {
            // An entry the filesystem declined to type is resolved rather
            // than skipped: `resolveUnknownKind` says why that is not a loss
            // of coverage.
            var kind = e.kind;
            if (kind == .other) {
                const resolved = try resolveUnknownKind(io_context, allocator, base_path, relative_path, e.name);
                kind = resolved orelse continue;
            }

            if (kind == .directory) {
                if (shouldIgnoreDir(e.name)) {
                    log.debug("walk: skip dir {s}", .{e.name});
                    continue;
                }
                if (depth >= max_walk_depth) {
                    log.debug("walk: depth {d} reached, not entering {s}/{s}", .{ max_walk_depth, dir_to_open, e.name });
                    continue;
                }
                const new_relative = if (relative_path) |rel|
                    std.fmt.allocPrint(allocator, "{s}/{s}", .{ rel, e.name }) catch return FileDiscoveryError.OutOfMemory
                else
                    allocator.dupe(u8, e.name) catch return FileDiscoveryError.OutOfMemory;
                defer allocator.free(new_relative);

                log.debug("walk: enter dir {s}", .{new_relative});
                try walkDirectoryRecursive(io_context, allocator, files, base_path, new_relative, depth + 1);
            } else if (kind == .file and isZigFile(e.name)) {
                const full_path = try entryPath(allocator, base_path, relative_path, e.name);

                if (std.mem.eql(u8, base_path, ".")) {
                    allocator.free(full_path);
                    const simple_path = if (relative_path) |rel|
                        std.fmt.allocPrint(allocator, "{s}/{s}", .{ rel, e.name }) catch return FileDiscoveryError.OutOfMemory
                    else
                        allocator.dupe(u8, e.name) catch return FileDiscoveryError.OutOfMemory;
                    log.debug("walk: found file {s}", .{simple_path});
                    files.append(allocator, simple_path) catch {
                        allocator.free(simple_path);
                        return FileDiscoveryError.OutOfMemory;
                    };
                } else {
                    log.debug("walk: found file {s}", .{full_path});
                    files.append(allocator, full_path) catch {
                        allocator.free(full_path);
                        return FileDiscoveryError.OutOfMemory;
                    };
                }
            }
        } else {
            break;
        }
    }
}

/// The path of `name` as the walk reaches it, built the same way whether or
/// not the walk has descended below `base_path` yet.
fn entryPath(
    allocator: std.mem.Allocator,
    base_path: []const u8,
    relative_path: ?[]const u8,
    name: []const u8,
) FileDiscoveryError![]u8 {
    const printed = if (relative_path) |rel|
        std.fmt.allocPrint(allocator, "{s}/{s}/{s}", .{ base_path, rel, name })
    else
        std.fmt.allocPrint(allocator, "{s}/{s}", .{ base_path, name });
    return printed catch return FileDiscoveryError.OutOfMemory;
}

/// Resolves the kind of an entry whose type the filesystem did not report, and
/// returns null when the entry cannot be classified at all.
///
/// Not every filesystem fills in an entry's type while it reads a directory:
/// NFS and other network mounts answer `DT_UNKNOWN`, and the compat layer hands
/// every kind that is neither a file nor a directory over as `.other`. Skipping
/// those entries is not a conservative choice but a silent loss of coverage -
/// on this repository 31 of the 111 sources under `src/` were never opened, the
/// cross-file references only they held went missing, and that surfaced as
/// findings against live declarations. Resolving the kind is what makes those
/// entries visible again, so "simplifying" this back into skipping `.other`
/// reintroduces the under-analysis.
///
/// The compat layer maps `DT_LNK` to `.other` just as it maps `DT_UNKNOWN`, and
/// `compat.stat` follows symlinks, so a resolved `.directory` may be a symlink
/// to one. Telling the two apart needs a no-follow stat the compat layer does
/// not expose, so `max_walk_depth` is what keeps a symlink cycle finite.
///
/// A stat that fails is not an error: the entry is skipped and the walk
/// continues, so an entry that cannot be classified never turns into a failure
/// the CLI reports against a file.
fn resolveUnknownKind(
    io_context: *compat.Context,
    allocator: std.mem.Allocator,
    base_path: []const u8,
    relative_path: ?[]const u8,
    name: []const u8,
) FileDiscoveryError!?compat.EntryKind {
    const path = try entryPath(allocator, base_path, relative_path, name);
    defer allocator.free(path);

    const kind = compat.stat(io_context, path) catch |err| {
        log.debug("walk: cannot classify {s}: {s}", .{ path, @errorName(err) });
        return null;
    };

    // A stat that resolves to neither a file nor a directory - a device, a
    // socket, a dangling link - holds nothing to analyse.
    return switch (kind) {
        .file, .directory => kind,
        .other => null,
    };
}

fn shouldIgnoreDir(name: []const u8) bool {
    for (ignored_dirs) |ignored| {
        if (std.mem.eql(u8, name, ignored)) {
            return true;
        }
    }
    return false;
}

fn isZigFile(name: []const u8) bool {
    return std.mem.endsWith(u8, name, ".zig");
}

pub fn freeDiscoveredFiles(allocator: std.mem.Allocator, files: []const []const u8) void {
    for (files) |file| {
        allocator.free(file);
    }
    allocator.free(files);
}

/// The names `--help` and `docs/USAGE.md` list as skipped, repeated here so the
/// discovery test states the documented contract independently of the table
/// that implements it.
const documented_ignored_dirs = [_][]const u8{
    "zig-cache",
    ".zig-cache",
    ".zig-global-cache",
    "zig-out",
    ".zigmod",
    ".gyro",
    "zig-pkg",
    "third_party",
    ".git",
    ".jj",
};

fn pathLessThan(_: void, a: []const u8, b: []const u8) bool {
    return std.mem.lessThan(u8, a, b);
}

fn expectDiscovered(actual: []const []const u8, expected: []const []const u8) !void {
    // Directory iteration order is not defined, so compare as sets.
    std.mem.sort([]const u8, actual, {}, pathLessThan);
    std.mem.sort([]const u8, expected, {}, pathLessThan);

    try std.testing.expectEqual(expected.len, actual.len);
    for (actual, expected) |found, want| {
        try std.testing.expectEqualStrings(want, found);
    }
}

test "discoverFiles: recursive scan skips only the documented directory names" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    // Each ignored name holds a `.zig` file, so a scan that descends into one
    // selects a file the assertions below reject. `.firstparty` holds the same
    // file under a hidden name that is not ignored.
    const scanned_dirs = [_][]const u8{ "src", ".firstparty" } ++ documented_ignored_dirs;
    for (scanned_dirs) |dir_name| {
        var dir_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
        const dir_path = try std.fmt.bufPrint(&dir_path_buffer, "{s}/{s}", .{ temp_dir.path(), dir_name });
        try compat.makePath(io_context, dir_path);

        const file_sub_path = try std.fmt.allocPrint(allocator, "{s}/item.zig", .{dir_name});
        defer allocator.free(file_sub_path);
        try temp_dir.writeFile(file_sub_path, "pub const marker: u8 = 0;\n");
    }

    var first_party_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const first_party_item = try std.fmt.bufPrint(&first_party_buffer, "{s}/.firstparty/item.zig", .{temp_dir.path()});
    var src_item_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const src_item = try std.fmt.bufPrint(&src_item_buffer, "{s}/src/item.zig", .{temp_dir.path()});

    // Walking the root keeps the first-party sources, hidden one included, and
    // leaves out every documented directory name.
    {
        const paths = [_][]const u8{temp_dir.path()};
        const files = try discoverFiles(io_context, allocator, &paths);
        defer freeDiscoveredFiles(allocator, files);

        const expected = [_][]const u8{ first_party_item, src_item };
        try expectDiscovered(files, &expected);
    }

    // An ordinary directory selection is unaffected by the skip list.
    {
        var src_dir_buffer: [std.fs.max_path_bytes]u8 = undefined;
        const src_dir = try std.fmt.bufPrint(&src_dir_buffer, "{s}/src", .{temp_dir.path()});
        const paths = [_][]const u8{src_dir};
        const files = try discoverFiles(io_context, allocator, &paths);
        defer freeDiscoveredFiles(allocator, files);

        const expected = [_][]const u8{src_item};
        try expectDiscovered(files, &expected);
    }

    // The skip list only filters children of a recursive walk: a skipped
    // directory named directly is walked, and a file inside one is taken as
    // given.
    for (documented_ignored_dirs) |dir_name| {
        var dir_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
        const dir_path = try std.fmt.bufPrint(&dir_path_buffer, "{s}/{s}", .{ temp_dir.path(), dir_name });
        var item_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
        const item_path = try std.fmt.bufPrint(&item_path_buffer, "{s}/item.zig", .{dir_path});

        {
            const paths = [_][]const u8{dir_path};
            const files = try discoverFiles(io_context, allocator, &paths);
            defer freeDiscoveredFiles(allocator, files);

            const expected = [_][]const u8{item_path};
            try expectDiscovered(files, &expected);
        }
        {
            const paths = [_][]const u8{item_path};
            const files = try discoverFiles(io_context, allocator, &paths);
            defer freeDiscoveredFiles(allocator, files);

            const expected = [_][]const u8{item_path};
            try expectDiscovered(files, &expected);
        }
    }
}

test "isZigFile" {
    try std.testing.expect(isZigFile("main.zig"));
    try std.testing.expect(isZigFile("path/to/file.zig"));
    try std.testing.expect(!isZigFile("main.c"));
    try std.testing.expect(!isZigFile("main.zig.bak"));
    try std.testing.expect(!isZigFile(""));
}

// The unknown-kind path cannot be provoked from a test without a fake
// filesystem: the kind comes from the host's own `d_type`, so on a filesystem
// that reports types every entry arrives already typed and the resolution
// never runs. What can be tested directly is the resolution itself, which is
// where the coverage belongs - these assertions fail if the stat stops
// resolving, if it resolves to the wrong kind, or if a failed stat starts
// aborting the walk instead of skipping the entry.
test "resolveUnknownKind: a stat decides the kind, and a stat that fails skips" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile("item.zig", "pub const marker: u8 = 0;\n");
    try temp_dir.writeFile("notes.txt", "not a source\n");
    var nested_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const nested_path = try std.fmt.bufPrint(&nested_buffer, "{s}/nested", .{temp_dir.path()});
    try compat.makePath(io_context, nested_path);
    try temp_dir.writeFile("nested/item.zig", "pub const nested_marker: u8 = 1;\n");

    const root = temp_dir.path();

    // A directory and a regular file both resolve, from the top of the walk
    // and from below it.
    try std.testing.expectEqual(
        compat.EntryKind.directory,
        (try resolveUnknownKind(io_context, allocator, root, null, "nested")).?,
    );
    try std.testing.expectEqual(
        compat.EntryKind.file,
        (try resolveUnknownKind(io_context, allocator, root, null, "item.zig")).?,
    );
    try std.testing.expectEqual(
        compat.EntryKind.file,
        (try resolveUnknownKind(io_context, allocator, root, "nested", "item.zig")).?,
    );

    // Resolution reports the entry's kind, not whether it is a source: the
    // `.zig` filter stays with the walk.
    try std.testing.expectEqual(
        compat.EntryKind.file,
        (try resolveUnknownKind(io_context, allocator, root, null, "notes.txt")).?,
    );

    // An entry that cannot be stat'd is skipped, never reported as an error
    // the CLI would blame on a file.
    try std.testing.expectEqual(
        @as(?compat.EntryKind, null),
        try resolveUnknownKind(io_context, allocator, root, null, "absent.zig"),
    );
    try std.testing.expectEqual(
        @as(?compat.EntryKind, null),
        try resolveUnknownKind(io_context, allocator, root, null, "nested/absent/deeper.zig"),
    );
}

test "discoverFiles: explicit files" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    const paths = [_][]const u8{"src/main.zig"};
    const files = try discoverFiles(io_context, allocator, &paths);
    defer freeDiscoveredFiles(allocator, files);

    try std.testing.expectEqual(@as(usize, 1), files.len);
    try std.testing.expectEqualStrings("src/main.zig", files[0]);
}

test "discoverFiles: walks directory" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    const paths = [_][]const u8{"src"};
    const files = try discoverFiles(io_context, allocator, &paths);
    defer freeDiscoveredFiles(allocator, files);

    try std.testing.expect(files.len > 0);

    var found_main = false;
    for (files) |f| {
        if (std.mem.endsWith(u8, f, "main.zig")) {
            found_main = true;
            break;
        }
    }
    try std.testing.expect(found_main);
}

test "discoverFiles: empty paths walks current directory" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    const paths = [_][]const u8{};
    const files = try discoverFiles(io_context, allocator, &paths);
    defer freeDiscoveredFiles(allocator, files);

    try std.testing.expect(files.len > 0);
}

test "discoverFiles: non-zig files filtered" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    const paths = [_][]const u8{"."};
    const files = try discoverFiles(io_context, allocator, &paths);
    defer freeDiscoveredFiles(allocator, files);

    for (files) |f| {
        try std.testing.expect(std.mem.endsWith(u8, f, ".zig"));
    }
}
