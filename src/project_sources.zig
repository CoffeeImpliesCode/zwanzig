const std = @import("std");
const compat = @import("compat.zig");
const call_resolver = @import("analysis/call_resolver.zig");
const import_resolver = @import("analysis/import_resolver.zig");

const max_context_depth = 64;
const build_file_name = "build.zig";
const max_source_size = 10 * 1024 * 1024;

const Entry = struct {
    path: []u8,
    content: [:0]u8,
    tree: std.zig.Ast,
    diagnostic: bool,

    fn load(
        io_context: *compat.Context,
        allocator: std.mem.Allocator,
        path: []const u8,
        diagnostic: bool,
    ) !Entry {
        const owned_path = try allocator.dupe(u8, path);
        errdefer allocator.free(owned_path);

        // The sentinel is required by std.zig.Ast.parse.
        const content = try compat.readFileAlloc(io_context, allocator, path, max_source_size);
        errdefer allocator.free(content.ptr[0 .. content.len + 1]);

        const tree = try std.zig.Ast.parse(allocator, content, .zig);

        return .{
            .path = owned_path,
            .content = content,
            .tree = tree,
            .diagnostic = diagnostic,
        };
    }

    fn deinit(self: *Entry, allocator: std.mem.Allocator) void {
        self.tree.deinit(allocator);
        allocator.free(self.content.ptr[0 .. self.content.len + 1]);
        allocator.free(self.path);
    }
};

/// Owns one immutable parsed snapshot of selected sources and build context.
pub const ProjectSources = struct {
    allocator: std.mem.Allocator,
    entry_storage: []Entry,
    entry_count: usize,
    resolver_files: []import_resolver.File,
    diagnostic_indices: []usize,
    build_file_indices: []usize,
    project_fingerprint: [32]u8,

    pub fn init(
        io_context: *compat.Context,
        allocator: std.mem.Allocator,
        file_paths: []const []const u8,
    ) !ProjectSources {
        var context_paths: std.ArrayList([]u8) = .empty;
        defer freeOwnedPaths(allocator, &context_paths);
        for (file_paths) |path| {
            try discoverBuildContext(io_context, allocator, &context_paths, path);
        }

        // Allocate the maximum entry count once. Resolver pointers are not made
        // until every owned AST has reached its final address in this slice.
        const entry_storage = try allocator.alloc(
            Entry,
            file_paths.len + context_paths.items.len,
        );
        errdefer allocator.free(entry_storage);

        var entry_count: usize = 0;
        errdefer {
            for (entry_storage[0..entry_count]) |*entry| entry.deinit(allocator);
        }

        for (file_paths) |path| {
            if (containsPath(entry_storage[0..entry_count], path)) continue;
            entry_storage[entry_count] = try Entry.load(io_context, allocator, path, true);
            entry_count += 1;
        }
        for (context_paths.items) |path| {
            if (containsPath(entry_storage[0..entry_count], path)) continue;
            entry_storage[entry_count] = try Entry.load(io_context, allocator, path, false);
            entry_count += 1;
        }

        std.mem.sort(Entry, entry_storage[0..entry_count], {}, entryLessThan);
        return initViews(allocator, entry_storage, entry_count);
    }

    fn initViews(
        allocator: std.mem.Allocator,
        entry_storage: []Entry,
        entry_count: usize,
    ) !ProjectSources {
        std.debug.assert(entry_count <= entry_storage.len);

        const resolver_files = try allocator.alloc(import_resolver.File, entry_count);
        errdefer allocator.free(resolver_files);

        var diagnostic_count: usize = 0;
        var build_count: usize = 0;
        for (entry_storage[0..entry_count]) |entry| {
            if (entry.diagnostic) diagnostic_count += 1;
            if (isBuildFile(entry.path)) build_count += 1;
        }

        const diagnostic_indices = try allocator.alloc(usize, diagnostic_count);
        errdefer allocator.free(diagnostic_indices);
        const build_file_indices = try allocator.alloc(usize, build_count);
        errdefer allocator.free(build_file_indices);

        var diagnostic_index: usize = 0;
        var build_index: usize = 0;
        for (entry_storage[0..entry_count], 0..) |*entry, index| {
            resolver_files[index] = .{
                .path = entry.path,
                .tree = &entry.tree,
            };
            if (entry.diagnostic) {
                diagnostic_indices[diagnostic_index] = index;
                diagnostic_index += 1;
            }
            if (isBuildFile(entry.path)) {
                build_file_indices[build_index] = index;
                build_index += 1;
            }
        }

        return .{
            .allocator = allocator,
            .entry_storage = entry_storage,
            .entry_count = entry_count,
            .resolver_files = resolver_files,
            .diagnostic_indices = diagnostic_indices,
            .build_file_indices = build_file_indices,
            .project_fingerprint = calculateFingerprint(entry_storage[0..entry_count]),
        };
    }

    pub fn deinit(self: *ProjectSources) void {
        self.allocator.free(self.build_file_indices);
        self.allocator.free(self.diagnostic_indices);
        self.allocator.free(self.resolver_files);
        for (self.entry_storage[0..self.entry_count]) |*entry| {
            entry.deinit(self.allocator);
        }
        self.allocator.free(self.entry_storage);
    }

    /// Returns every selected source and discovered context file.
    pub fn files(self: *const ProjectSources) []const import_resolver.File {
        return self.resolver_files;
    }

    pub fn diagnosticFileIndices(self: *const ProjectSources) []const usize {
        return self.diagnostic_indices;
    }

    pub fn buildFileIndices(self: *const ProjectSources) []const usize {
        return self.build_file_indices;
    }

    /// Returns the number of files selected for diagnostics.
    pub fn count(self: *const ProjectSources) usize {
        return self.diagnostic_indices.len;
    }

    pub fn sourceForPath(
        self: *const ProjectSources,
        path: []const u8,
    ) ?import_resolver.File {
        const file_index = import_resolver.findFileIndexByPath(self.resolver_files, path) orelse
            return null;
        return self.resolver_files[file_index];
    }

    pub fn resolverForPath(
        self: *const ProjectSources,
        path: []const u8,
    ) ?call_resolver.ProjectTypeResolver {
        const file_index = import_resolver.findFileIndexByPath(self.resolver_files, path) orelse
            return null;
        return .{
            .files = self.resolver_files,
            .file_index = file_index,
        };
    }

    pub fn fingerprint(self: *const ProjectSources) *const [32]u8 {
        return &self.project_fingerprint;
    }
};

fn containsPath(entries: []const Entry, path: []const u8) bool {
    for (entries) |entry| {
        if (std.mem.eql(u8, entry.path, path)) return true;
        if (import_resolver.pathsEquivalent(entry.path, path)) return true;
    }
    return false;
}

fn discoverBuildContext(
    io_context: *compat.Context,
    allocator: std.mem.Allocator,
    context_paths: *std.ArrayList([]u8),
    source_path: []const u8,
) !void {
    const source_directory = std.fs.path.dirname(source_path) orelse ".";
    var directory = if (source_directory.len == 0) "." else source_directory;

    var depth: usize = 0;
    while (depth < max_context_depth) : (depth += 1) {
        var candidate_buffer: [std.fs.max_path_bytes]u8 = undefined;
        const candidate = if (std.mem.eql(u8, directory, "/"))
            std.fmt.bufPrint(&candidate_buffer, "/{s}", .{build_file_name}) catch return
        else
            std.fmt.bufPrint(&candidate_buffer, "{s}/{s}", .{ directory, build_file_name }) catch return;

        const found = compat.stat(io_context, candidate) catch null;
        if (found) |kind| {
            if (kind == .file) {
                try appendContextPath(allocator, context_paths, candidate);
                return;
            }
        }

        if (std.mem.eql(u8, directory, ".") or std.mem.eql(u8, directory, "/")) return;
        const parent = std.fs.path.dirname(directory) orelse {
            directory = ".";
            continue;
        };
        if (std.mem.eql(u8, parent, directory)) return;
        directory = if (parent.len == 0) "." else parent;
    }
}

fn appendContextPath(
    allocator: std.mem.Allocator,
    context_paths: *std.ArrayList([]u8),
    path: []const u8,
) !void {
    for (context_paths.items) |existing| {
        if (std.mem.eql(u8, existing, path)) return;
        if (import_resolver.pathsEquivalent(existing, path)) return;
    }

    const owned_path = try allocator.dupe(u8, path);
    errdefer allocator.free(owned_path);
    try context_paths.append(allocator, owned_path);
}

fn freeOwnedPaths(allocator: std.mem.Allocator, paths: *std.ArrayList([]u8)) void {
    for (paths.items) |path| allocator.free(path);
    paths.deinit(allocator);
}

fn isBuildFile(path: []const u8) bool {
    return std.mem.eql(u8, std.fs.path.basename(path), build_file_name);
}

fn entryLessThan(_: void, a: Entry, b: Entry) bool {
    return std.mem.lessThan(u8, a.path, b.path);
}

fn calculateFingerprint(entries: []const Entry) [32]u8 {
    var project_hasher = std.crypto.hash.sha2.Sha256.init(.{});
    project_hasher.update("zwanzig-project-sources-v2\x00");
    for (entries) |entry| {
        project_hasher.update(if (entry.diagnostic) "\x01" else "\x02");
        project_hasher.update(entry.path);
        project_hasher.update("\x00");
        var content_hash: [32]u8 = undefined;
        std.crypto.hash.sha2.Sha256.hash(entry.tree.source, &content_hash, .{});
        project_hasher.update(&content_hash);
    }

    var fingerprint: [32]u8 = undefined;
    project_hasher.final(&fingerprint);
    return fingerprint;
}

test "ProjectSources lends one immutable parsed snapshot to Source" {
    const Source = @import("source.zig").Source;
    const allocator = std.testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    const original = "pub const original: u8 = 1;\n";
    const replacement = "pub const replacement: u8 = 2;\n";
    try temp_dir.writeFile("snapshot.zig", original);

    var path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const path = try std.fmt.bufPrint(
        &path_buffer,
        "{s}/snapshot.zig",
        .{temp_dir.path()},
    );
    const selected_files = [_][]const u8{path};

    var project = try ProjectSources.init(&io_context, allocator, &selected_files);
    defer project.deinit();

    const registered = project.sourceForPath(path) orelse return error.MissingSource;
    try temp_dir.writeFile("snapshot.zig", replacement);
    {
        var source = Source.initParsed(allocator, registered.path, registered.tree);
        defer source.deinit();

        try std.testing.expect(source.findDecl("original") != null);
        try std.testing.expect(source.findDecl("replacement") == null);
    }

    var source = Source.initParsed(allocator, registered.path, registered.tree);
    defer source.deinit();
    try std.testing.expect(source.findDecl("original") != null);
    try std.testing.expect(source.findDecl("replacement") == null);
}

test "ProjectSources fingerprints discovered build context" {
    const allocator = std.testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    const build_before =
        "const std = @import(\"std\");\n" ++
        "pub fn build(b: *std.Build) void {\n" ++
        "    _ = b.addModule(\"fixture\", .{ .root_source_file = b.path(\"api.zig\") });\n" ++
        "}\n";
    const build_after =
        "const std = @import(\"std\");\n" ++
        "pub fn build(b: *std.Build) void {\n" ++
        "    _ = b.addModule(\"renamed\", .{ .root_source_file = b.path(\"api.zig\") });\n" ++
        "}\n";
    try temp_dir.writeFile("build.zig", build_before);
    try temp_dir.writeFile("api.zig", "pub fn exported() void {}\n");

    var path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const source_path = try std.fmt.bufPrint(
        &path_buffer,
        "{s}/api.zig",
        .{temp_dir.path()},
    );
    const selected_files = [_][]const u8{source_path};

    const fingerprint_before = blk: {
        var project = try ProjectSources.init(&io_context, allocator, &selected_files);
        defer project.deinit();
        break :blk project.fingerprint().*;
    };

    try temp_dir.writeFile("build.zig", build_after);
    var project_after = try ProjectSources.init(&io_context, allocator, &selected_files);
    defer project_after.deinit();

    try std.testing.expect(!std.mem.eql(
        u8,
        &fingerprint_before,
        project_after.fingerprint(),
    ));
}

test "ProjectSources releases partial discovered context state" {
    const allocator = std.testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile(
        "build.zig",
        "const std = @import(\"std\");\n" ++
            "pub fn build(b: *std.Build) void {\n" ++
            "    _ = b.addModule(\"fixture\", .{ .root_source_file = b.path(\"api.zig\") });\n" ++
            "}\n",
    );
    try temp_dir.writeFile("api.zig", "pub fn exported() void {}\n");

    var path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const source_path = try std.fmt.bufPrint(
        &path_buffer,
        "{s}/api.zig",
        .{temp_dir.path()},
    );
    const selected_files = [_][]const u8{source_path};

    const Harness = struct {
        fn run(
            failing_allocator: std.mem.Allocator,
            io_context_ptr: *compat.Context,
            paths: []const []const u8,
        ) !void {
            var project = try ProjectSources.init(
                io_context_ptr,
                failing_allocator,
                paths,
            );
            defer project.deinit();
            try std.testing.expectEqual(@as(usize, 1), project.count());
            try std.testing.expectEqual(@as(usize, 2), project.files().len);
        }
    };
    try std.testing.checkAllAllocationFailures(
        allocator,
        Harness.run,
        .{ &io_context, &selected_files },
    );
}
