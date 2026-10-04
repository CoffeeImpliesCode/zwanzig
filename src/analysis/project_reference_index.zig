const std = @import("std");
const ast_walk = @import("../ast_walk.zig");
const import_resolver = @import("import_resolver.zig");
const ProjectTypeResolver = @import("call_resolver.zig").ProjectTypeResolver;

/// No build script supplied a name table for this file set.
const no_module_names: import_resolver.ModuleNames = .empty;

/// Invocation-owned namespace edges. Resolver files and their ASTs remain borrowed.
pub const ProjectReferenceIndex = struct {
    arena: std.heap.ArenaAllocator,
    files: []const import_resolver.File,
    file_indexes: []FileIndex = &.{},
    exact_paths: FileLists = .empty,
    normalized_paths: FileLists = .empty,
    package_names: FileLists = .empty,
    entries: std.ArrayList(Entry) = .empty,
    entry_ids: std.AutoHashMapUnmanaged(Key, usize) = .empty,
    edges: std.AutoHashMapUnmanaged(Edge, void) = .empty,
    pending: std.ArrayList(Fact) = .empty,
    cursor: usize = 0,

    const Error = std.mem.Allocator.Error;
    const FileLists = std.StringHashMapUnmanaged(std.ArrayList(usize));
    const Kind = enum { initializer, namespace, public_file, using_file };
    const Key = struct { file: usize, node: u32 = 0, kind: Kind };
    const Edge = struct { source: usize, target: usize };
    const Fact = struct { entry: usize, file: usize };
    const MemberLink = struct { target: usize, name: []const u8 };
    const ImportUse = struct { path: []const u8, public: bool };
    const FileIndex = struct {
        members: std.StringHashMapUnmanaged(std.ArrayList(u32)) = .empty,
        imports: std.StringHashMapUnmanaged([]const usize) = .empty,
        using_namespaces: std.ArrayList(ImportUse) = .empty,
    };
    const Entry = struct {
        files: std.ArrayList(usize) = .empty,
        membership: std.AutoHashMapUnmanaged(usize, void) = .empty,
        dependents: std.ArrayList(usize) = .empty,
        member_dependents: std.ArrayList(MemberLink) = .empty,
    };

    pub fn init(allocator: std.mem.Allocator, files: []const import_resolver.File) Error!ProjectReferenceIndex {
        var self = ProjectReferenceIndex{ .arena = std.heap.ArenaAllocator.init(allocator), .files = files };
        errdefer self.deinit();
        const arena = self.arena.allocator();
        self.file_indexes = try arena.alloc(FileIndex, files.len);
        @memset(self.file_indexes, .{});
        for (files, 0..) |file, file_index| {
            try appendFile(arena, &self.exact_paths, file.path, file_index);
            var buffer: [std.fs.max_path_bytes]u8 = undefined;
            if (import_resolver.normalizePath(&buffer, file.path)) |normalized| {
                try appendFile(arena, &self.normalized_paths, normalized, file_index);
            } else |_| {}
            const basename = std.fs.path.basename(file.path);
            if (std.mem.endsWith(u8, basename, ".zig")) {
                try appendFile(arena, &self.package_names, basename[0 .. basename.len - 4], file_index);
            }
            const tree = file.tree;
            // Keep malformed files addressable without trusting recovered syntax.
            if (tree.errors.len != 0) continue;
            for (tree.rootDecls()) |decl| {
                const full = tree.fullVarDecl(decl) orelse continue;
                const public = full.visib_token orelse continue;
                if (tree.tokenTag(public) != .keyword_pub) continue;
                const name_token = full.ast.mut_token + 1;
                if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
                const initializer = full.ast.init_node.unwrap() orelse continue;
                const name = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token));
                const member = try self.file_indexes[file_index].members.getOrPut(arena, name);
                if (!member.found_existing) member.value_ptr.* = .empty;
                try member.value_ptr.append(arena, @intFromEnum(initializer));
            }
            const token_tags = tree.tokens.items(.tag);
            for (token_tags, 0..) |_, token_index| {
                if (!std.mem.eql(u8, tree.tokenSlice(@intCast(token_index)), "usingnamespace")) continue;
                const import_token = import_resolver.nextNonCommentToken(token_tags, token_index + 1) orelse continue;
                if (!std.mem.eql(u8, tree.tokenSlice(@intCast(import_token)), "@import")) continue;
                const path = import_resolver.importPathFromBuiltinToken(tree, import_token) orelse continue;
                const previous = import_resolver.prevNonCommentToken(token_tags, token_index);
                try self.file_indexes[file_index].using_namespaces.append(arena, .{
                    .path = path,
                    .public = if (previous) |token| tree.tokenTag(@intCast(token)) == .keyword_pub else false,
                });
            }
        }
        return self;
    }

    pub fn deinit(self: *ProjectReferenceIndex) void {
        self.arena.deinit();
    }

    pub fn publicTargets(self: *ProjectReferenceIndex, file: usize) Error![]const usize {
        return self.targets(.{ .file = file, .kind = .public_file });
    }

    pub fn usingTargets(self: *ProjectReferenceIndex, file: usize) Error![]const usize {
        return self.targets(.{ .file = file, .kind = .using_file });
    }

    pub fn namespaceTargets(self: *ProjectReferenceIndex, file: usize, node: u32) Error![]const usize {
        return self.targets(.{ .file = file, .node = node, .kind = .namespace });
    }

    fn targets(self: *ProjectReferenceIndex, key: Key) Error![]const usize {
        const entry = try self.ensure(key);
        try self.drain();
        return self.entries.items[entry].files.items;
    }

    fn appendFile(allocator: std.mem.Allocator, map: *FileLists, name: []const u8, file: usize) Error!void {
        const result = try map.getOrPut(allocator, name);
        if (!result.found_existing) {
            result.key_ptr.* = try allocator.dupe(u8, name);
            result.value_ptr.* = .empty;
        }
        try result.value_ptr.append(allocator, file);
    }

    fn appendMatching(self: *ProjectReferenceIndex, result: *std.ArrayList(usize), candidates: []const usize, file: usize, path: []const u8) Error!void {
        for (candidates) |candidate| {
            if (!import_resolver.importMayResolveToPath(self.files[file].path, path, self.files[candidate].path)) continue;
            if (std.mem.indexOfScalar(usize, result.items, candidate) != null) continue;
            try result.append(self.arena.allocator(), candidate);
        }
    }

    /// Build-registered import names shared with the path resolver, so both
    /// spellings of an import name answer from the same build context.
    fn moduleNames(self: *const ProjectReferenceIndex) *const import_resolver.ModuleNames {
        if (self.files.len != 0) {
            if (self.files[0].path_index) |index| return &index.module_names;
        }
        return &no_module_names;
    }

    fn importTargets(self: *ProjectReferenceIndex, file: usize, path: []const u8) Error![]const usize {
        if (self.file_indexes[file].imports.get(path)) |cached| return cached;
        var result: std.ArrayList(usize) = .empty;
        if (self.exact_paths.get(path)) |candidates| try self.appendMatching(&result, candidates.items, file, path);
        const directory = std.fs.path.dirname(self.files[file].path) orelse "";
        var joined_buffer: [std.fs.max_path_bytes]u8 = undefined;
        const joined = if (directory.len == 0) path else std.fmt.bufPrint(&joined_buffer, "{s}/{s}", .{ directory, path }) catch "";
        var normalized_buffer: [std.fs.max_path_bytes]u8 = undefined;
        if (import_resolver.normalizePath(&normalized_buffer, joined)) |normalized| {
            if (self.normalized_paths.get(normalized)) |candidates| {
                try self.appendMatching(&result, candidates.items, file, path);
            }
        } else |_| {}
        // A build-registered name names one module root, and the basename stem
        // cannot tell that root from an unrelated file sharing its stem, so the
        // registration is the only answer for a name the build binds.
        if (import_resolver.registeredModuleTarget(self.moduleNames(), path)) |registered| {
            try result.append(self.arena.allocator(), registered);
        } else if (self.package_names.get(path)) |candidates| {
            try self.appendMatching(&result, candidates.items, file, path);
        }
        // usingnamespace follows the first matching file, just like the resolver.
        std.mem.sort(usize, result.items, {}, std.sort.asc(usize));
        try self.file_indexes[file].imports.put(self.arena.allocator(), path, result.items);
        return result.items;
    }

    fn ensure(self: *ProjectReferenceIndex, key: Key) Error!usize {
        if (self.entry_ids.get(key)) |entry| return entry;
        const entry = self.entries.items.len;
        try self.entries.append(self.arena.allocator(), .{});
        try self.entry_ids.put(self.arena.allocator(), key, entry);
        // Register before following aliases so a cycle becomes an edge, not recursion.
        try self.expand(entry, key);
        return entry;
    }

    fn emit(self: *ProjectReferenceIndex, entry: usize, file: usize) Error!void {
        const result = try self.entries.items[entry].membership.getOrPut(self.arena.allocator(), file);
        if (result.found_existing) return;
        try self.entries.items[entry].files.append(self.arena.allocator(), file);
        try self.pending.append(self.arena.allocator(), .{ .entry = entry, .file = file });
    }

    fn connect(self: *ProjectReferenceIndex, source: usize, target: usize) Error!void {
        const edge = try self.edges.getOrPut(self.arena.allocator(), .{ .source = source, .target = target });
        if (edge.found_existing) return;
        try self.entries.items[source].dependents.append(self.arena.allocator(), target);
        const files = self.entries.items[source].files.items;
        for (files) |file| try self.emit(target, file);
    }

    fn linkMember(self: *ProjectReferenceIndex, file: usize, link: MemberLink) Error!void {
        const members = self.file_indexes[file].members.get(link.name) orelse return;
        for (members.items) |node| {
            const source = try self.ensure(.{ .file = file, .node = node, .kind = .initializer });
            try self.connect(source, link.target);
        }
    }

    fn drain(self: *ProjectReferenceIndex) Error!void {
        while (self.cursor < self.pending.items.len) : (self.cursor += 1) {
            const fact = self.pending.items[self.cursor];
            const dependents = self.entries.items[fact.entry].dependents.items;
            for (dependents) |target| try self.emit(target, fact.file);
            const members = self.entries.items[fact.entry].member_dependents.items;
            for (members) |link| try self.linkMember(fact.file, link);
        }
    }

    fn expand(self: *ProjectReferenceIndex, entry: usize, key: Key) Error!void {
        const tree = self.files[key.file].tree;
        if (tree.errors.len != 0) return;
        switch (key.kind) {
            .public_file, .using_file => {
                if (key.kind == .public_file) {
                    var members = self.file_indexes[key.file].members.valueIterator();
                    while (members.next()) |nodes| {
                        for (nodes.items) |node| {
                            const source = try self.ensure(.{ .file = key.file, .node = node, .kind = .initializer });
                            try self.connect(source, entry);
                        }
                    }
                }
                for (self.file_indexes[key.file].using_namespaces.items) |namespace| {
                    if (key.kind == .public_file and !namespace.public) continue;
                    const files = try self.importTargets(key.file, namespace.path);
                    for (files) |file| try self.emit(entry, file);
                    if (files.len != 0) {
                        const source = try self.ensure(.{ .file = files[0], .kind = .public_file });
                        try self.connect(source, entry);
                    }
                }
            },
            .namespace => {
                if (key.node >= tree.nodes.len) return;
                switch (tree.nodes.items(.tag)[key.node]) {
                    .identifier, .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                        const source = try self.ensure(.{ .file = key.file, .node = key.node, .kind = .initializer });
                        try self.connect(source, entry);
                    },
                    .field_access => {
                        const access = tree.nodes.items(.data)[key.node].node_and_token;
                        const source = try self.ensure(.{ .file = key.file, .node = @intFromEnum(access[0]), .kind = .namespace });
                        const link = MemberLink{ .target = entry, .name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1])) };
                        try self.entries.items[source].member_dependents.append(self.arena.allocator(), link);
                        const files = self.entries.items[source].files.items;
                        for (files) |file| try self.linkMember(file, link);
                    },
                    else => {},
                }
            },
            .initializer => {
                if (key.node >= tree.nodes.len) return;
                switch (tree.nodes.items(.tag)[key.node]) {
                    .identifier => {
                        const resolver = ProjectTypeResolver{ .files = self.files, .file_index = key.file };
                        const declaration = resolver.resolveDeclarationNode(key.node) orelse return;
                        const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return;
                        const initializer = full.ast.init_node.unwrap() orelse return;
                        const source = try self.ensure(.{ .file = key.file, .node = @intFromEnum(initializer), .kind = .initializer });
                        try self.connect(source, entry);
                    },
                    .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                        const path = import_resolver.importPathFromBuiltinCall(tree, key.node) orelse return;
                        for (try self.importTargets(key.file, path)) |file| try self.emit(entry, file);
                    },
                    .call,
                    .call_comma,
                    .call_one,
                    .call_one_comma,
                    .struct_init,
                    .struct_init_comma,
                    .struct_init_one,
                    .struct_init_one_comma,
                    .struct_init_dot,
                    .struct_init_dot_comma,
                    .struct_init_dot_two,
                    .struct_init_dot_two_comma,
                    .array_init,
                    .array_init_comma,
                    .array_init_one,
                    .array_init_one_comma,
                    .array_init_dot,
                    .array_init_dot_comma,
                    .array_init_dot_two,
                    .array_init_dot_two_comma,
                    => {},
                    else => {
                        var children = InitializerChildren{ .index = self, .entry = entry, .file = key.file };
                        if (tree.fullIf(@enumFromInt(key.node))) |full| {
                            try InitializerChildren.visit(tree, @intFromEnum(full.ast.then_expr), &children);
                            if (full.ast.else_expr.unwrap()) |alternative| {
                                try InitializerChildren.visit(tree, @intFromEnum(alternative), &children);
                            }
                        } else {
                            try ast_walk.walkChildren(InitializerChildren, tree, key.node, &children, InitializerChildren.visit);
                        }
                    },
                }
            },
        }
    }

    const InitializerChildren = struct {
        index: *ProjectReferenceIndex,
        entry: usize,
        file: usize,

        fn visit(_: *const std.zig.Ast, node: u32, self: *InitializerChildren) Error!void {
            const source = try self.index.ensure(.{ .file = self.file, .node = node, .kind = .initializer });
            try self.index.connect(source, self.entry);
        }
    };
};

test "reference index propagates imports through cyclic aliases" {
    const allocator = std.testing.allocator;
    var root = try std.zig.Ast.parse(allocator,
        \\const first = second;
        \\const second = if (true) first else @import("leaf.zig");
        \\pub const exposed = first;
    , .zig);
    defer root.deinit(allocator);
    var leaf = try std.zig.Ast.parse(allocator, "", .zig);
    defer leaf.deinit(allocator);
    const files = [_]import_resolver.File{
        .{ .path = "root.zig", .tree = &root },
        .{ .path = "leaf.zig", .tree = &leaf },
    };
    var index = try ProjectReferenceIndex.init(allocator, &files);
    defer index.deinit();
    try std.testing.expectEqualSlices(usize, &.{1}, try index.publicTargets(0));
    const declaration = root.fullVarDecl(root.rootDecls()[0]) orelse return error.TestUnexpectedResult;
    const initializer = declaration.ast.init_node.unwrap() orelse return error.TestUnexpectedResult;
    try std.testing.expectEqualSlices(usize, &.{1}, try index.namespaceTargets(0, @intFromEnum(initializer)));
}

test "reference index isolates unsupported usingnamespace syntax from valid siblings" {
    const allocator = std.testing.allocator;
    var root = try std.zig.Ast.parse(allocator, "pub usingnamespace @import(\"facade.zig\");", .zig);
    defer root.deinit(allocator);
    var facade = try std.zig.Ast.parse(allocator,
        \\pub usingnamespace @import("root.zig");
        \\pub usingnamespace @import("leaf.zig");
    , .zig);
    defer facade.deinit(allocator);
    var leaf = try std.zig.Ast.parse(allocator, "pub const api = @import(\"sibling.zig\");", .zig);
    defer leaf.deinit(allocator);
    var sibling = try std.zig.Ast.parse(allocator, "pub const value = 1;", .zig);
    defer sibling.deinit(allocator);
    try std.testing.expect(root.errors.len != 0);
    try std.testing.expect(facade.errors.len != 0);
    try std.testing.expectEqual(@as(usize, 0), leaf.errors.len);
    try std.testing.expectEqual(@as(usize, 0), sibling.errors.len);
    const files = [_]import_resolver.File{
        .{ .path = "root.zig", .tree = &root },
        .{ .path = "facade.zig", .tree = &facade },
        .{ .path = "leaf.zig", .tree = &leaf },
        .{ .path = "sibling.zig", .tree = &sibling },
    };
    const Harness = struct {
        fn run(failing_allocator: std.mem.Allocator, sources: []const import_resolver.File) !void {
            var index = try ProjectReferenceIndex.init(failing_allocator, sources);
            defer index.deinit();
            for (0..2) |file_index| {
                try std.testing.expectEqual(@as(usize, 0), (try index.publicTargets(file_index)).len);
                try std.testing.expectEqual(@as(usize, 0), (try index.usingTargets(file_index)).len);
                for (0..sources[file_index].tree.nodes.len) |node| {
                    try std.testing.expectEqual(@as(usize, 0), (try index.namespaceTargets(file_index, @intCast(node))).len);
                }
            }
            try std.testing.expectEqualSlices(usize, &.{3}, try index.publicTargets(2));
            const tree = sources[2].tree;
            const declaration = tree.fullVarDecl(tree.rootDecls()[0]) orelse return error.TestUnexpectedResult;
            const initializer = declaration.ast.init_node.unwrap() orelse return error.TestUnexpectedResult;
            try std.testing.expectEqualSlices(usize, &.{3}, try index.namespaceTargets(2, @intFromEnum(initializer)));
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Harness.run, .{@as([]const import_resolver.File, &files)});
}

test "reference index keeps malformed import targets without scanning their exports" {
    const allocator = std.testing.allocator;
    var root = try std.zig.Ast.parse(allocator,
        \\pub const malformed = @import("malformed.zig");
        \\pub const leaf = @import("leaf.zig");
    , .zig);
    defer root.deinit(allocator);
    var malformed = try std.zig.Ast.parse(allocator,
        \\pub const leaked = @import("hidden.zig");
        \\pub usingnamespace @import("hidden.zig");
        \\const broken = ;
    , .zig);
    defer malformed.deinit(allocator);
    try std.testing.expect(malformed.errors.len != 0);
    var leaf = try std.zig.Ast.parse(allocator, "pub const value = 1;", .zig);
    defer leaf.deinit(allocator);
    const files = [_]import_resolver.File{
        .{ .path = "root.zig", .tree = &root },
        .{ .path = "malformed.zig", .tree = &malformed },
        .{ .path = "leaf.zig", .tree = &leaf },
        .{ .path = "hidden.zig", .tree = &leaf },
    };
    const Harness = struct {
        fn run(failing_allocator: std.mem.Allocator, sources: []const import_resolver.File) !void {
            var index = try ProjectReferenceIndex.init(failing_allocator, sources);
            defer index.deinit();
            const public = try index.publicTargets(0);
            try std.testing.expectEqual(@as(usize, 2), public.len);
            try std.testing.expect(std.mem.indexOfScalar(usize, public, 1) != null);
            try std.testing.expect(std.mem.indexOfScalar(usize, public, 2) != null);
            try std.testing.expectEqual(@as(usize, 0), (try index.publicTargets(1)).len);
            try std.testing.expectEqual(@as(usize, 0), (try index.usingTargets(1)).len);
            for (0..sources[1].tree.nodes.len) |node| {
                try std.testing.expectEqual(@as(usize, 0), (try index.namespaceTargets(1, @intCast(node))).len);
            }
            const tree = sources[0].tree;
            const declaration = tree.fullVarDecl(tree.rootDecls()[0]) orelse return error.TestUnexpectedResult;
            const initializer = declaration.ast.init_node.unwrap() orelse return error.TestUnexpectedResult;
            try std.testing.expectEqualSlices(usize, &.{1}, try index.namespaceTargets(0, @intFromEnum(initializer)));
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Harness.run, .{@as([]const import_resolver.File, &files)});
}

test "reference index keeps namespace member and shadowed alias targets distinct" {
    const allocator = std.testing.allocator;
    var root = try std.zig.Ast.parse(allocator,
        \\const facade = @import("facade.zig");
        \\pub const direct = facade;
        \\pub fn run() void {
        \\    _ = facade.api.used;
        \\    const facade = struct { const api = struct { const used = 0; }; };
        \\    _ = facade.api.used;
        \\}
    , .zig);
    defer root.deinit(allocator);
    var facade = try std.zig.Ast.parse(allocator, "pub const api = @import(\"leaf.zig\");", .zig);
    defer facade.deinit(allocator);
    var leaf = try std.zig.Ast.parse(allocator, "pub const used = 1;", .zig);
    defer leaf.deinit(allocator);
    const files = [_]import_resolver.File{
        .{ .path = "root.zig", .tree = &root },
        .{ .path = "facade.zig", .tree = &facade },
        .{ .path = "leaf.zig", .tree = &leaf },
    };
    var index = try ProjectReferenceIndex.init(allocator, &files);
    defer index.deinit();
    var matched: usize = 0;
    for (root.nodes.items(.tag), 0..) |tag, node| {
        if (tag != .field_access) continue;
        const name = import_resolver.fieldAccessName(&root, node) orelse return error.TestUnexpectedResult;
        if (!std.mem.eql(u8, name, "api")) continue;
        const actual = try index.namespaceTargets(0, @intCast(node));
        for (files, 0..) |file, file_index| {
            const expected = import_resolver.nodeImportsPath(&files, &root, node, files[0].path, file.path);
            try std.testing.expectEqual(expected, std.mem.indexOfScalar(usize, actual, file_index) != null);
        }
        matched += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), matched);
}
