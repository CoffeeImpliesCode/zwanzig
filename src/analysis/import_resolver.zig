const std = @import("std");
const ast_walk = @import("../ast_walk.zig");
const ProjectTypeResolver = @import("call_resolver.zig").ProjectTypeResolver;
const LexicalIndex = @import("lexical_index.zig").LexicalIndex;

pub const File = struct {
    path: []const u8,
    tree: *const std.zig.Ast,
    /// Optional immutable metadata borrowed from the owner of this AST.
    lexical_index: ?*const LexicalIndex = null,
    path_index: ?*const PathIndex = null,
};

/// Owns normalized keys and borrows the immutable file slice and exact paths.
pub const PathIndex = struct {
    files: []const File,
    exact: std.StringHashMapUnmanaged(usize) = .empty,
    normalized: std.StringHashMapUnmanaged(usize) = .empty,

    pub fn init(allocator: std.mem.Allocator, files: []const File) !PathIndex {
        var index = PathIndex{ .files = files };
        errdefer index.deinit(allocator);
        for (files, 0..) |file, file_index| {
            const first_equivalent = normalized: {
                var buffer: [std.fs.max_path_bytes]u8 = undefined;
                const path = normalizePath(&buffer, file.path) catch break :normalized file_index;
                if (index.normalized.get(path)) |existing| break :normalized existing;
                const owned = try allocator.dupe(u8, path);
                errdefer allocator.free(owned);
                try index.normalized.put(allocator, owned, file_index);
                break :normalized file_index;
            };
            const exact = try index.exact.getOrPut(allocator, file.path);
            if (!exact.found_existing) exact.value_ptr.* = first_equivalent;
        }
        return index;
    }

    pub fn deinit(self: *PathIndex, allocator: std.mem.Allocator) void {
        var keys = self.normalized.keyIterator();
        while (keys.next()) |key| allocator.free(key.*);
        self.normalized.deinit(allocator);
        self.exact.deinit(allocator);
    }

    pub fn find(self: *const PathIndex, path: []const u8) ?usize {
        // Exact spellings already point to the first normalized equivalent.
        if (self.exact.get(path)) |file_index| return file_index;
        var buffer: [std.fs.max_path_bytes]u8 = undefined;
        const normalized = normalizePath(&buffer, path) catch return null;
        return self.normalized.get(normalized);
    }
};

pub fn findFileIndexByPath(files: []const File, path: []const u8) ?usize {
    if (files.len != 0) {
        if (files[0].path_index) |index| {
            // A borrowed File may also appear in a caller's subset or fixture.
            if (index.files.ptr == files.ptr and index.files.len == files.len) return index.find(path);
        }
    }
    for (files, 0..) |file, file_index| {
        if (std.mem.eql(u8, file.path, path) or pathsEquivalent(file.path, path)) return file_index;
    }
    return null;
}

pub fn filePubliclyImportsPath(files: []const File, file_index: usize, target_path: []const u8) bool {
    var visited: [64]usize = undefined;
    return filePubliclyImportsPathVisited(files, file_index, target_path, &visited, 0);
}

fn filePubliclyImportsPathVisited(
    files: []const File,
    file_index: usize,
    target_path: []const u8,
    visited: *[64]usize,
    depth: usize,
) bool {
    if (depth >= visited.len) return false;
    if (std.mem.indexOfScalar(usize, visited[0..depth], file_index) != null) return false;
    visited[depth] = file_index;
    if (file_index >= files.len) return false;

    const file = files[file_index];
    if (file.tree.errors.len != 0) return false;
    const tags = file.tree.nodes.items(.tag);

    for (file.tree.rootDecls()) |decl_idx| {
        const idx = @intFromEnum(decl_idx);
        if (idx >= tags.len) continue;
        if (!isVarDeclTag(tags[idx])) continue;
        if (publicVarDeclImportsPath(file, @intCast(idx), target_path)) return true;
    }
    return usingnamespaceImportsPathVisited(files, file.tree, file.path, target_path, true, visited, depth + 1);
}

pub fn nodeImportsPath(
    files: []const File,
    tree: *const std.zig.Ast,
    node: usize,
    importer_path: []const u8,
    target_path: []const u8,
) bool {
    if (tree.errors.len != 0) return false;
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;

    switch (tags[node]) {
        .identifier => {
            if (findFileIndexByPath(files, importer_path)) |file_index| {
                if (files[file_index].tree == tree) return initNodeImportsFile(files[file_index], node, target_path);
            }
            return initNodeImportsPath(tree, node, importer_path, target_path);
        },
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => {
            const import_path = importPathFromBuiltinCall(tree, node) orelse return false;
            return importMayResolveToPath(importer_path, import_path, target_path);
        },
        .field_access => {
            const datas = tree.nodes.items(.data);
            const lhs = @intFromEnum(datas[node].node_and_token[0]);
            const field_name = normalizeIdentifier(tree.tokenSlice(datas[node].node_and_token[1]));

            for (files, 0..) |candidate, candidate_index| {
                if (!nodeImportsPath(files, tree, lhs, importer_path, candidate.path)) continue;
                if (filePublicMemberImportsPath(files, candidate_index, field_name, target_path)) return true;
            }
            return false;
        },
        else => return false,
    }
}

pub fn fileUsingnamespaceImportsPath(
    files: []const File,
    tree: *const std.zig.Ast,
    importer_path: []const u8,
    target_path: []const u8,
) bool {
    var visited: [64]usize = undefined;
    return usingnamespaceImportsPathVisited(files, tree, importer_path, target_path, false, &visited, 0);
}

fn usingnamespaceImportsPathVisited(
    files: []const File,
    tree: *const std.zig.Ast,
    importer_path: []const u8,
    target_path: []const u8,
    public_only: bool,
    visited: *[64]usize,
    depth: usize,
) bool {
    if (tree.errors.len != 0) return false;
    const token_tags = tree.tokens.items(.tag);

    for (token_tags, 0..) |_, token_index| {
        if (!std.mem.eql(u8, tree.tokenSlice(@intCast(token_index)), "usingnamespace")) continue;

        if (public_only) {
            const pub_token = prevNonCommentToken(token_tags, token_index) orelse continue;
            if (tree.tokenTag(@intCast(pub_token)) != .keyword_pub) continue;
        }

        const import_token = nextNonCommentToken(token_tags, token_index + 1) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(@intCast(import_token)), "@import")) continue;

        const import_path = importPathFromBuiltinToken(tree, import_token) orelse continue;
        if (importMayResolveToPath(importer_path, import_path, target_path)) return true;
        if (resolveImportToFileIndex(files, importer_path, import_path)) |file_index| {
            if (filePubliclyImportsPathVisited(files, file_index, target_path, visited, depth)) return true;
        }
    }

    return false;
}

pub fn initNodeImportsPath(
    tree: *const std.zig.Ast,
    node: usize,
    importer_path: []const u8,
    target_path: []const u8,
) bool {
    return initNodeImportsFile(.{ .path = importer_path, .tree = tree }, node, target_path);
}

fn initNodeImportsFile(file: File, node: usize, target_path: []const u8) bool {
    var visited: [64]u32 = undefined;
    return initNodeImportsPathVisited(file, node, target_path, &visited, 0);
}

fn initNodeImportsPathVisited(
    file: File,
    node: usize,
    target_path: []const u8,
    visited: *[64]u32,
    depth: usize,
) bool {
    const tree = file.tree;
    if (tree.errors.len != 0) return false;
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or depth >= visited.len) return false;

    switch (tags[node]) {
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => {
            const import_path = importPathFromBuiltinCall(tree, node) orelse return false;
            return importMayResolveToPath(file.path, import_path, target_path);
        },
        .identifier => {
            const alias_node: u32 = @intCast(node);
            return aliasInitImportsPath(
                file,
                alias_node,
                target_path,
                visited,
                depth,
            );
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
        => return false,
        else => {
            var scanner = InitPathScanner{
                .file = file,
                .target_path = target_path,
                .visited = visited,
                .depth = depth,
            };
            if (tree.fullIf(@enumFromInt(node))) |full| {
                InitPathScanner.visit(tree, @intFromEnum(full.ast.then_expr), &scanner) catch return false;
                if (full.ast.else_expr.unwrap()) |alternative| {
                    InitPathScanner.visit(tree, @intFromEnum(alternative), &scanner) catch return false;
                }
            } else {
                ast_walk.walkChildren(InitPathScanner, tree, @intCast(node), &scanner, InitPathScanner.visit) catch return false;
            }
            return scanner.found;
        },
    }
}

fn aliasInitImportsPath(
    file: File,
    alias_node: u32,
    target_path: []const u8,
    visited: *[64]u32,
    depth: usize,
) bool {
    const tree = file.tree;
    const files = [_]File{file};
    const resolver = ProjectTypeResolver{ .files = &files, .file_index = 0 };
    const decl_node = resolver.resolveDeclarationNode(alias_node) orelse return false;
    if (std.mem.indexOfScalar(u32, visited[0..depth], decl_node) != null) return false;
    const full = tree.fullVarDecl(@enumFromInt(decl_node)) orelse return false;
    const init_node = full.ast.init_node.unwrap() orelse return false;
    visited[depth] = decl_node;
    return initNodeImportsPathVisited(
        file,
        @intFromEnum(init_node),
        target_path,
        visited,
        depth + 1,
    );
}

pub fn importPathFromBuiltinCall(tree: *const std.zig.Ast, node_idx: usize) ?[]const u8 {
    const main_tokens = tree.nodes.items(.main_token);
    if (node_idx >= main_tokens.len) return null;
    const token = main_tokens[node_idx];
    if (token >= tree.tokens.len) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(token), "@import")) return null;

    const token_tags = tree.tokens.items(.tag);
    var scan_token = token + 1;
    const end_token = @min(token_tags.len, token + 6);
    while (scan_token < end_token) : (scan_token += 1) {
        if (token_tags[scan_token] != .string_literal) continue;
        const literal = tree.tokenSlice(scan_token);
        if (literal.len < 2) return null;
        return literal[1 .. literal.len - 1];
    }
    return null;
}

pub fn importPathFromBuiltinToken(tree: *const std.zig.Ast, token: usize) ?[]const u8 {
    const token_tags = tree.tokens.items(.tag);
    const l_paren = nextNonCommentToken(token_tags, token + 1) orelse return null;
    if (token_tags[l_paren] != .l_paren) return null;

    const string_token = nextNonCommentToken(token_tags, l_paren + 1) orelse return null;
    if (token_tags[string_token] != .string_literal) return null;

    const literal = tree.tokenSlice(@intCast(string_token));
    if (literal.len < 2) return null;
    return literal[1 .. literal.len - 1];
}

pub fn importResolvesToPath(importer_path: []const u8, import_path: []const u8, target_path: []const u8) bool {
    if (std.mem.eql(u8, import_path, target_path)) return true;
    if (distinctPathLeaves(import_path, target_path)) return false;

    const importer_dir = std.fs.path.dirname(importer_path) orelse "";
    if (importer_dir.len == 0) return pathsEquivalent(import_path, target_path);

    var resolved_buf: [std.fs.max_path_bytes]u8 = undefined;
    const resolved = std.fmt.bufPrint(&resolved_buf, "{s}/{s}", .{ importer_dir, import_path }) catch return false;
    return pathsEquivalent(resolved, target_path);
}

pub fn importMayResolveToPath(importer_path: []const u8, import_path: []const u8, target_path: []const u8) bool {
    if (importResolvesToPath(importer_path, import_path, target_path)) return true;
    return packageImportMayResolveToPath(import_path, target_path);
}

pub fn resolveImportToFileIndex(files: []const File, importer_path: []const u8, import_path: []const u8) ?usize {
    for (files, 0..) |file, file_index| {
        if (importMayResolveToPath(importer_path, import_path, file.path)) return file_index;
    }
    return null;
}

pub fn packageImportMayResolveToPath(import_path: []const u8, target_path: []const u8) bool {
    if (std.mem.indexOfScalar(u8, import_path, '/') != null) return false;
    if (std.mem.endsWith(u8, import_path, ".zig")) return false;

    const basename = std.fs.path.basename(target_path);
    if (!std.mem.endsWith(u8, basename, ".zig")) return false;
    const stem = basename[0 .. basename.len - ".zig".len];
    return std.mem.eql(u8, stem, import_path);
}

pub fn pathsEquivalent(a: []const u8, b: []const u8) bool {
    if (distinctPathLeaves(a, b)) return false;
    var a_buf: [std.fs.max_path_bytes]u8 = undefined;
    var b_buf: [std.fs.max_path_bytes]u8 = undefined;
    const normalized_a = normalizePath(&a_buf, a) catch return false;
    const normalized_b = normalizePath(&b_buf, b) catch return false;
    return std.mem.eql(u8, normalized_a, normalized_b);
}

fn distinctPathLeaves(a: []const u8, b: []const u8) bool {
    // Match normalizePath's slash-only syntax on every host.
    const a_leaf = std.fs.path.basenamePosix(a);
    const b_leaf = std.fs.path.basenamePosix(b);
    // Dot components can change the final segment during normalization.
    if (a_leaf.len == 0 or b_leaf.len == 0) return false;
    if (std.mem.eql(u8, a_leaf, ".") or std.mem.eql(u8, a_leaf, "..")) return false;
    if (std.mem.eql(u8, b_leaf, ".") or std.mem.eql(u8, b_leaf, "..")) return false;
    return !std.mem.eql(u8, a_leaf, b_leaf);
}

pub fn normalizePath(buffer: []u8, path: []const u8) ![]const u8 {
    var segments: [128][]const u8 = undefined;
    var segment_count: usize = 0;

    var rest = path;
    while (rest.len > 0) {
        const slash_index = std.mem.indexOfScalar(u8, rest, '/') orelse rest.len;
        const segment = rest[0..slash_index];
        if (segment.len != 0 and !std.mem.eql(u8, segment, ".")) {
            if (std.mem.eql(u8, segment, "..") and segment_count > 0) {
                segment_count -= 1;
            } else {
                if (segment_count >= segments.len) return error.PathTooManySegments;
                segments[segment_count] = segment;
                segment_count += 1;
            }
        }
        if (slash_index == rest.len) break;
        rest = rest[slash_index + 1 ..];
    }

    var len: usize = 0;
    for (segments[0..segment_count]) |segment| {
        if (len != 0) {
            if (len >= buffer.len) return error.PathTooLong;
            buffer[len] = '/';
            len += 1;
        }
        if (len + segment.len > buffer.len) return error.PathTooLong;
        @memcpy(buffer[len..][0..segment.len], segment);
        len += segment.len;
    }

    return buffer[0..len];
}

pub fn normalizeIdentifier(ident: []const u8) []const u8 {
    if (ident.len >= 3 and std.mem.startsWith(u8, ident, "@\"") and ident[ident.len - 1] == '"') {
        return ident[2 .. ident.len - 1];
    }
    return ident;
}

pub fn isVarDeclTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .simple_var_decl,
        .aligned_var_decl,
        .global_var_decl,
        .local_var_decl,
        => true,
        else => false,
    };
}

pub fn isBuiltinCallTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => true,
        else => false,
    };
}

pub fn nextNonCommentToken(token_tags: []const std.zig.Token.Tag, start: usize) ?usize {
    var index = start;
    while (index < token_tags.len) : (index += 1) {
        switch (token_tags[index]) {
            .container_doc_comment, .doc_comment => continue,
            else => return index,
        }
    }
    return null;
}

pub fn prevNonCommentToken(token_tags: []const std.zig.Token.Tag, start: usize) ?usize {
    if (start == 0) return null;
    var index = start - 1;
    while (true) {
        switch (token_tags[index]) {
            .container_doc_comment, .doc_comment => {},
            else => return index,
        }
        if (index == 0) return null;
        index -= 1;
    }
}

pub fn paramNameTokenBeforeType(tree: *const std.zig.Ast, type_node: usize) ?usize {
    if (type_node >= tree.nodes.len) return null;
    const token_tags = tree.tokens.items(.tag);
    const type_token = tree.firstToken(@enumFromInt(type_node));
    const colon_token = prevNonCommentToken(token_tags, type_token) orelse return null;
    if (token_tags[colon_token] != .colon) return null;
    const name_token = prevNonCommentToken(token_tags, colon_token) orelse return null;
    if (token_tags[name_token] != .identifier) return null;
    return name_token;
}

pub fn identifierName(tree: *const std.zig.Ast, node: usize) ?[]const u8 {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .identifier) return null;
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= main_tokens.len) return null;
    return normalizeIdentifier(tree.tokenSlice(main_tokens[node]));
}

pub fn fieldAccessName(tree: *const std.zig.Ast, node: usize) ?[]const u8 {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .field_access) return null;
    const datas = tree.nodes.items(.data);
    return normalizeIdentifier(tree.tokenSlice(datas[node].node_and_token[1]));
}

fn publicVarDeclImportsPath(
    file: File,
    node_idx: u32,
    target_path: []const u8,
) bool {
    const tree = file.tree;
    const full = tree.fullVarDecl(@enumFromInt(node_idx)) orelse return false;
    if (!isPubToken(tree, full.visib_token)) return false;

    const init_node = full.ast.init_node.unwrap() orelse return false;
    const init_idx = @intFromEnum(init_node);
    const tags = tree.nodes.items(.tag);
    if (init_idx >= tags.len) return false;

    return initNodeImportsFile(file, init_idx, target_path);
}

fn filePublicMemberImportsPath(files: []const File, file_index: usize, member_name: []const u8, target_path: []const u8) bool {
    if (file_index >= files.len) return false;
    const file = files[file_index];
    if (file.tree.errors.len != 0) return false;
    const tags = file.tree.nodes.items(.tag);

    for (file.tree.rootDecls()) |decl_idx| {
        const idx = @intFromEnum(decl_idx);
        if (idx >= tags.len) continue;
        if (!isVarDeclTag(tags[idx])) continue;
        if (publicVarDeclNamedImportsPath(file, @intCast(idx), member_name, target_path)) return true;
    }
    return false;
}

fn publicVarDeclNamedImportsPath(
    file: File,
    node_idx: u32,
    expected_name: []const u8,
    target_path: []const u8,
) bool {
    const tree = file.tree;
    const full = tree.fullVarDecl(@enumFromInt(node_idx)) orelse return false;
    if (!isPubToken(tree, full.visib_token)) return false;
    const name_token = full.ast.mut_token + 1;
    if (name_token >= tree.tokens.len) return false;
    if (tree.tokenTag(name_token) != .identifier) return false;
    const name = normalizeIdentifier(tree.tokenSlice(name_token));
    if (!std.mem.eql(u8, name, expected_name)) return false;

    const init_node = full.ast.init_node.unwrap() orelse return false;
    return initNodeImportsFile(file, @intFromEnum(init_node), target_path);
}

fn isPubToken(tree: *const std.zig.Ast, token: ?std.zig.Ast.TokenIndex) bool {
    const tok = token orelse return false;
    return tree.tokenTag(tok) == .keyword_pub;
}

const InitPathScanner = struct {
    file: File,
    target_path: []const u8,
    visited: *[64]u32,
    depth: usize,
    found: bool = false,
    stop: bool = false,

    pub fn visit(_: *const std.zig.Ast, node: u32, self: *InitPathScanner) anyerror!void {
        if (self.stop) return;
        self.found = initNodeImportsPathVisited(
            self.file,
            node,
            self.target_path,
            self.visited,
            self.depth,
        );
        self.stop = self.found;
    }
};

test "skript residual: public conditional imports expose both branches" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const dynlib_impl = @import("dynlib.zig");
        \\const no_dynlib_impl = @import("no_dynlib.zig");
        \\pub const dynlib = if (true) dynlib_impl else no_dynlib_impl;
        \\const ffi_impl = @import("ffi.zig");
        \\const no_ffi_impl = @import("no_ffi.zig");
        \\pub const ffi = if (true) ffi_impl else no_ffi_impl;
    ;
    var tree = try std.zig.Ast.parse(allocator, code, .zig);
    defer tree.deinit(allocator);

    const files = [_]File{
        .{ .path = "src/intrinsics/root.zig", .tree = &tree },
    };
    try std.testing.expect(filePubliclyImportsPath(&files, 0, "src/intrinsics/dynlib.zig"));
    try std.testing.expect(filePubliclyImportsPath(&files, 0, "src/intrinsics/no_dynlib.zig"));
    try std.testing.expect(filePubliclyImportsPath(&files, 0, "src/intrinsics/ffi.zig"));
    try std.testing.expect(filePubliclyImportsPath(&files, 0, "src/intrinsics/no_ffi.zig"));
}

test "import resolution rejects malformed exports and preserves valid aliases" {
    const allocator = std.testing.allocator;
    var source = try std.zig.Ast.parse(allocator,
        \\const malformed = @import("malformed.zig");
        \\const valid = @import("valid.zig");
        \\pub const hidden = malformed.leaf;
        \\pub const visible = valid.leaf;
    , .zig);
    defer source.deinit(allocator);
    var malformed = try std.zig.Ast.parse(allocator,
        \\pub const leaf = @import("hidden.zig");
        \\pub const cycle = alias;
        \\const alias = cycle;
        \\const broken = ;
    , .zig);
    defer malformed.deinit(allocator);
    var valid = try std.zig.Ast.parse(allocator,
        \\pub const leaf = selected;
        \\const selected = @import("visible.zig");
        \\pub const cycle = alias;
        \\const alias = cycle;
    , .zig);
    defer valid.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 0), source.errors.len);
    try std.testing.expectEqual(@as(usize, 0), valid.errors.len);
    try std.testing.expect(malformed.errors.len != 0);
    var source_index = try LexicalIndex.init(allocator, &source);
    defer source_index.deinit(allocator);
    var malformed_index = try LexicalIndex.init(allocator, &malformed);
    defer malformed_index.deinit(allocator);
    var valid_index = try LexicalIndex.init(allocator, &valid);
    defer valid_index.deinit(allocator);
    var files = [_]File{
        .{ .path = "source.zig", .tree = &source },
        .{ .path = "malformed.zig", .tree = &malformed },
        .{ .path = "valid.zig", .tree = &valid },
    };
    var paths = try PathIndex.init(allocator, &files);
    defer paths.deinit(allocator);
    for ([_]bool{ false, true }) |indexed| {
        files[0].lexical_index = if (indexed) &source_index else null;
        files[1].lexical_index = if (indexed) &malformed_index else null;
        files[2].lexical_index = if (indexed) &valid_index else null;
        for (&files) |*file| file.path_index = if (indexed) &paths else null;
        try std.testing.expect(!filePubliclyImportsPath(&files, 1, "hidden.zig"));
        try std.testing.expect(filePubliclyImportsPath(&files, 2, "visible.zig"));
        try std.testing.expect(!filePubliclyImportsPath(&files, 2, "missing.zig"));

        const hidden_decl = source.fullVarDecl(source.rootDecls()[2]) orelse return error.TestUnexpectedResult;
        const hidden = hidden_decl.ast.init_node.unwrap() orelse return error.TestUnexpectedResult;
        const visible_decl = source.fullVarDecl(source.rootDecls()[3]) orelse return error.TestUnexpectedResult;
        const visible = visible_decl.ast.init_node.unwrap() orelse return error.TestUnexpectedResult;
        try std.testing.expect(!nodeImportsPath(&files, &source, @intFromEnum(hidden), "source.zig", "hidden.zig"));
        try std.testing.expect(nodeImportsPath(&files, &source, @intFromEnum(visible), "source.zig", "visible.zig"));
        const imported_decl = source.fullVarDecl(source.rootDecls()[0]) orelse return error.TestUnexpectedResult;
        const imported = imported_decl.ast.init_node.unwrap() orelse return error.TestUnexpectedResult;
        try std.testing.expect(nodeImportsPath(&files, &source, @intFromEnum(imported), "source.zig", "malformed.zig"));
        for (0..malformed.nodes.len) |node| {
            try std.testing.expect(!nodeImportsPath(&files, &malformed, node, "malformed.zig", "hidden.zig"));
            try std.testing.expect(!initNodeImportsPath(&malformed, node, "malformed.zig", "hidden.zig"));
        }
    }
}

test "indexed imports preserve forward aliases and local shadowing" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\pub const exposed = @"selected module";
        \\const @"selected module" = @import("selected.zig");
        \\const hidden = @import("hidden.zig");
        \\pub const value = blk: { const hidden = 1; break :blk hidden; };
        \\pub const cycle = alias;
        \\const alias = cycle;
    ;
    var tree = try std.zig.Ast.parse(allocator, code, .zig);
    defer tree.deinit(allocator);
    var index = try LexicalIndex.init(allocator, &tree);
    defer index.deinit(allocator);
    for ([_]?*const LexicalIndex{ null, &index }) |metadata| {
        const files = [_]File{.{ .path = "src/root.zig", .tree = &tree, .lexical_index = metadata }};
        try std.testing.expect(filePubliclyImportsPath(&files, 0, "src/selected.zig"));
        try std.testing.expect(!filePubliclyImportsPath(&files, 0, "src/hidden.zig"));
        const declaration = tree.fullVarDecl(tree.rootDecls()[0]) orelse return error.TestUnexpectedResult;
        const initializer = declaration.ast.init_node.unwrap() orelse return error.TestUnexpectedResult;
        try std.testing.expect(nodeImportsPath(&files, &tree, @intFromEnum(initializer), files[0].path, "src/selected.zig"));
        try std.testing.expect(!nodeImportsPath(&files, &tree, @intFromEnum(initializer), files[0].path, "src/hidden.zig"));
    }
}

test "public import aliases ignore unrelated local bindings" {
    const code: [:0]const u8 =
        \\const selected = @import("selected.zig");
        \\pub const exposed = selected;
        \\fn unrelated() void {
        \\    const selected = @import("hidden.zig");
        \\    _ = selected;
        \\}
    ;
    var tree = try std.zig.Ast.parse(std.testing.allocator, code, .zig);
    defer tree.deinit(std.testing.allocator);
    const files = [_]File{.{ .path = "src/root.zig", .tree = &tree }};
    try std.testing.expect(filePubliclyImportsPath(&files, 0, "src/selected.zig"));
    try std.testing.expect(!filePubliclyImportsPath(&files, 0, "src/hidden.zig"));
    const declaration = tree.fullVarDecl(tree.rootDecls()[1]) orelse return error.MissingDeclaration;
    const initializer = declaration.ast.init_node.unwrap() orelse return error.MissingInitializer;
    try std.testing.expect(nodeImportsPath(&files, &tree, @intFromEnum(initializer), files[0].path, "src/selected.zig"));
    try std.testing.expect(!nodeImportsPath(&files, &tree, @intFromEnum(initializer), files[0].path, "src/hidden.zig"));
}

test "public initializer locals shadow root import aliases" {
    const code: [:0]const u8 =
        \\const selected = @import("selected.zig");
        \\pub const exposed = blk: {
        \\    const selected = 1;
        \\    break :blk selected;
        \\};
    ;
    var tree = try std.zig.Ast.parse(std.testing.allocator, code, .zig);
    defer tree.deinit(std.testing.allocator);
    const files = [_]File{.{ .path = "src/root.zig", .tree = &tree }};
    try std.testing.expect(!filePubliclyImportsPath(&files, 0, "src/selected.zig"));
}

test "public values do not reexport namespaces passed to constructors" {
    const code: [:0]const u8 =
        \\const hidden = @import("hidden.zig");
        \\const Box = struct { count: usize };
        \\fn count(_: type) usize { return 1; }
        \\pub const value = count(hidden);
        \\pub const instance = Box{ .count = count(hidden) };
        \\pub const conditional = if (true) Box{ .count = count(hidden) } else count(hidden);
    ;
    var tree = try std.zig.Ast.parse(std.testing.allocator, code, .zig);
    defer tree.deinit(std.testing.allocator);
    const files = [_]File{.{ .path = "src/root.zig", .tree = &tree }};
    try std.testing.expect(!filePubliclyImportsPath(&files, 0, "src/hidden.zig"));
}

test "conditional namespace aliases do not reexport their condition" {
    const code: [:0]const u8 =
        \\pub const selected = if (@import("condition.zig").enabled)
        \\    @import("native.zig")
        \\else
        \\    @import("fallback.zig");
    ;
    var tree = try std.zig.Ast.parse(std.testing.allocator, code, .zig);
    defer tree.deinit(std.testing.allocator);
    const files = [_]File{.{ .path = "src/root.zig", .tree = &tree }};
    try std.testing.expect(filePubliclyImportsPath(&files, 0, "src/native.zig"));
    try std.testing.expect(filePubliclyImportsPath(&files, 0, "src/fallback.zig"));
    try std.testing.expect(!filePubliclyImportsPath(&files, 0, "src/condition.zig"));
}

test "unsupported usingnamespace syntax does not expose imports" {
    const allocator = std.testing.allocator;
    var first = try std.zig.Ast.parse(allocator, "pub usingnamespace @import(\"b.zig\");", .zig);
    defer first.deinit(allocator);
    var second = try std.zig.Ast.parse(allocator,
        \\pub usingnamespace @import("a.zig");
        \\pub usingnamespace @import("malformed.zig");
        \\pub usingnamespace @import("c.zig");
    , .zig);
    defer second.deinit(allocator);
    var malformed = try std.zig.Ast.parse(allocator,
        \\pub usingnamespace @import("hidden.zig");
        \\const broken = ;
    , .zig);
    defer malformed.deinit(allocator);
    try std.testing.expect(malformed.errors.len != 0);
    const files = [_]File{
        .{ .path = "a.zig", .tree = &first },
        .{ .path = "b.zig", .tree = &second },
        .{ .path = "malformed.zig", .tree = &malformed },
    };
    try std.testing.expect(!filePubliclyImportsPath(&files, 0, "missing.zig"));
    try std.testing.expect(!filePubliclyImportsPath(&files, 0, "hidden.zig"));
    try std.testing.expect(!fileUsingnamespaceImportsPath(&files, &first, "a.zig", "missing.zig"));
    try std.testing.expect(!fileUsingnamespaceImportsPath(&files, &first, "a.zig", "hidden.zig"));
    try std.testing.expect(!fileUsingnamespaceImportsPath(&files, &malformed, "malformed.zig", "hidden.zig"));
    try std.testing.expect(first.errors.len != 0);
    try std.testing.expect(second.errors.len != 0);
    try std.testing.expect(!filePubliclyImportsPath(&files, 0, "b.zig"));
    try std.testing.expect(!filePubliclyImportsPath(&files, 0, "c.zig"));
    try std.testing.expect(!filePubliclyImportsPath(&files, 1, "a.zig"));
    try std.testing.expect(!filePubliclyImportsPath(&files, 1, "malformed.zig"));
    try std.testing.expect(!filePubliclyImportsPath(&files, 1, "c.zig"));
    try std.testing.expect(!fileUsingnamespaceImportsPath(&files, &first, "a.zig", "b.zig"));
    try std.testing.expect(!fileUsingnamespaceImportsPath(&files, &first, "a.zig", "c.zig"));
    try std.testing.expect(!fileUsingnamespaceImportsPath(&files, &second, "b.zig", "a.zig"));
    try std.testing.expect(!fileUsingnamespaceImportsPath(&files, &second, "b.zig", "c.zig"));
}

test "path index preserves POSIX equivalence and first matching file" {
    const allocator = std.testing.allocator;
    var tree = try std.zig.Ast.parse(allocator, "", .zig);
    defer tree.deinit(allocator);
    var files = [_]File{
        .{ .path = "./src/value.zig", .tree = &tree },
        .{ .path = "src/value.zig", .tree = &tree },
        .{ .path = "other/value.zig", .tree = &tree },
        .{ .path = "C:value.zig", .tree = &tree },
        .{ .path = "src/back\\slash.zig", .tree = &tree },
    };
    const plain = files;
    var index = try PathIndex.init(allocator, &files);
    defer index.deinit(allocator);
    for (&files) |*file| file.path_index = &index;
    const paths = [_][]const u8{
        "src/value.zig",          "/src//value.zig",     "src/value.zig/.",
        "src/value.zig/child/..", "src/value.zig/",      "other/value.zig",
        "./C:value.zig",          "src/back\\slash.zig", "src/missing.zig",
    };
    for (paths) |path| {
        try std.testing.expectEqual(findFileIndexByPath(&plain, path), findFileIndexByPath(&files, path));
    }
    try std.testing.expectEqual(@as(?usize, 0), findFileIndexByPath(&files, "src/value.zig"));
    try std.testing.expectEqual(@as(?usize, 0), findFileIndexByPath(files[2..3], "other/value.zig"));
    try std.testing.expectEqual(@as(?usize, null), findFileIndexByPath(files[2..3], "src/value.zig"));
}

test "path index releases duplicate and partial normalized keys" {
    const allocator = std.testing.allocator;
    var tree = try std.zig.Ast.parse(allocator, "", .zig);
    defer tree.deinit(allocator);
    const files = [_]File{
        .{ .path = "src/value.zig", .tree = &tree },
        .{ .path = "./src/value.zig", .tree = &tree },
        .{ .path = "src/other.zig", .tree = &tree },
    };
    const Harness = struct {
        fn run(failing_allocator: std.mem.Allocator, source_files: []const File) !void {
            var index = try PathIndex.init(failing_allocator, source_files);
            defer index.deinit(failing_allocator);
            try std.testing.expectEqual(@as(?usize, 0), index.find("./src/value.zig"));
            try std.testing.expectEqual(@as(?usize, 2), index.find("src/other.zig/child/.."));
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Harness.run, .{@as([]const File, &files)});
}

test "import path comparisons preserve normalization and package precedence" {
    try std.testing.expect(importResolvesToPath("src/main.zig", "../lib/value.zig", "lib/value.zig"));
    try std.testing.expect(!importResolvesToPath("src/main.zig", "../lib/value.zig", "lib/other.zig"));
    try std.testing.expect(importResolvesToPath("src/main.zig", "value.zig/.", "src/value.zig"));
    try std.testing.expect(importResolvesToPath("src/main.zig", "value.zig/child/..", "src/value.zig"));
    try std.testing.expect(pathsEquivalent("/src//value.zig", "src/value.zig"));
    try std.testing.expect(pathsEquivalent("src/value.zig", "src/value.zig/"));
    try std.testing.expect(pathsEquivalent("C:value.zig", "./C:value.zig"));
    try std.testing.expect(!pathsEquivalent("src/value.zig", "other/value.zig"));
    try std.testing.expect(importMayResolveToPath("src/main.zig", "module", "lib/module.zig"));
}
