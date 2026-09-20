const std = @import("std");
const compat = @import("compat.zig");
const ast_walk = @import("ast_walk.zig");
const call_resolver = @import("analysis/call_resolver.zig");
const Diagnostic = @import("diagnostic.zig").Diagnostic;
const import_resolver = @import("analysis/import_resolver.zig");
const ProjectSources = @import("project_sources.zig").ProjectSources;
const ProjectReferenceIndex = @import("analysis/project_reference_index.zig").ProjectReferenceIndex;
const Source = @import("source.zig").Source;
const suppression = @import("suppression.zig");

const rule_id = "unused-decl";
const fieldAccessName = import_resolver.fieldAccessName;
const identifierName = import_resolver.identifierName;
const importPathFromBuiltinCall = import_resolver.importPathFromBuiltinCall;
const isVarDeclTag = import_resolver.isVarDeclTag;
const normalizeIdentifier = import_resolver.normalizeIdentifier;

const DeclKind = enum {
    function,
    type_decl,
    constant,
    variable,
    declaration,

    fn description(self: DeclKind) []const u8 {
        return switch (self) {
            .function => "Function",
            .type_decl => "Type",
            .constant => "Constant",
            .variable => "Variable",
            .declaration => "Declaration",
        };
    }
};

const FileInfo = struct {
    path: []const u8,
    tree: *const std.zig.Ast,
    suppressions: suppression.SuppressionMap,

    fn deinit(self: *FileInfo) void {
        self.suppressions.deinit();
    }
};

const DeclInfo = struct {
    file_index: usize,
    node_index: u32,
    name: []const u8,
    normalized_name: []const u8,
    byte_offset: usize,
    kind: DeclKind,

    fn deinit(self: *DeclInfo, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
        allocator.free(self.normalized_name);
    }
};

const BuildReceiver = struct {
    name: []const u8,
    declaration_node: u32,
};

const ProjectContext = struct {
    allocator: std.mem.Allocator,
    files: []const import_resolver.File,
    build_file_indices: []const usize,
    api_roots: std.ArrayList(usize) = .empty,
    public_api_files: std.ArrayList(usize) = .empty,
    api_root_membership: std.AutoHashMapUnmanaged(usize, void) = .empty,
    public_api_membership: std.AutoHashMapUnmanaged(usize, void) = .empty,
    references: ProjectReferenceIndex,

    fn init(
        allocator: std.mem.Allocator,
        files: []const import_resolver.File,
        build_file_indices: []const usize,
    ) !ProjectContext {
        return .{
            .allocator = allocator,
            .files = files,
            .build_file_indices = build_file_indices,
            .references = try ProjectReferenceIndex.init(allocator, files),
        };
    }

    fn deinit(self: *ProjectContext) void {
        self.references.deinit();
        self.public_api_membership.deinit(self.allocator);
        self.api_root_membership.deinit(self.allocator);
        self.public_api_files.deinit(self.allocator);
        self.api_roots.deinit(self.allocator);
    }

    fn collectApiRoots(self: *ProjectContext) !void {
        for (self.build_file_indices) |file_index| {
            if (file_index >= self.files.len) continue;
            try self.collectBuildRootSourceFiles(file_index);
        }
    }

    fn collectPublicApiFiles(self: *ProjectContext) !void {
        for (self.api_roots.items) |root_index| {
            try self.appendPublicApiFile(root_index);
        }

        var cursor: usize = 0;
        while (cursor < self.public_api_files.items.len) : (cursor += 1) {
            const importer_index = self.public_api_files.items[cursor];
            for (try self.references.publicTargets(importer_index)) |file_index| {
                try self.appendPublicApiFile(file_index);
            }
        }
    }

    fn isPublicApiFile(self: *const ProjectContext, file_index: usize) bool {
        return self.public_api_membership.contains(file_index);
    }

    fn appendApiRoot(self: *ProjectContext, file_index: usize) !void {
        const result = try self.api_root_membership.getOrPut(self.allocator, file_index);
        if (result.found_existing) return;
        try self.api_roots.append(self.allocator, file_index);
    }

    fn appendPublicApiFile(self: *ProjectContext, file_index: usize) !void {
        const result = try self.public_api_membership.getOrPut(self.allocator, file_index);
        if (result.found_existing) return;
        try self.public_api_files.append(self.allocator, file_index);
    }
    fn collectBuildRootSourceFiles(self: *ProjectContext, build_file_index: usize) !void {
        const build_file = self.files[build_file_index];
        const resolver = call_resolver.ProjectTypeResolver{
            .files = self.files,
            .file_index = build_file_index,
        };
        try self.collectBuildRootSourceFilesFromTree(
            build_file.tree,
            build_file.path,
            resolver,
        );
    }

    fn collectBuildRootSourceFilesFromTree(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
    ) !void {
        if (tree.errors.len != 0) return;
        const build_receiver = buildFunctionReceiver(tree, resolver) orelse return;
        const tags = tree.nodes.items(.tag);
        for (tags, 0..) |tag, node_index| {
            if (!call_resolver.isCallNode(tag)) continue;
            if (!isBuildMethodCall(tree, resolver, @intCast(node_index), build_receiver)) continue;

            var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, @enumFromInt(node_index)) orelse continue;
            const callee = @intFromEnum(call.ast.fn_expr);
            const method = tree.tokenSlice(tree.nodes.items(.data)[callee].node_and_token[1]);
            if (!std.mem.eql(u8, method, "addModule") and !std.mem.eql(u8, method, "createModule")) continue;
            for (call.ast.params) |param_node| {
                const parameter = @intFromEnum(param_node);
                if (parameter >= tags.len) continue;

                var struct_buffer: [2]std.zig.Ast.Node.Index = undefined;
                const struct_init = tree.fullStructInit(
                    &struct_buffer,
                    @enumFromInt(parameter),
                ) orelse continue;
                for (struct_init.ast.fields) |field_node| {
                    const field_name = structInitFieldName(tree, field_node) orelse continue;
                    if (!std.mem.eql(u8, field_name, "root_source_file")) continue;
                    const root_path = buildPathLiteral(tree, resolver, @intFromEnum(field_node), build_receiver) orelse continue;
                    if (import_resolver.resolveImportToFileIndex(self.files, build_path, root_path)) |root_index| {
                        try self.appendApiRoot(root_index);
                    }
                }
            }
        }
    }
};

fn buildFunctionReceiver(
    tree: *const std.zig.Ast,
    resolver: call_resolver.ProjectTypeResolver,
) ?BuildReceiver {
    const tags = tree.nodes.items(.tag);
    var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;

    for (tree.rootDecls()) |decl_idx| {
        const node = @intFromEnum(decl_idx);
        if (node >= tags.len or tags[node] != .fn_decl) continue;

        const proto = tree.fullFnProto(&proto_buffer, decl_idx) orelse continue;
        if (!isPubToken(tree, proto.visib_token)) continue;

        const name_token = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), "build")) continue;
        var params = proto.iterate(tree);
        const parameter = params.next() orelse return null;
        const type_node = parameter.type_expr orelse return null;
        if (!parameterIsStdBuild(tree, @intFromEnum(type_node), resolver)) return null;
        const parameter_token = parameter.name_token orelse return null;
        if (parameter_token >= tree.tokens.len or tree.tokenTag(parameter_token) != .identifier) return null;
        return .{
            .name = import_resolver.normalizeIdentifier(tree.tokenSlice(parameter_token)),
            .declaration_node = @intFromEnum(type_node),
        };
    }
    return null;
}

fn parameterIsStdBuild(
    tree: *const std.zig.Ast,
    type_node: u32,
    resolver: call_resolver.ProjectTypeResolver,
) bool {
    const tags = tree.nodes.items(.tag);
    var node = type_node;
    if (node >= tags.len) return false;

    switch (tags[node]) {
        .ptr_type,
        .ptr_type_aligned,
        .ptr_type_sentinel,
        .ptr_type_bit_range,
        => {
            const pointer = tree.fullPtrType(@enumFromInt(node)) orelse return false;
            node = @intFromEnum(pointer.ast.child_type);
            if (node >= tags.len) return false;
        },
        else => return false,
    }

    if (tags[node] != .field_access) return false;
    const access = tree.nodes.items(.data)[node].node_and_token;
    const namespace = @intFromEnum(access[0]);
    if (namespace >= tags.len or tags[namespace] != .identifier) return false;
    const namespace_token = tree.nodes.items(.main_token)[namespace];
    if (namespace_token >= tree.tokens.len or tree.tokenTag(namespace_token) != .identifier) return false;
    if (!resolver.isVerifiedImportBinding(namespace, "std")) return false;
    if (access[1] >= tree.tokens.len or tree.tokenTag(access[1]) != .identifier) return false;
    return std.mem.eql(u8, tree.tokenSlice(access[1]), "Build");
}

fn isBuildMethodCall(
    tree: *const std.zig.Ast,
    resolver: call_resolver.ProjectTypeResolver,
    node: u32,
    expected_receiver: BuildReceiver,
) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;

    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return false;
    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return false;

    const access = tree.nodes.items(.data)[callee].node_and_token;
    const receiver = @intFromEnum(access[0]);
    if (receiver >= tags.len or tags[receiver] != .identifier) return false;
    const main_token = tree.nodes.items(.main_token)[receiver];
    if (main_token >= tree.tokens.len or tree.tokenTag(main_token) != .identifier) return false;
    if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(main_token)), expected_receiver.name)) return false;
    const declaration_node = resolver.resolveDeclarationNode(receiver) orelse return false;
    return declaration_node == expected_receiver.declaration_node;
}

fn structInitFieldName(tree: *const std.zig.Ast, value: std.zig.Ast.Node.Index) ?[]const u8 {
    const first = tree.firstToken(value);
    if (first < 3) return null;
    if (tree.tokenTag(first - 1) != .equal or tree.tokenTag(first - 2) != .identifier or tree.tokenTag(first - 3) != .period) return null;
    return import_resolver.normalizeIdentifier(tree.tokenSlice(first - 2));
}

fn buildPathLiteral(
    tree: *const std.zig.Ast,
    resolver: call_resolver.ProjectTypeResolver,
    node: u32,
    receiver: BuildReceiver,
) ?[]const u8 {
    if (!isBuildMethodCall(tree, resolver, node, receiver)) return null;
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return null;

    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return null;
    if (call.ast.params.len != 1) return null;

    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return null;
    const access = tree.nodes.items(.data)[callee].node_and_token;
    const field_name = tree.tokenSlice(access[1]);
    if (!std.mem.eql(u8, field_name, "path")) return null;

    const argument = @intFromEnum(call.ast.params[0]);
    if (argument >= tags.len or tags[argument] != .string_literal) return null;
    const main_token = tree.nodes.items(.main_token)[argument];
    const token_tags = tree.tokens.items(.tag);
    if (main_token >= token_tags.len or token_tags[main_token] != .string_literal) return null;
    const literal = tree.tokenSlice(main_token);
    if (literal.len < 2) return null;
    return literal[1 .. literal.len - 1];
}

pub fn analyze(
    project_sources: *const ProjectSources,
    allocator: std.mem.Allocator,
    diagnostics: *std.ArrayList(Diagnostic),
) !void {
    const resolver_files = project_sources.files();
    const diagnostic_indices = project_sources.diagnosticFileIndices();
    if (diagnostic_indices.len < 2) return;
    // Incomplete syntax cannot prove the absence of cross-file references.
    for (resolver_files) |file| {
        if (file.tree.errors.len != 0) return;
    }

    const files = try allocator.alloc(FileInfo, resolver_files.len);
    var file_count: usize = 0;
    defer {
        for (files[0..file_count]) |*file| file.deinit();
        allocator.free(files);
    }

    for (resolver_files) |file| {
        const suppressions = try suppression.parseSuppressions(allocator, file.tree.source);
        files[file_count] = .{
            .path = file.path,
            .tree = file.tree,
            .suppressions = suppressions,
        };
        file_count += 1;
    }

    var project = try ProjectContext.init(
        allocator,
        resolver_files,
        project_sources.buildFileIndices(),
    );
    defer project.deinit();
    try project.collectApiRoots();
    try project.collectPublicApiFiles();

    var decls: std.ArrayList(DeclInfo) = .empty;
    defer {
        for (decls.items) |*decl| decl.deinit(allocator);
        decls.deinit(allocator);
    }

    for (diagnostic_indices) |file_index| {
        if (file_index >= files.len) continue;
        const file = files[file_index];
        if (project.isPublicApiFile(file_index)) continue;
        try collectPublicRootDecls(allocator, file.tree, file.path, file_index, &decls);
    }

    const used = try collectProjectUsedDecls(
        allocator,
        files,
        resolver_files,
        decls.items,
        &project.references,
    );
    defer allocator.free(used);

    for (decls.items, 0..) |decl, decl_index| {
        if (used[decl_index]) continue;
        const file = files[decl.file_index];
        var source = Source.initParsed(allocator, file.path, file.tree);
        defer source.deinit();
        const range = try source.byteRangeToSourceRange(
            decl.byte_offset,
            decl.byte_offset + decl.name.len,
        );

        if (file.suppressions.isSuppressed(range.start.line, rule_id)) continue;

        const message = try std.fmt.allocPrint(
            allocator,
            "{s} '{s}' is never used by another analyzed file",
            .{ decl.kind.description(), decl.name },
        );
        defer allocator.free(message);

        var diag = try Diagnostic.init(
            allocator,
            file.path,
            rule_id,
            .warning,
            message,
            range,
        );
        errdefer diag.deinit(allocator);
        try diagnostics.append(allocator, diag);
    }
}

fn collectPublicRootDecls(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    path: []const u8,
    file_index: usize,
    decls: *std.ArrayList(DeclInfo),
) !void {
    if (tree.errors.len != 0) return;
    const tags = tree.nodes.items(.tag);
    const token_starts = tree.tokens.items(.start);

    for (tree.rootDecls()) |decl_idx| {
        const idx = @intFromEnum(decl_idx);
        const info = switch (tags[idx]) {
            .simple_var_decl,
            .aligned_var_decl,
            .global_var_decl,
            => try extractPublicVarDecl(allocator, tree, @intCast(idx), token_starts, file_index),
            .fn_decl,
            .fn_proto,
            .fn_proto_simple,
            .fn_proto_one,
            .fn_proto_multi,
            => try extractPublicFnDecl(allocator, tree, @intCast(idx), token_starts, file_index),
            else => null,
        };

        if (info) |decl| {
            if (isIgnoredPublicDecl(path, decl.name)) {
                var mutable_decl = decl;
                mutable_decl.deinit(allocator);
                continue;
            }
            var mutable_decl = decl;
            errdefer mutable_decl.deinit(allocator);
            try decls.append(allocator, mutable_decl);
        }
    }
}

fn extractPublicVarDecl(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    node_idx: u32,
    token_starts: []const u32,
    file_index: usize,
) !?DeclInfo {
    const full = tree.fullVarDecl(@enumFromInt(node_idx)) orelse return null;
    if (!isPubToken(tree, full.visib_token)) return null;
    if (full.extern_export_token != null) return null;
    if (isPublicAliasDecl(tree, full)) return null;

    const token_tags = tree.tokens.items(.tag);
    const name_token = full.ast.mut_token + 1;
    if (name_token >= token_tags.len) return null;
    if (token_tags[name_token] != .identifier) return null;

    const name = tree.tokenSlice(name_token);
    return try makeDeclInfo(
        allocator,
        file_index,
        node_idx,
        name,
        token_starts[name_token],
        classifyVarDecl(tree, full),
    );
}

fn extractPublicFnDecl(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    node_idx: u32,
    token_starts: []const u32,
    file_index: usize,
) !?DeclInfo {
    const tags = tree.nodes.items(.tag);
    const tag = tags[node_idx];
    var buffer: [1]std.zig.Ast.Node.Index = undefined;

    return switch (tag) {
        .fn_decl => blk: {
            const data = tree.nodes.items(.data)[node_idx];
            const proto_node = @intFromEnum(data.node_and_node[0]);
            break :blk extractPublicFnDecl(allocator, tree, proto_node, token_starts, file_index);
        },
        .fn_proto => extractPublicFnProto(
            allocator,
            tree,
            node_idx,
            tree.fnProto(@enumFromInt(node_idx)),
            token_starts,
            file_index,
        ),
        .fn_proto_simple => extractPublicFnProto(
            allocator,
            tree,
            node_idx,
            tree.fnProtoSimple(&buffer, @enumFromInt(node_idx)),
            token_starts,
            file_index,
        ),
        .fn_proto_one => extractPublicFnProto(
            allocator,
            tree,
            node_idx,
            tree.fnProtoOne(&buffer, @enumFromInt(node_idx)),
            token_starts,
            file_index,
        ),
        .fn_proto_multi => extractPublicFnProto(
            allocator,
            tree,
            node_idx,
            tree.fnProtoMulti(@enumFromInt(node_idx)),
            token_starts,
            file_index,
        ),
        else => null,
    };
}

fn extractPublicFnProto(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    node_idx: u32,
    proto: std.zig.Ast.full.FnProto,
    token_starts: []const u32,
    file_index: usize,
) !?DeclInfo {
    if (!isPubToken(tree, proto.visib_token)) return null;
    if (proto.extern_export_inline_token) |tok| {
        const tag = tree.tokenTag(tok);
        if (tag == .keyword_extern or tag == .keyword_export) return null;
    }

    const name_token = proto.name_token orelse return null;
    if (tree.tokenTag(name_token) != .identifier) return null;

    return try makeDeclInfo(
        allocator,
        file_index,
        node_idx,
        tree.tokenSlice(name_token),
        token_starts[name_token],
        .function,
    );
}

fn makeDeclInfo(
    allocator: std.mem.Allocator,
    file_index: usize,
    node_index: u32,
    name: []const u8,
    byte_offset: usize,
    kind: DeclKind,
) !DeclInfo {
    const name_copy = try allocator.dupe(u8, name);
    errdefer allocator.free(name_copy);
    const normalized_copy = try allocator.dupe(u8, normalizeIdentifier(name));
    return .{
        .file_index = file_index,
        .node_index = node_index,
        .name = name_copy,
        .normalized_name = normalized_copy,
        .byte_offset = byte_offset,
        .kind = kind,
    };
}

fn isPubToken(tree: *const std.zig.Ast, token: ?std.zig.Ast.TokenIndex) bool {
    const tok = token orelse return false;
    return tree.tokenTag(tok) == .keyword_pub;
}

fn isPublicAliasDecl(tree: *const std.zig.Ast, full: std.zig.Ast.full.VarDecl) bool {
    if (tree.tokenTag(full.ast.mut_token) != .keyword_const) return false;

    const init_node = full.ast.init_node.unwrap() orelse return false;
    const init_idx = @intFromEnum(init_node);
    const tags = tree.nodes.items(.tag);
    if (init_idx >= tags.len) return false;

    const name_token = full.ast.mut_token + 1;
    if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return false;
    const public_name = tree.tokenSlice(name_token);

    return switch (tags[init_idx]) {
        .identifier => isReexportAlias(public_name, identifierName(tree, init_idx) orelse return false),
        .field_access => isReexportAlias(public_name, fieldAccessName(tree, init_idx) orelse return false),
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => isImportBuiltinCall(tree, init_idx),
        else => false,
    };
}

fn isImportBuiltinCall(tree: *const std.zig.Ast, node_idx: usize) bool {
    return importPathFromBuiltinCall(tree, node_idx) != null;
}

fn classifyVarDecl(tree: *const std.zig.Ast, full: std.zig.Ast.full.VarDecl) DeclKind {
    if (full.ast.init_node.unwrap()) |init_node| {
        const tag = tree.nodes.items(.tag)[@intFromEnum(init_node)];
        if (isContainerTag(tag) or tag == .error_set_decl) return .type_decl;
    }
    const mut_tag = tree.tokenTag(full.ast.mut_token);
    if (mut_tag == .keyword_const) return .constant;
    if (mut_tag == .keyword_var) return .variable;
    return .declaration;
}

fn collectProjectUsedDecls(
    allocator: std.mem.Allocator,
    files: []const FileInfo,
    resolver_files: []const import_resolver.File,
    decls: []const DeclInfo,
    references: *ProjectReferenceIndex,
) ![]bool {
    const used = try allocator.alloc(bool, decls.len);
    errdefer allocator.free(used);
    @memset(used, false);
    var usage = DeclUsage{ .allocator = allocator, .decls = decls, .used = used };
    defer usage.deinit();
    for (decls, 0..) |decl, decl_index| {
        const result = try usage.by_name.getOrPut(allocator, decl.normalized_name);
        if (!result.found_existing) result.value_ptr.* = .empty;
        try result.value_ptr.append(allocator, decl_index);
    }

    for (resolver_files, 0..) |file, file_index| {
        try usage.scanFile(resolver_files, file, file_index, references);
    }
    var cursor: usize = 0;
    while (cursor < usage.queue.items.len) : (cursor += 1) {
        const decl = decls[usage.queue.items[cursor]];
        var scanner = PublicSurfaceScanner{
            .tree = files[decl.file_index].tree,
            .usage = &usage,
            .file_index = decl.file_index,
        };
        try scanner.scanDecl(decl.node_index);
    }
    return used;
}

const DeclUsage = struct {
    allocator: std.mem.Allocator,
    decls: []const DeclInfo,
    used: []bool,
    by_name: std.StringHashMapUnmanaged(std.ArrayList(usize)) = .empty,
    queue: std.ArrayList(usize) = .empty,

    fn deinit(self: *DeclUsage) void {
        var values = self.by_name.valueIterator();
        while (values.next()) |value| value.deinit(self.allocator);
        self.by_name.deinit(self.allocator);
        self.queue.deinit(self.allocator);
    }

    fn mark(self: *DeclUsage, declaration: usize) !void {
        if (self.used[declaration]) return;
        try self.queue.append(self.allocator, declaration);
        self.used[declaration] = true;
    }

    fn hasUnused(self: *const DeclUsage, candidates: []const usize) bool {
        for (candidates) |candidate| {
            if (!self.used[candidate]) return true;
        }
        return false;
    }

    fn scanFile(
        self: *DeclUsage,
        files: []const import_resolver.File,
        file: import_resolver.File,
        file_index: usize,
        references: *ProjectReferenceIndex,
    ) !void {
        const tree = file.tree;
        if (tree.errors.len != 0) return;
        const namespaces = try references.usingTargets(file_index);
        const resolver = call_resolver.ProjectTypeResolver{ .files = files, .file_index = file_index };
        for (tree.nodes.items(.tag), 0..) |tag, node| {
            switch (tag) {
                .identifier => {
                    const name = identifierName(tree, node) orelse continue;
                    const candidates = self.by_name.get(name) orelse continue;
                    for (candidates.items) |candidate| {
                        const decl = self.decls[candidate];
                        if (decl.file_index == file_index) {
                            if (node != decl.node_index) try self.mark(candidate);
                        } else if (!std.mem.eql(u8, file.path, files[decl.file_index].path) and
                            std.mem.indexOfScalar(usize, namespaces, decl.file_index) != null)
                        {
                            try self.mark(candidate);
                        }
                    }
                },
                .field_access => {
                    const name = fieldAccessName(tree, node) orelse continue;
                    const candidates = self.by_name.get(name) orelse continue;
                    if (!self.hasUnused(candidates.items)) continue;
                    const receiver = @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]);
                    const targets = try references.namespaceTargets(file_index, receiver);
                    const receiver_type = resolver.resolveExprType(receiver);
                    for (candidates.items) |candidate| {
                        const decl = self.decls[candidate];
                        if (decl.file_index != file_index and std.mem.eql(u8, file.path, files[decl.file_index].path)) continue;
                        if (receiver_type) |actual| {
                            if (actual.file_index == decl.file_index and actual.container_node == null) {
                                try self.mark(candidate);
                                continue;
                            }
                        }
                        if (decl.file_index != file_index and std.mem.indexOfScalar(usize, targets, decl.file_index) != null) {
                            try self.mark(candidate);
                        }
                    }
                },
                .enum_literal => {
                    const name = normalizeIdentifier(tree.tokenSlice(tree.nodes.items(.main_token)[node]));
                    const candidates = self.by_name.get(name) orelse continue;
                    if (!self.hasUnused(candidates.items)) continue;
                    const expected = resolver.resolveResultLocationTypeNode(@intCast(node)) orelse continue;
                    const owner_resolver = call_resolver.ProjectTypeResolver{
                        .files = files,
                        .file_index = expected.file_index,
                    };
                    const owner = owner_resolver.resolveTypeNode(expected.node_index) orelse continue;
                    if (owner.container_node != null) continue;
                    for (candidates.items) |candidate| {
                        const decl = self.decls[candidate];
                        if (decl.file_index != owner.file_index) continue;
                        if (decl.file_index != file_index and std.mem.eql(u8, file.path, files[decl.file_index].path)) continue;
                        try self.mark(candidate);
                    }
                },
                .simple_var_decl, .aligned_var_decl, .global_var_decl, .local_var_decl => {
                    const full = tree.fullVarDecl(@enumFromInt(node)) orelse continue;
                    const initializer = full.ast.init_node.unwrap() orelse continue;
                    const name = implicitResultMethodName(tree, @intFromEnum(initializer)) orelse continue;
                    const candidates = self.by_name.get(name) orelse continue;
                    if (!self.hasUnused(candidates.items)) continue;
                    for (candidates.items) |candidate| {
                        const decl = self.decls[candidate];
                        if (decl.file_index != file_index and std.mem.eql(u8, file.path, files[decl.file_index].path)) continue;
                        if (resolver.varDeclInitializerReferencesExpectedTypeMethod(full, decl.file_index, name)) {
                            try self.mark(candidate);
                        }
                    }
                },
                else => {},
            }
        }
    }
};

fn implicitResultMethodName(tree: *const std.zig.Ast, initial: u32) ?[]const u8 {
    var node = initial;
    while (node < tree.nodes.len) {
        const data = tree.nodes.items(.data)[node];
        switch (tree.nodes.items(.tag)[node]) {
            .call, .call_comma, .call_one, .call_one_comma => {
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return null;
                const callee = @intFromEnum(call.ast.fn_expr);
                if (callee >= tree.nodes.len or tree.nodes.items(.tag)[callee] != .enum_literal) return null;
                return normalizeIdentifier(tree.tokenSlice(tree.nodes.items(.main_token)[callee]));
            },
            .@"try", .address_of, .deref, .optional_type => node = @intFromEnum(data.node),
            .grouped_expression, .unwrap_optional => node = @intFromEnum(data.node_and_token[0]),
            .@"catch" => node = @intFromEnum(data.node_and_node[0]),
            else => return null,
        }
    }
    return null;
}

const PublicSurfaceScanner = struct {
    tree: *const std.zig.Ast,
    usage: *DeclUsage,
    file_index: usize,
    stop: bool = false,

    fn scanDecl(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const tags = self.tree.nodes.items(.tag);
        if (node >= tags.len) return;

        switch (tags[node]) {
            .simple_var_decl,
            .aligned_var_decl,
            .global_var_decl,
            => try self.scanVarDeclSurface(node),
            .fn_decl => {
                const data = self.tree.nodes.items(.data)[node];
                try self.scanFnProto(@intFromEnum(data.node_and_node[0]));
            },
            .fn_proto,
            .fn_proto_simple,
            .fn_proto_one,
            .fn_proto_multi,
            => try self.scanFnProto(node),
            else => {},
        }
    }

    fn scanVarDeclSurface(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const full = self.tree.fullVarDecl(@enumFromInt(node)) orelse return;
        try self.scanOptionalNode(full.ast.type_node);

        const init_node = full.ast.init_node.unwrap() orelse return;
        const init_idx = @intFromEnum(init_node);
        const tags = self.tree.nodes.items(.tag);
        if (init_idx < tags.len and isContainerTag(tags[init_idx])) {
            try self.scanContainerSurface(init_idx);
        } else {
            try self.scanNode(init_idx);
        }
    }

    fn scanFnProto(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const tags = self.tree.nodes.items(.tag);
        if (node >= tags.len) return;

        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = switch (tags[node]) {
            .fn_proto => self.tree.fnProto(@enumFromInt(node)),
            .fn_proto_simple => self.tree.fnProtoSimple(&buffer, @enumFromInt(node)),
            .fn_proto_one => self.tree.fnProtoOne(&buffer, @enumFromInt(node)),
            .fn_proto_multi => self.tree.fnProtoMulti(@enumFromInt(node)),
            else => return,
        };

        for (proto.ast.params) |param| try self.scanParam(@intFromEnum(param));
        try self.scanOptionalNode(proto.ast.return_type);
        try self.scanOptionalNode(proto.ast.align_expr);
        try self.scanOptionalNode(proto.ast.addrspace_expr);
        try self.scanOptionalNode(proto.ast.section_expr);
        try self.scanOptionalNode(proto.ast.callconv_expr);
    }

    fn scanParam(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const tags = self.tree.nodes.items(.tag);
        if (node >= tags.len) return;

        if (isVarDeclTag(tags[node])) {
            const full = self.tree.fullVarDecl(@enumFromInt(node)) orelse return;
            try self.scanOptionalNode(full.ast.type_node);
            return;
        }

        try self.scanNode(node);
    }

    fn scanContainerSurface(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const tags = self.tree.nodes.items(.tag);
        if (node >= tags.len) return;

        switch (tags[node]) {
            .container_decl,
            .container_decl_trailing,
            => try self.scanContainerDeclComponents(self.tree.containerDecl(@enumFromInt(node))),
            .container_decl_two,
            .container_decl_two_trailing,
            => {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                try self.scanContainerDeclComponents(self.tree.containerDeclTwo(&buffer, @enumFromInt(node)));
            },
            .container_decl_arg,
            .container_decl_arg_trailing,
            => try self.scanContainerDeclComponents(self.tree.containerDeclArg(@enumFromInt(node))),
            .tagged_union,
            .tagged_union_trailing,
            => try self.scanContainerDeclComponents(self.tree.taggedUnion(@enumFromInt(node))),
            .tagged_union_enum_tag,
            .tagged_union_enum_tag_trailing,
            => try self.scanContainerDeclComponents(self.tree.taggedUnionEnumTag(@enumFromInt(node))),
            .tagged_union_two,
            .tagged_union_two_trailing,
            => {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                try self.scanContainerDeclComponents(self.tree.taggedUnionTwo(&buffer, @enumFromInt(node)));
            },
            else => {},
        }
    }

    fn scanContainerDeclComponents(
        self: *PublicSurfaceScanner,
        container: std.zig.Ast.full.ContainerDecl,
    ) anyerror!void {
        if (container.ast.arg.unwrap()) |arg_node| try self.scanNode(@intFromEnum(arg_node));

        const tags = self.tree.nodes.items(.tag);
        for (container.ast.members) |member_node| {
            const member = @intFromEnum(member_node);
            if (member >= tags.len) continue;

            switch (tags[member]) {
                .container_field,
                .container_field_init,
                .container_field_align,
                => try self.scanContainerField(member),
                .simple_var_decl,
                .aligned_var_decl,
                .global_var_decl,
                => {
                    const full = self.tree.fullVarDecl(@enumFromInt(member)) orelse continue;
                    if (isPubToken(self.tree, full.visib_token)) try self.scanVarDeclSurface(member);
                },
                .fn_decl,
                .fn_proto,
                .fn_proto_simple,
                .fn_proto_one,
                .fn_proto_multi,
                => if (isPublicFnDecl(self.tree, member)) try self.scanDecl(member),
                else => {},
            }
        }
    }

    fn scanContainerField(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const field = self.tree.fullContainerField(@enumFromInt(node)) orelse return;
        try self.scanOptionalNode(field.ast.type_expr);
        try self.scanOptionalNode(field.ast.value_expr);
        try self.scanOptionalNode(field.ast.align_expr);
    }

    fn scanOptionalNode(self: *PublicSurfaceScanner, node_opt: std.zig.Ast.Node.OptionalIndex) anyerror!void {
        if (node_opt.unwrap()) |node| try self.scanNode(@intFromEnum(node));
    }

    fn scanNode(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        try ast_walk.walk(PublicSurfaceScanner, self.tree, node, self);
    }

    pub fn visit(
        self: *PublicSurfaceScanner,
        tree: *const std.zig.Ast,
        node: u32,
        tag: std.zig.Ast.Node.Tag,
    ) anyerror!void {
        if (tag != .identifier) return;

        const main_tokens = tree.nodes.items(.main_token);
        if (node >= main_tokens.len) return;
        try self.markIdentifier(tree.tokenSlice(main_tokens[node]));
    }

    fn markIdentifier(self: *PublicSurfaceScanner, identifier: []const u8) !void {
        const candidates = self.usage.by_name.get(normalizeIdentifier(identifier)) orelse return;
        for (candidates.items) |candidate| {
            if (self.usage.decls[candidate].file_index != self.file_index) continue;
            try self.usage.mark(candidate);
        }
    }
};

fn isReexportAlias(public_name: []const u8, referenced_name: []const u8) bool {
    const normalized_public = normalizeIdentifier(public_name);
    const normalized_referenced = normalizeIdentifier(referenced_name);
    if (std.mem.eql(u8, normalized_public, normalized_referenced)) return true;
    return isTypeLikeName(normalized_public) and isTypeLikeName(normalized_referenced);
}

fn isTypeLikeName(name: []const u8) bool {
    if (name.len == 0) return false;
    return std.ascii.isUpper(name[0]);
}

fn isIgnoredPublicDecl(path: []const u8, name: []const u8) bool {
    if (isSpecialName(name)) return true;
    return std.mem.eql(u8, std.fs.path.basename(path), "build.zig") and std.mem.eql(u8, name, "build");
}

fn isSpecialName(name: []const u8) bool {
    if (name.len > 0 and name[0] == '_') return true;
    if (std.mem.eql(u8, name, "main")) return true;
    if (std.mem.eql(u8, name, "panic")) return true;
    if (std.mem.eql(u8, name, "std_options")) return true;
    return false;
}

fn isPublicFnDecl(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;

    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = switch (tags[node]) {
        .fn_decl => blk: {
            const data = tree.nodes.items(.data)[node];
            const proto_node = @intFromEnum(data.node_and_node[0]);
            break :blk switch (tags[proto_node]) {
                .fn_proto => tree.fnProto(@enumFromInt(proto_node)),
                .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)),
                .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(proto_node)),
                .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)),
                else => return false,
            };
        },
        .fn_proto => tree.fnProto(@enumFromInt(node)),
        .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(node)),
        .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(node)),
        .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(node)),
        else => return false,
    };

    return isPubToken(tree, proto.visib_token);
}

fn isContainerTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .container_decl,
        .container_decl_trailing,
        .container_decl_two,
        .container_decl_two_trailing,
        .container_decl_arg,
        .container_decl_arg_trailing,
        .tagged_union,
        .tagged_union_trailing,
        .tagged_union_enum_tag,
        .tagged_union_enum_tag_trailing,
        .tagged_union_two,
        .tagged_union_two_trailing,
        => true,
        else => false,
    };
}

test "project unused source selection uses discovered API root scope" {
    const allocator = std.testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile(
        "build.zig",
        "const build_api = @import(\"std\");\n" ++
            "const Fake = struct {\n" ++
            "    fn addModule(_: anytype, _: anytype) void {}\n" ++
            "    fn path(_: []const u8) build_api.LazyPath {\n" ++
            "        return .{ .cwd_relative = \"not-api.zig\" };\n" ++
            "    }\n" ++
            "};\n" ++
            "const main = @import(\"main.zig\");\n" ++
            "pub fn contextOnly() void {}\n" ++
            "pub fn build(b: *build_api.Build) void {\n" ++
            "    {\n" ++
            "        const b = Fake;\n" ++
            "        _ = b.addModule(.{ .root_source_file = b.path(\"unrelated.zig\") });\n" ++
            "    }\n" ++
            "    _ = Fake.addModule(b, .{ .root_source_file = b.path(\"unrelated.zig\") });\n" ++
            "    _ = b.addModule(\"not_api\", .{ .root_source_file = Fake.path(\"unrelated.zig\") });\n" ++
            "    _ = b.addConfigHeader(.{}, .{ .root_source_file = b.path(\"unrelated.zig\") });\n" ++
            "    _ = b.addModule(\"fixture\", .{ .root_source_file = b.path(\"api.zig\") });\n" ++
            "    _ = main.publicUnused;\n" ++
            "}\n",
    );
    try temp_dir.writeFile(
        "api.zig",
        "pub fn exportedByPackage() void {}\n",
    );
    try temp_dir.writeFile(
        "main.zig",
        "pub fn publicUnused() void {}\n",
    );
    try temp_dir.writeFile(
        "unrelated.zig",
        "pub fn unrelatedUnused() void {}\n",
    );

    var api_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    var main_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    var unrelated_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const api_path = try std.fmt.bufPrint(
        &api_path_buffer,
        "{s}/api.zig",
        .{temp_dir.path()},
    );
    const main_path = try std.fmt.bufPrint(
        &main_path_buffer,
        "{s}/main.zig",
        .{temp_dir.path()},
    );
    const unrelated_path = try std.fmt.bufPrint(
        &unrelated_path_buffer,
        "{s}/unrelated.zig",
        .{temp_dir.path()},
    );
    const selected_files = [_][]const u8{ api_path, main_path, unrelated_path };

    var project = try ProjectSources.init(&io_context, allocator, &selected_files);
    defer project.deinit();
    for (project.files()) |file| try std.testing.expectEqual(0, file.tree.errors.len);

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*item| item.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    var found_unrelated = false;
    for (diagnostics.items) |diagnostic| {
        if (std.mem.eql(u8, diagnostic.file_path, unrelated_path)) {
            found_unrelated = std.mem.indexOf(u8, diagnostic.message, "unrelatedUnused") != null;
        }
    }
    try std.testing.expect(found_unrelated);
}

test "project unused rejects a shadowed std build type" {
    const allocator = std.testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile(
        "build.zig",
        "const std = struct { pub const Build = struct {}; };\n" ++
            "pub fn build(b: *std.Build) void {\n" ++
            "    _ = b.addModule(\"fixture\", .{ .root_source_file = b.path(\"api.zig\") });\n" ++
            "}\n",
    );
    try temp_dir.writeFile("api.zig", "pub fn exportedByPackage() void {}\n");
    try temp_dir.writeFile("main.zig", "pub fn publicUnused() void {}\n");

    var api_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    var main_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const api_path = try std.fmt.bufPrint(
        &api_path_buffer,
        "{s}/api.zig",
        .{temp_dir.path()},
    );
    const main_path = try std.fmt.bufPrint(
        &main_path_buffer,
        "{s}/main.zig",
        .{temp_dir.path()},
    );
    const selected_files = [_][]const u8{ api_path, main_path };

    var project = try ProjectSources.init(&io_context, allocator, &selected_files);
    defer project.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*item| item.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var found_api = false;
    var found_main = false;
    for (diagnostics.items) |diagnostic| {
        if (std.mem.eql(u8, diagnostic.file_path, api_path)) {
            found_api = std.mem.indexOf(u8, diagnostic.message, "exportedByPackage") != null;
        } else if (std.mem.eql(u8, diagnostic.file_path, main_path)) {
            found_main = std.mem.indexOf(u8, diagnostic.message, "publicUnused") != null;
        }
    }
    try std.testing.expect(found_api);
    try std.testing.expect(found_main);
}

test "project public API closure follows conditional aliases and cycles" {
    const allocator = std.testing.allocator;
    var root = try std.zig.Ast.parse(allocator,
        \\const selected = @import("left.zig");
        \\pub const api = if (@import("condition.zig").enabled) selected else @import("right.zig");
        \\pub const value = make(@import("hidden.zig"));
    , .zig);
    defer root.deinit(allocator);
    var left = try std.zig.Ast.parse(allocator,
        \\pub const cycle = @import("root.zig");
        \\pub const leaf = @import("leaf.zig");
    , .zig);
    defer left.deinit(allocator);
    var empty = try std.zig.Ast.parse(allocator, "", .zig);
    defer empty.deinit(allocator);
    const files = [_]import_resolver.File{
        .{ .path = "root.zig", .tree = &root },
        .{ .path = "left.zig", .tree = &left },
        .{ .path = "right.zig", .tree = &empty },
        .{ .path = "leaf.zig", .tree = &empty },
        .{ .path = "condition.zig", .tree = &empty },
        .{ .path = "hidden.zig", .tree = &empty },
    };
    var project = try ProjectContext.init(allocator, &files, &.{});
    defer project.deinit();
    try project.appendApiRoot(0);
    try project.collectPublicApiFiles();
    for (0..4) |index| try std.testing.expect(project.isPublicApiFile(index));
    try std.testing.expect(!project.isPublicApiFile(4));
    try std.testing.expect(!project.isPublicApiFile(5));
}

test "project references retain typed reexports without promoting homonyms" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var directory = compat.TestDir.init();
    defer directory.cleanup();
    try directory.writeFile("api.zig",
        \\const Self = @This();
        \\pub const Leaf = struct {};
        \\pub const Wrapper = struct { child: Leaf, next: ?*Wrapper };
        \\pub fn run(_: *Self) Wrapper { return undefined; }
        \\pub fn unused() void {}
    );
    try directory.writeFile("facade.zig", "pub const api = @import(\"api.zig\");\n");
    try directory.writeFile("decoy.zig", "pub fn run() void {}\n");
    try directory.writeFile("consumer.zig",
        \\const facade = @import("facade.zig");
        \\pub fn main() void {
        \\    var api: facade.api = .{};
        \\    _ = api.run();
        \\}
        \\fn dynamic(receiver: anytype) void { receiver.unused(); }
    );
    const names = [_][]const u8{ "api.zig", "facade.zig", "decoy.zig", "consumer.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ directory.path(), name });
    }
    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*item| item.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var found_unused = false;
    var found_homonym = false;
    for (diagnostics.items) |diagnostic| {
        if (std.mem.eql(u8, diagnostic.file_path, paths[0])) {
            found_unused = std.mem.indexOf(u8, diagnostic.message, "unused") != null;
        } else if (std.mem.eql(u8, diagnostic.file_path, paths[2])) {
            found_homonym = std.mem.indexOf(u8, diagnostic.message, "run") != null;
        }
    }
    try std.testing.expect(found_unused);
    try std.testing.expect(found_homonym);
}

test "project contextual constants retain only their expected container" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var directory = compat.TestDir.init();
    defer directory.cleanup();
    const constant = "pub const empty: @This() = .{};\n";
    try directory.writeFile("assigned.zig", constant);
    try directory.writeFile("returned.zig", constant);
    try directory.writeFile("initialized.zig", constant);
    try directory.writeFile("decoy.zig", constant);
    try directory.writeFile("nested.zig", constant ++
        "pub const Item = struct { pub const empty: @This() = .{}; };\n");
    try directory.writeFile(
        "consumer.zig",
        "const Assigned = @import(\"assigned.zig\");\n" ++
            "const Returned = @import(\"returned.zig\");\n" ++
            "const Initialized = @import(\"initialized.zig\");\n" ++
            "const Nested = @import(\"nested.zig\").Item;\n" ++
            "fn reset(value: *Assigned) void { value.* = .empty; }\n" ++
            "fn make() error{OutOfMemory}!Returned { return .empty; }\n" ++
            "pub fn main() void {\n" ++
            "    var assigned: Assigned = .{};\n" ++
            "    reset(&assigned);\n" ++
            "    _ = make() catch return;\n" ++
            "    const initialized: Initialized = .empty;\n" ++
            "    const nested: Nested = .empty;\n" ++
            "    _ = initialized;\n" ++
            "    _ = nested;\n" ++
            "}\n",
    );
    const names = [_][]const u8{
        "assigned.zig", "returned.zig", "initialized.zig",
        "decoy.zig",    "nested.zig",   "consumer.zig",
    };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ directory.path(), name });
    }
    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var found_decoy = false;
    var found_nested = false;
    for (diagnostics.items) |diagnostic| {
        try std.testing.expectEqual(@as(usize, 1), diagnostic.range.start.line);
        if (std.mem.eql(u8, diagnostic.file_path, paths[3])) found_decoy = true;
        if (std.mem.eql(u8, diagnostic.file_path, paths[4])) found_nested = true;
    }
    try std.testing.expect(found_decoy);
    try std.testing.expect(found_nested);
}

test "project unused declarations ignore Zig build entrypoint" {
    try std.testing.expect(isIgnoredPublicDecl("build.zig", "build"));
    try std.testing.expect(isIgnoredPublicDecl("workspace/build.zig", "build"));
    try std.testing.expect(!isIgnoredPublicDecl("src/lib.zig", "build"));
    try std.testing.expect(!isIgnoredPublicDecl("build.zig", "helper"));
}

test "project unused analysis requires complete source and build syntax" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var directory = compat.TestDir.init();
    defer directory.cleanup();
    try directory.writeFile("a.zig",
        \\pub fn unusedA() void {}
        \\fn use() void {
        \\    _ = @import("b.zig").used;
        \\}
    );
    try directory.writeFile("b.zig", "pub fn unusedB() void {}\npub const used = 1;\n");
    const complete_source = "pub fn ignored() void {}\n";
    const complete_build =
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    _ = b.addModule("fixture", .{ .root_source_file = b.path("b.zig") });
        \\}
    ;
    const scenarios = [_]struct { source: []const u8, build: []const u8, expected: usize }{
        .{ .source = "const broken = ;", .build = complete_build, .expected = 0 },
        .{ .source = complete_source, .build = "const broken = ;", .expected = 0 },
        .{ .source = complete_source, .build = complete_build, .expected = 2 },
    };
    const names = [_][]const u8{ "a.zig", "malformed.zig", "b.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ directory.path(), name });
    }
    const Harness = struct {
        fn run(failing_allocator: std.mem.Allocator, sources: *const ProjectSources, expected: usize) !void {
            var diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer {
                for (diagnostics.items) |*item| item.deinit(failing_allocator);
                diagnostics.deinit(failing_allocator);
            }
            try analyze(sources, failing_allocator, &diagnostics);
            try std.testing.expectEqual(expected, diagnostics.items.len);
            if (expected == 0) return;
            try std.testing.expectEqualStrings("a.zig", std.fs.path.basename(diagnostics.items[0].file_path));
            try std.testing.expectEqualStrings("malformed.zig", std.fs.path.basename(diagnostics.items[1].file_path));
        }
    };
    for (scenarios) |scenario| {
        try directory.writeFile("malformed.zig", scenario.source);
        try directory.writeFile("build.zig", scenario.build);
        var project = try ProjectSources.init(&io_context, allocator, &paths);
        defer project.deinit();
        try std.testing.checkAllAllocationFailures(allocator, Harness.run, .{ &project, scenario.expected });
    }
}
