const std = @import("std");
const import_resolver = @import("import_resolver.zig");
const lexical_index = @import("lexical_index.zig");
const LexicalIndex = lexical_index.LexicalIndex;
const ast_walk = @import("../ast_walk.zig");
const TypeContext = @import("../type_context.zig").TypeContext;
const TypeInfo = @import("../zir_bridge.zig").TypeInfo;

const log = std.log.scoped(.call_resolver);

/// Frames a bounded resolution walk in this file may consume before it has to
/// answer conservatively. The limit bounds stack use; it is not evidence that
/// the chain is absent, so every exit at the limit names the walk that stopped.
const resolution_budget_frames: usize = 64;

/// Parent-map climb budget for ancestor queries, reported like any other one.
const ancestor_map_budget_frames: usize = 256;

pub const ResolvedType = struct {
    file_index: usize,
    type_name: ?[]const u8 = null,
    container_node: ?u32 = null,
};

/// A return type expression together with the source file that owns it.
pub const ResolvedTypeNode = struct {
    file_index: usize,
    node_index: u32,
    inferred_error_union: bool = false,
};

pub const CallInfo = struct {
    call_node: u32,
    method_name: []const u8,
    receiver_type: ?[]const u8,
    fqn: ?[]const u8,
    base_node: ?u32,
    param_count: usize,
};

pub fn isCallNode(tag: std.zig.Ast.Node.Tag) bool {
    return tag == .call or tag == .call_comma or tag == .call_one or tag == .call_one_comma;
}

pub fn resolveCall(
    tree: *const std.zig.Ast,
    type_ctx: ?*TypeContext,
    call_node: u32,
    fqn_buffer: *[256]u8,
) ?CallInfo {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const token_tags = tree.tokens.items(.tag);

    if (call_node >= tags.len or !isCallNode(tags[call_node])) return null;

    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
    const full_call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return null;
    const callee_node: u32 = @intFromEnum(full_call.ast.fn_expr);
    if (callee_node >= tags.len) return null;

    return switch (tags[callee_node]) {
        .identifier => blk: {
            const token = tree.nodes.items(.main_token)[callee_node];
            if (token >= token_tags.len or token_tags[token] != .identifier) return null;
            const name = tree.tokenSlice(token);
            break :blk .{
                .call_node = call_node,
                .method_name = name,
                .receiver_type = null,
                .fqn = name,
                .base_node = null,
                .param_count = full_call.ast.params.len,
            };
        },
        .field_access => blk: {
            const field_access_data = datas[callee_node].node_and_token;
            const base_node = @intFromEnum(field_access_data[0]);
            const field_token = field_access_data[1];
            if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return null;
            const field_name = tree.tokenSlice(field_token);
            const receiver_type = getReceiverTypeName(type_ctx, tree, base_node);
            const fqn = constructFqn(tree, base_node, field_name, fqn_buffer);
            break :blk .{
                .call_node = call_node,
                .method_name = field_name,
                .receiver_type = receiver_type,
                .fqn = fqn,
                .base_node = base_node,
                .param_count = full_call.ast.params.len,
            };
        },
        else => null,
    };
}

pub fn callParam(tree: *const std.zig.Ast, call_node: u32, index: usize) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (call_node >= tags.len or !isCallNode(tags[call_node])) return null;

    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
    const full_call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return null;
    if (index >= full_call.ast.params.len) return null;
    return @intFromEnum(full_call.ast.params[index]);
}

pub fn getReceiverTypeName(type_ctx: ?*TypeContext, tree: *const std.zig.Ast, base_node: u32) ?[]const u8 {
    const ctx = type_ctx orelse return null;
    const tags = tree.nodes.items(.tag);
    if (base_node >= tags.len) return null;
    if (ctx.getExpressionType(base_node)) |ti| {
        return ti.type_str;
    }
    return null;
}

pub fn constructFqn(
    tree: *const std.zig.Ast,
    base_node: u32,
    method_name: []const u8,
    buffer: *[256]u8,
) ?[]const u8 {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_tags = tree.tokens.items(.tag);

    var parts: [16][]const u8 = undefined;
    var count: usize = 0;
    var node = base_node;

    while (true) {
        if (node >= tags.len) return null;

        switch (tags[node]) {
            .identifier => {
                const ident_token = main_tokens[node];
                if (ident_token >= token_tags.len or token_tags[ident_token] != .identifier) return null;
                if (count >= parts.len) return null;
                parts[count] = tree.tokenSlice(ident_token);
                count += 1;
                break;
            },
            .field_access => {
                const field_access = datas[node].node_and_token;
                const field_token = field_access[1];
                if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return null;
                if (count >= parts.len) return null;
                parts[count] = tree.tokenSlice(field_token);
                count += 1;
                node = @intFromEnum(field_access[0]);
            },
            else => return null,
        }
    }

    var pos: usize = 0;
    var idx: usize = count;
    while (idx > 0) : (idx -= 1) {
        if (!appendFqnPart(buffer, parts[idx - 1], &pos)) return null;
        if (idx > 1 and !appendFqnSeparator(buffer, &pos)) return null;
    }

    if (!appendFqnSeparator(buffer, &pos)) return null;
    if (!appendFqnPart(buffer, method_name, &pos)) return null;

    return buffer[0..pos];
}

/// Path of the file a `TypeContext` tree belongs to, so a budget cut-off can
/// name the source it truncated.
fn typeContextFilePath(type_ctx: *TypeContext, tree: *const std.zig.Ast) ?[]const u8 {
    if (type_ctx.project_resolver) |project| {
        for (project.files) |file| {
            if (file.tree == tree) return file.path;
        }
        return null;
    }
    return type_ctx.source.file_path;
}

pub fn resolveResultLocationType(
    tree: *const std.zig.Ast,
    type_ctx: *TypeContext,
    parent_map: []const u32,
    expr_node: u32,
) ?TypeInfo {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const token_tags = tree.tokens.items(.tag);

    var node = expr_node;
    var depth: u32 = 0;
    while (node < parent_map.len) {
        if (depth >= resolution_budget_frames) {
            reportResolutionBudget("result-location parent climb", resolution_budget_frames, typeContextFilePath(type_ctx, tree));
            return null;
        }
        depth += 1;
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;

        switch (tags[parent]) {
            .grouped_expression, .unwrap_optional, .@"try", .@"catch", .if_simple, .@"if" => {
                node = parent;
                continue;
            },
            .call, .call_comma, .call_one, .call_one_comma => {
                return resolveCallArgumentType(tree, type_ctx, parent, expr_node, parent_map);
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                if (builtinCallName(tree, tags, token_tags, parent)) |name| {
                    if (std.mem.eql(u8, name, "@as")) {
                        var buf: [2]std.zig.Ast.Node.Index = undefined;
                        const params = tree.builtinCallParams(&buf, @enumFromInt(parent)) orelse return null;
                        if (params.len < 2) return null;
                        const type_node = @intFromEnum(params[0]);
                        const value_node = @intFromEnum(params[1]);
                        if (!nodeIsAncestor(value_node, expr_node, parent_map)) return null;
                        if (type_ctx.getTypeFromAstNode(type_node)) |ti| return ti;
                        return typeInfoFromTypeNode(tree, tags, datas, type_node);
                    }
                }
                return null;
            },
            .simple_var_decl, .local_var_decl, .global_var_decl, .aligned_var_decl => {
                const full = tree.fullVarDecl(@enumFromInt(parent)) orelse return null;
                if (full.ast.type_node.unwrap()) |type_node| {
                    if (type_ctx.getTypeFromAstNode(@intFromEnum(type_node))) |ti| return ti;
                    if (typeInfoFromTypeNode(tree, tags, datas, @intFromEnum(type_node))) |ti| return ti;
                }
                if (full.ast.init_node.unwrap()) |init_node| {
                    if (nodeIsAncestor(@intFromEnum(init_node), expr_node, parent_map)) {
                        if (type_ctx.getExpressionTypeStrict(@intFromEnum(init_node))) |ti| {
                            if (!isUnknownTypeInfo(ti)) return ti;
                        }
                    }
                }
                return null;
            },
            .@"return" => {
                if (findAncestorFn(type_ctx, tree, parent_map, parent)) |fn_node| {
                    if (type_ctx.getContainingFunctionReturnType(fn_node)) |ti| {
                        if (!isUnknownTypeInfo(ti)) return ti;
                    }
                    if (returnTypeInfoFromFn(tree, tags, datas, fn_node)) |ti| return ti;
                }
                return null;
            },
            else => {
                if (isAssignTag(tags[parent])) {
                    const pair = datas[parent].node_and_node;
                    const lhs = @intFromEnum(pair[0]);
                    const rhs = @intFromEnum(pair[1]);
                    if (nodeIsAncestor(rhs, expr_node, parent_map)) {
                        if (type_ctx.getExpressionTypeStrict(lhs)) |ti| {
                            if (!isUnknownTypeInfo(ti)) return ti;
                        }
                    }
                }
                return null;
            },
        }
    }
    return null;
}

fn resolveCallArgumentType(
    tree: *const std.zig.Ast,
    type_ctx: *TypeContext,
    parent_call: u32,
    expr_node: u32,
    parent_map: []const u32,
) ?TypeInfo {
    var files = [_]import_resolver.File{
        .{ .path = "", .tree = tree },
    };
    // Borrow the project file that owns this tree first, then the source's own
    // immutable syntax facts, so this single-file resolver stops walking every
    // node per query. Both borrow; the source outlives the resolver.
    if (type_ctx.project_resolver) |project| {
        const file = project.files[project.file_index];
        if (file.tree == tree) files[0].lexical_index = file.lexical_index;
    }
    if (files[0].lexical_index == null) files[0].lexical_index = type_ctx.lexicalIndexForTree(tree);
    const resolver = ProjectTypeResolver{
        .files = &files,
        .file_index = 0,
    };
    const type_node = resolver.resolveCallArgumentTypeNode(parent_call, expr_node, parent_map) orelse return null;

    if (type_ctx.getTypeFromAstNode(type_node)) |type_info| {
        if (!isUnknownTypeInfo(type_info)) return type_info;
    }
    if (resolver.resolveTypeNode(type_node)) |resolved| {
        if (resolved.type_name) |type_name| {
            return .{ .kind = .unknown, .type_str = type_name };
        }
    }
    return typeInfoFromTypeNode(
        tree,
        tree.nodes.items(.tag),
        tree.nodes.items(.data),
        type_node,
    );
}

const BindingResolution = struct {
    found: bool = false,
    resolved: ?ResolvedType = null,
    declaration_node: ?u32 = null,
    is_type_namespace: bool = false,
};

const ScopeRange = lexical_index.ScopeRange;

/// Identity of the function a call expression actually reaches.
///
/// `file_index` and `proto_node` together name one prototype in one project
/// file, so a consumer can compare a resolved callee against another one for
/// equality without re-deriving either half. `implicit_self_count` is the
/// number of leading prototype parameters that are not written at the call
/// site; explicit argument `i` is prototype parameter `i + implicit_self_count`.
/// A prototype that only resolves for some receivers (a generic, or a member
/// found through a type the receiver expression does not pin down) is never
/// reported here: the record is only produced once the binding is unambiguous.
pub const CallableInfo = struct {
    proto_node: u32,
    file_index: usize,
    implicit_self_count: usize,
};

/// Malformed source files retain their IDs but do not provide declarations or types.
pub const ProjectTypeResolver = struct {
    files: []const import_resolver.File,
    file_index: usize,
    active_binding: ?*const BindingFrame = null,

    const BindingFrame = struct {
        file_index: usize,
        reference_node: usize,
        name: []const u8,
        previous: ?*const BindingFrame,
    };

    fn forFile(self: ProjectTypeResolver, file_index: usize) ProjectTypeResolver {
        var resolver = self;
        resolver.file_index = file_index;
        return resolver;
    }

    fn enterBinding(
        self: ProjectTypeResolver,
        name: []const u8,
        node: usize,
        frame: *BindingFrame,
    ) ?ProjectTypeResolver {
        var active = self.active_binding;
        while (active) |entry| : (active = entry.previous) {
            if (entry.file_index == self.file_index and
                entry.reference_node == node and
                std.mem.eql(u8, entry.name, name)) return null;
        }
        frame.* = .{
            .file_index = self.file_index,
            .reference_node = node,
            .name = name,
            .previous = self.active_binding,
        };
        var resolver = self;
        resolver.active_binding = frame;
        return resolver;
    }

    fn currentFile(self: ProjectTypeResolver) import_resolver.File {
        return self.files[self.file_index];
    }

    fn parentNode(self: ProjectTypeResolver, node: u32) ?u32 {
        const file = self.currentFile();
        if (file.lexical_index) |index| return index.parent(node);
        return findParentNode(file.tree, node);
    }

    fn enclosingFunctionAt(self: ProjectTypeResolver, token: u32) ?u32 {
        const file = self.currentFile();
        if (file.lexical_index) |index| return index.enclosingFunction(token);
        return findEnclosingFunction(file.tree, file.tree.nodes.items(.tag), token);
    }

    fn isRootDeclaration(self: ProjectTypeResolver, node: usize) bool {
        const file = self.currentFile();
        if (file.lexical_index) |index| return index.isRootDeclaration(node);
        return isRootDeclNode(file.tree, node);
    }

    pub fn resolveExprType(self: ProjectTypeResolver, node: usize) ?ResolvedType {
        const tree = self.currentFile().tree;
        if (tree.errors.len != 0) return null;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;

        switch (tags[node]) {
            .identifier => {
                const name = import_resolver.identifierName(tree, node) orelse return null;
                return self.resolveNameType(name, node);
            },
            .field_access => {
                const datas = tree.nodes.items(.data);
                const field_access = datas[node].node_and_token;
                const lhs = @intFromEnum(field_access[0]);
                const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(field_access[1]));
                const base_type = self.resolveExprType(lhs) orelse return null;
                return self.resolveMemberType(base_type, member_name);
            },
            .array_access => return self.resolveArrayAccessType(@intCast(node)),
            .call,
            .call_comma,
            .call_one,
            .call_one_comma,
            => return self.resolveCallType(@intCast(node)),
            .struct_init,
            .struct_init_comma,
            .struct_init_one,
            .struct_init_one_comma,
            .struct_init_dot,
            .struct_init_dot_comma,
            .struct_init_dot_two,
            .struct_init_dot_two_comma,
            => return self.resolveStructInitType(@intCast(node)),
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => return self.resolveBuiltinType(@intCast(node)),
            else => return null,
        }
    }

    pub fn resolveTypeNode(self: ProjectTypeResolver, node: usize) ?ResolvedType {
        const tree = self.currentFile().tree;
        if (tree.errors.len != 0) return null;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;
        if (isContainerTag(tags[node])) return .{ .file_index = self.file_index, .container_node = @intCast(node) };

        switch (tags[node]) {
            .identifier => {
                const name = import_resolver.identifierName(tree, node) orelse return null;
                return self.resolveNameType(name, node);
            },
            .field_access => {
                const datas = tree.nodes.items(.data);
                const field_access = datas[node].node_and_token;
                const lhs = @intFromEnum(field_access[0]);
                const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(field_access[1]));
                const base_type = self.resolveTypeNode(lhs) orelse self.resolveExprType(lhs) orelse return null;
                return self.resolveMemberType(base_type, member_name);
            },
            .ptr_type,
            .ptr_type_aligned,
            .ptr_type_bit_range,
            .ptr_type_sentinel,
            => {
                const ptr = tree.fullPtrType(@enumFromInt(node)) orelse return null;
                return self.resolveTypeNode(@intFromEnum(ptr.ast.child_type));
            },
            .optional_type => return self.resolveTypeNode(@intFromEnum(tree.nodes.items(.data)[node].node)),
            .error_union => return self.resolveTypeNode(@intFromEnum(tree.nodes.items(.data)[node].node_and_node[1])),
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => return self.resolveBuiltinType(@intCast(node)),
            else => return null,
        }
    }
    pub fn resolveTypeAliasNode(self: ProjectTypeResolver, node: u32) ?ResolvedTypeNode {
        const tree = self.currentFile().tree;
        if (tree.errors.len != 0) return null;
        if (node >= tree.nodes.len) return null;
        switch (tree.nodeTag(@enumFromInt(node))) {
            .identifier => {
                const declaration = self.resolveDeclarationNode(node) orelse return null;
                return self.constInitializer(self.file_index, declaration);
            },
            .field_access => {
                const access = tree.nodeData(@enumFromInt(node)).node_and_token;
                const owner = self.resolveTypeNode(@intFromEnum(access[0])) orelse return null;
                const owner_tree = self.files[owner.file_index].tree;
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const members = if (owner.container_node) |container|
                    (owner_tree.fullContainerDecl(&buffer, @enumFromInt(container)) orelse return null).ast.members
                else
                    owner_tree.rootDecls();
                const name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                for (members) |member| {
                    const full = owner_tree.fullVarDecl(member) orelse continue;
                    const declared = import_resolver.normalizeIdentifier(owner_tree.tokenSlice(full.ast.mut_token + 1));
                    if (!std.mem.eql(u8, name, declared)) continue;
                    return self.constInitializer(owner.file_index, @intFromEnum(member));
                }
                return null;
            },
            else => return null,
        }
    }

    fn constInitializer(self: ProjectTypeResolver, file_index: usize, declaration: u32) ?ResolvedTypeNode {
        const tree = self.files[file_index].tree;
        const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return null;
        if (tree.tokenTag(full.ast.mut_token) != .keyword_const) return null;
        const initializer = full.ast.init_node.unwrap() orelse return null;
        return .{ .file_index = file_index, .node_index = @intFromEnum(initializer) };
    }

    pub fn varDeclInitializerReferencesExpectedTypeMethod(
        self: ProjectTypeResolver,
        full: std.zig.Ast.full.VarDecl,
        decl_file_index: usize,
        method_name: []const u8,
    ) bool {
        const type_node = full.ast.type_node.unwrap() orelse return false;
        const expected_type = self.resolveTypeNode(@intFromEnum(type_node)) orelse return false;
        if (expected_type.file_index != decl_file_index) return false;
        if (expected_type.container_node != null) return false;

        const init_node = full.ast.init_node.unwrap() orelse return false;
        return self.initializerReferencesExpectedTypeMethod(@intFromEnum(init_node), method_name);
    }

    pub fn resolveCallArgumentTypeNode(
        self: ProjectTypeResolver,
        parent_call: u32,
        expr_node: u32,
        parent_map: []const u32,
    ) ?u32 {
        const tree = self.currentFile().tree;
        if (tree.errors.len != 0) return null;
        const tags = tree.nodes.items(.tag);
        if (parent_call >= tags.len or !isCallNode(tags[parent_call])) return null;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(parent_call)) orelse return null;
        var argument_index: ?usize = null;
        for (call.ast.params, 0..) |param_node, index| {
            if (nodeIsAncestor(@intFromEnum(param_node), expr_node, parent_map)) {
                argument_index = index;
                break;
            }
        }
        const explicit_index = argument_index orelse return null;

        const callable = self.resolveCallableAtCall(parent_call) orelse return null;
        const parameter_index = explicit_index + callable.implicit_self_count;
        const target_tree = self.files[callable.file_index].tree;
        return protoParamTypeNode(target_tree, callable.proto_node, parameter_index);
    }

    pub fn resolveResultLocationTypeNode(self: ProjectTypeResolver, expression: u32) ?ResolvedTypeNode {
        return self.resolveExpectedTypeNode(expression, 0);
    }

    fn resolveExpectedTypeNode(self: ProjectTypeResolver, expression: u32, depth: u8) ?ResolvedTypeNode {
        if (depth >= resolution_budget_frames) {
            reportResolutionBudget("expected-type resolution", resolution_budget_frames, self.currentFile().path);
            return null;
        }
        const tree = self.currentFile().tree;
        if (tree.errors.len != 0) return null;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var node = expression;
        for (0..resolution_budget_frames) |_| {
            const parent = self.parentNode(node) orelse return null;
            switch (tags[parent]) {
                .simple_var_decl, .local_var_decl, .global_var_decl, .aligned_var_decl => {
                    const full = tree.fullVarDecl(@enumFromInt(parent)) orelse return null;
                    const init_node = full.ast.init_node.unwrap() orelse return null;
                    if (@intFromEnum(init_node) != node) return null;
                    const type_node = full.ast.type_node.unwrap() orelse return null;
                    return .{ .file_index = self.file_index, .node_index = @intFromEnum(type_node) };
                },
                .assign => {
                    const pair = datas[parent].node_and_node;
                    if (@intFromEnum(pair[1]) != node) return null;
                    return self.resolveExprTypeNode(@intFromEnum(pair[0]));
                },
                .call, .call_comma, .call_one, .call_one_comma => {
                    return self.resolveArgumentTypeAtNode(parent, node, depth + 1);
                },
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    const name = tree.tokenSlice(tree.nodeMainToken(@enumFromInt(parent)));
                    if (!std.mem.eql(u8, name, "@as")) return null;
                    var buffer: [2]std.zig.Ast.Node.Index = undefined;
                    const params = tree.builtinCallParams(&buffer, @enumFromInt(parent)) orelse return null;
                    if (params.len != 2 or @intFromEnum(params[1]) != node) return null;
                    return .{ .file_index = self.file_index, .node_index = @intFromEnum(params[0]) };
                },
                .@"return" => {
                    const token = tokenForNode(tree, parent) orelse return null;
                    const function = self.enclosingFunctionAt(token) orelse return null;
                    const proto = functionProtoNode(tree, function) orelse return null;
                    return self.callableReturnType(.{
                        .file_index = self.file_index,
                        .proto_node = proto,
                        .implicit_self_count = 0,
                    });
                },
                .grouped_expression, .@"try", .@"catch", .@"orelse" => node = parent,
                .@"if", .if_simple => {
                    const full = tree.fullIf(@enumFromInt(parent)) orelse return null;
                    if (@intFromEnum(full.ast.cond_expr) == node) return null;
                    node = parent;
                },
                else => return null,
            }
        }
        reportResolutionBudget("expected-type parent climb", resolution_budget_frames, self.currentFile().path);
        return null;
    }

    fn resolveArgumentTypeAtNode(self: ProjectTypeResolver, call_node: u32, argument: u32, depth: u8) ?ResolvedTypeNode {
        if (depth >= resolution_budget_frames) {
            reportResolutionBudget("call-argument type resolution", resolution_budget_frames, self.currentFile().path);
            return null;
        }
        const tree = self.currentFile().tree;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse return null;
        for (call.ast.params, 0..) |parameter, index| {
            if (@intFromEnum(parameter) != argument) continue;
            const callable = self.resolveCallableAtCallDepth(call_node, depth + 1) orelse return null;
            const target_tree = self.files[callable.file_index].tree;
            const type_node = protoParamTypeNode(target_tree, callable.proto_node, index + callable.implicit_self_count) orelse return null;
            return .{ .file_index = callable.file_index, .node_index = type_node };
        }
        return null;
    }

    pub fn resolveDeclarationNode(self: ProjectTypeResolver, node: usize) ?u32 {
        const tree = self.currentFile().tree;
        if (tree.errors.len != 0) return null;
        const name = import_resolver.identifierName(tree, node) orelse return null;
        return self.findNearestBinding(name, node).declaration_node;
    }

    /// Resolve a call's declaration and return-type expression without
    /// collapsing the result to a string. Callers that need type information
    /// from another source file can use the returned file index to select the
    /// matching AST.
    pub fn resolveCallReturnTypeNode(self: ProjectTypeResolver, call_node: u32) ?ResolvedTypeNode {
        const callable = self.resolveCallableAtCall(call_node) orelse return null;
        return self.callableReturnType(callable);
    }

    pub fn resolveMemberReturnTypeNode(self: ProjectTypeResolver, owner: ResolvedType, name: []const u8) ?ResolvedTypeNode {
        const proto_node = self.findMemberFunctionProto(owner, name) orelse return null;
        return self.callableReturnType(.{ .file_index = owner.file_index, .proto_node = proto_node, .implicit_self_count = 0 });
    }

    fn callableReturnType(self: ProjectTypeResolver, callable: CallableInfo) ?ResolvedTypeNode {
        const tree = self.files[callable.file_index].tree;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = switch (tree.nodes.items(.tag)[callable.proto_node]) {
            .fn_proto => tree.fnProto(@enumFromInt(callable.proto_node)),
            .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(callable.proto_node)),
            .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(callable.proto_node)),
            .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(callable.proto_node)),
            else => return null,
        };
        const return_type = proto.ast.return_type.unwrap() orelse return null;
        const first_token = tree.firstToken(return_type);
        return .{
            .file_index = callable.file_index,
            .node_index = @intFromEnum(return_type),
            .inferred_error_union = first_token > 0 and tree.tokenTag(first_token - 1) == .bang,
        };
    }

    /// Direct `@import(import_path)` binding proof; this does not follow aliases.
    pub fn isVerifiedImportBinding(
        self: ProjectTypeResolver,
        node: usize,
        import_path: []const u8,
    ) bool {
        const tree = self.currentFile().tree;
        const declaration_node = self.resolveBindingDeclaration(node) orelse return false;
        const init_node = self.varDeclInitializer(declaration_node) orelse return false;
        const declared_path = import_resolver.importPathFromBuiltinCall(tree, init_node) orelse return false;
        return std.mem.eql(u8, declared_path, import_path);
    }

    /// Verified `std.testing` namespace identity for the receiver of a
    /// reflection call. Only genuine `@import("std")` provenance counts, so a
    /// user declaration spelled like `std.testing` cannot stand in for the real
    /// namespace, while immutable aliases of the namespace stay trusted.
    pub fn isStdTestingNamespaceExpr(self: ProjectTypeResolver, node: usize) bool {
        if (self.currentFile().tree.errors.len != 0) return false;
        var visited: [resolution_budget_frames]u32 = undefined;
        return self.isStdTestingNamespaceExprVisited(node, &visited, 0);
    }

    /// Record a binding on the current walk's chain. Returns false when the
    /// walk must stop: a repeated binding is a cycle, an exhausted budget is
    /// a truncation, and only the truncation is reported.
    fn recordVisitedBinding(
        self: ProjectTypeResolver,
        visited: *[resolution_budget_frames]u32,
        depth: usize,
        declaration_node: u32,
        walk: []const u8,
    ) bool {
        return switch (pushVisitedBinding(visited, depth, declaration_node)) {
            .recorded => true,
            .repeated => false,
            .exhausted => blk: {
                reportResolutionBudget(walk, resolution_budget_frames, self.currentFile().path);
                break :blk false;
            },
        };
    }

    fn isStdTestingNamespaceExprVisited(
        self: ProjectTypeResolver,
        node: usize,
        visited: *[resolution_budget_frames]u32,
        depth: usize,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return false;
        if (depth >= visited.len) {
            reportResolutionBudget("std.testing namespace alias walk", resolution_budget_frames, self.currentFile().path);
            return false;
        }

        switch (tags[node]) {
            .field_access => {
                const access = tree.nodes.items(.data)[node].node_and_token;
                const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                if (!std.mem.eql(u8, member_name, "testing")) return false;
                return self.isVerifiedImportExprVisited(@intFromEnum(access[0]), "std", visited, depth, true);
            },
            .identifier => {
                const declaration_node = self.resolveBindingDeclaration(node) orelse return false;
                if (!self.recordVisitedBinding(visited, depth, declaration_node, "std.testing namespace alias walk")) return false;
                const init = self.constInitializer(self.file_index, declaration_node) orelse return false;
                return self.isStdTestingNamespaceExprVisited(init.node_index, visited, depth + 1);
            },
            .grouped_expression,
            .unwrap_optional,
            => return self.isStdTestingNamespaceExprVisited(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                visited,
                depth,
            ),
            else => return false,
        }
    }

    fn isVerifiedImportExprVisited(
        self: ProjectTypeResolver,
        node: usize,
        import_path: []const u8,
        visited: *[resolution_budget_frames]u32,
        depth: usize,
        comptime const_only: bool,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return false;
        if (depth >= visited.len) {
            reportResolutionBudget("verified-import alias walk", resolution_budget_frames, self.currentFile().path);
            return false;
        }

        switch (tags[node]) {
            .identifier => {
                const declaration_node = self.resolveBindingDeclaration(node) orelse return false;
                if (!self.recordVisitedBinding(visited, depth, declaration_node, "verified-import alias walk")) return false;
                const init_node = if (const_only)
                    (self.constInitializer(self.file_index, declaration_node) orelse return false).node_index
                else
                    self.varDeclInitializer(declaration_node) orelse return false;
                return self.isVerifiedImportExprVisited(init_node, import_path, visited, depth + 1, const_only);
            },
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => {
                const declared_path = import_resolver.importPathFromBuiltinCall(tree, node) orelse return false;
                return std.mem.eql(u8, declared_path, import_path);
            },
            .grouped_expression,
            .unwrap_optional,
            => return self.isVerifiedImportExprVisited(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                import_path,
                visited,
                depth,
                const_only,
            ),
            else => return false,
        }
    }

    /// Lexical binding of an identifier reference, ignoring its value.
    /// Malformed files never yield a binding, so provenance checks fail closed.
    fn resolveBindingDeclaration(self: ProjectTypeResolver, node: usize) ?u32 {
        const tree = self.currentFile().tree;
        if (tree.errors.len != 0) return null;
        const name = import_resolver.identifierName(tree, node) orelse return null;
        return self.findNearestBinding(name, node).declaration_node;
    }

    /// Initializer of the `const`/`var` binding at `declaration_node`; only
    /// those declarations can carry import provenance.
    fn varDeclInitializer(self: ProjectTypeResolver, declaration_node: u32) ?u32 {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (declaration_node >= tags.len or !import_resolver.isVarDeclTag(tags[declaration_node])) return null;
        const full = tree.fullVarDecl(@enumFromInt(declaration_node)) orelse return null;
        const init_node = full.ast.init_node.unwrap() orelse return null;
        return @intFromEnum(init_node);
    }

    /// Resolve the function a call expression reaches, across the whole
    /// project: a namespace-qualified or re-exported callee is followed to
    /// the prototype that defines it.
    ///
    /// Returns null when the callee is not a project function, when the file
    /// has parse errors, or when the binding is ambiguous; callers must read
    /// that as "unknown", never as "some other function". The prototype and
    /// the file holding it are borrowed from `self.files` and stay valid as
    /// long as the resolver's file list does.
    pub fn resolveCallableAtCall(self: ProjectTypeResolver, call_node: u32) ?CallableInfo {
        return self.resolveCallableAtCallDepth(call_node, 0);
    }

    fn resolveCallableAtCallDepth(self: ProjectTypeResolver, call_node: u32, depth: u8) ?CallableInfo {
        if (depth >= resolution_budget_frames) {
            reportResolutionBudget("callable resolution", resolution_budget_frames, self.currentFile().path);
            return null;
        }
        const tree = self.currentFile().tree;
        if (tree.errors.len != 0) return null;
        const tags = tree.nodes.items(.tag);
        if (call_node >= tags.len or !isCallNode(tags[call_node])) return null;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse return null;
        const callee = @intFromEnum(call.ast.fn_expr);
        if (callee >= tags.len) return null;

        switch (tags[callee]) {
            .identifier => {
                const name = import_resolver.identifierName(tree, callee) orelse return null;
                if (self.resolveNearestBindingType(name, callee).found) return null;
                const proto_node = self.findScopedFunctionProto(name, callee) orelse return null;
                return .{
                    .proto_node = proto_node,
                    .file_index = self.file_index,
                    .implicit_self_count = 0,
                };
            },
            .field_access => {
                const access = tree.nodes.items(.data)[callee].node_and_token;
                const receiver_node = @intFromEnum(access[0]);
                const field_token = access[1];
                if (field_token >= tree.tokens.len or tree.tokenTag(field_token) != .identifier) return null;
                const receiver_type = self.resolveExprType(receiver_node) orelse return null;
                const target_resolver = self.forFile(receiver_type.file_index);
                const method_name = import_resolver.normalizeIdentifier(tree.tokenSlice(field_token));
                const proto_node = target_resolver.findMemberFunctionProto(
                    receiver_type,
                    method_name,
                ) orelse return null;
                const implicit_self_count = if (self.isTypeNamespaceExpr(receiver_node))
                    0
                else
                    target_resolver.implicitSelfCount(proto_node, receiver_type);
                return .{
                    .proto_node = proto_node,
                    .file_index = receiver_type.file_index,
                    .implicit_self_count = implicit_self_count,
                };
            },
            .enum_literal => {
                const expected = self.resolveExpectedTypeNode(call_node, depth + 1) orelse return null;
                const owner_resolver = self.forFile(expected.file_index);
                const owner = owner_resolver.resolveTypeNode(expected.node_index) orelse return null;
                const name = import_resolver.normalizeIdentifier(tree.tokenSlice(tree.nodeMainToken(@enumFromInt(callee))));
                const proto = self.findMemberFunctionProto(owner, name) orelse return null;
                return .{ .file_index = owner.file_index, .proto_node = proto, .implicit_self_count = 0 };
            },
            else => return null,
        }
    }

    fn findScopedFunctionProto(self: ProjectTypeResolver, name: []const u8, reference_node: u32) ?u32 {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        const reference = tokenForNode(tree, reference_node) orelse return null;
        if (self.currentFile().lexical_index) |index| return index.findFunction(name, reference);
        var best: ?u32 = null;
        var best_span: u32 = std.math.maxInt(u32);
        for (tags, 0..) |tag, index| {
            if (tag != .fn_decl) continue;
            const proto = functionProtoNode(tree, @intCast(index)) orelse continue;
            const declared_name = functionProtoName(tree, proto) orelse continue;
            if (!std.mem.eql(u8, name, import_resolver.normalizeIdentifier(declared_name))) continue;
            const scope = findLexicalScope(tree, tags, tree.nodeMainToken(@enumFromInt(proto)));
            if (!scope.contains(reference)) continue;
            if (scope.span() >= best_span) continue;
            best = proto;
            best_span = scope.span();
        }
        return best;
    }

    fn findMemberFunctionProto(
        self: ProjectTypeResolver,
        base_type: ResolvedType,
        member_name: []const u8,
    ) ?u32 {
        if (self.files[base_type.file_index].tree.errors.len != 0) return null;
        if (base_type.container_node) |container_node| {
            return self.findContainerFunctionProto(
                base_type.file_index,
                container_node,
                member_name,
            );
        }
        return self.findRootFunctionProto(base_type.file_index, member_name);
    }

    fn findContainerFunctionProto(
        self: ProjectTypeResolver,
        file_index: usize,
        container_node: u32,
        member_name: []const u8,
    ) ?u32 {
        const tree = self.files[file_index].tree;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, @enumFromInt(container_node)) orelse return null;
        for (container.ast.members) |member_node| {
            const member = @intFromEnum(member_node);
            const proto_node = functionProtoNode(tree, member) orelse continue;
            const name = functionProtoName(tree, proto_node) orelse continue;
            if (std.mem.eql(u8, import_resolver.normalizeIdentifier(name), member_name)) {
                return proto_node;
            }
        }
        return null;
    }

    fn findRootFunctionProto(self: ProjectTypeResolver, file_index: usize, name: []const u8) ?u32 {
        const tree = self.files[file_index].tree;
        for (tree.rootDecls()) |decl_node| {
            const proto_node = functionProtoNode(tree, @intFromEnum(decl_node)) orelse continue;
            const candidate_name = functionProtoName(tree, proto_node) orelse continue;
            if (std.mem.eql(u8, import_resolver.normalizeIdentifier(candidate_name), name)) {
                return proto_node;
            }
        }
        return null;
    }

    /// How many leading prototype parameters an instance call leaves unwritten.
    ///
    /// A receiver written `anytype` or `...` names no type to compare against,
    /// so the slot cannot be matched by type and the receiver is recognised by
    /// being first instead. A first parameter that does declare a type still
    /// has to resolve to the receiver: an ordinary unknown typed first
    /// parameter is not evidence of one.
    ///
    /// A call written through a type namespace never reaches here, so a static
    /// function keeps an offset of zero even with an `anytype` first parameter.
    fn implicitSelfCount(self: ProjectTypeResolver, proto_node: u32, receiver_type: ResolvedType) usize {
        const tree = self.currentFile().tree;
        if (protoFirstParamIsInferred(tree, proto_node)) return 1;
        const type_node = protoParamTypeNode(tree, proto_node, 0) orelse return 0;
        const parameter_type = self.resolveTypeNode(type_node) orelse return 0;
        return if (resolvedTypesEqual(parameter_type, receiver_type)) 1 else 0;
    }

    fn resolveNameType(self: ProjectTypeResolver, name: []const u8, reference_node: usize) ?ResolvedType {
        const binding = self.resolveNearestBindingType(name, reference_node);
        if (binding.found) return binding.resolved;
        if (self.resolveNamedDeclType(self.file_index, name)) |resolved| return resolved;
        return null;
    }

    fn resolveNearestBindingType(
        self: ProjectTypeResolver,
        name: []const u8,
        reference_node: usize,
    ) BindingResolution {
        var frame: BindingFrame = undefined;
        // Keep "found" on a cycle so callers do not retry through root lookup.
        const resolver = self.enterBinding(name, reference_node, &frame) orelse return .{ .found = true };
        var binding = resolver.findNearestBinding(name, reference_node);
        const declaration_node = binding.declaration_node orelse return binding;
        const full = self.currentFile().tree.fullVarDecl(@enumFromInt(declaration_node)) orelse return binding;
        binding.resolved = resolver.resolveVarDeclType(full, declaration_node, name);
        binding.is_type_namespace = resolver.varDeclIsTypeNamespace(full);
        return binding;
    }

    fn findNearestBinding(
        self: ProjectTypeResolver,
        name: []const u8,
        reference_node: usize,
    ) BindingResolution {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        const reference_token = tokenForNode(tree, reference_node) orelse return .{};
        if (self.currentFile().lexical_index) |index| {
            const candidate = index.findBinding(name, reference_token) orelse return .{};
            if (candidate.kind == .variable) return .{ .found = true, .declaration_node = candidate.node };
            const type_node = parameterTypeNode(tree, tags, candidate.node) orelse return .{};
            return .{
                .found = true,
                .declaration_node = candidate.node,
                .resolved = if (tree.fullVarDecl(@enumFromInt(candidate.node))) |full|
                    self.resolveVarDeclType(full, candidate.node, name)
                else
                    self.resolveTypeNode(type_node),
                .is_type_namespace = isTypeKeywordNode(tree, tags, type_node),
            };
        }
        const reference_function = findEnclosingFunction(tree, tags, reference_token);
        var best: ?BindingCandidate = null;

        for (tags, 0..) |tag, node_index| {
            if (!import_resolver.isVarDeclTag(tag)) continue;
            const full = tree.fullVarDecl(@enumFromInt(node_index)) orelse continue;
            const name_token = full.ast.mut_token + 1;
            if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
            const declaration_name = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token));
            if (!std.mem.eql(u8, declaration_name, name)) continue;

            const is_root = isRootDeclNode(tree, node_index);
            if (!is_root and name_token > reference_token) continue;

            const declaration_function = findEnclosingFunction(tree, tags, name_token);
            if (declaration_function) |function_node| {
                if (reference_function == null or function_node != reference_function.?) continue;
            }

            const scope = if (is_root)
                rootScope(tree)
            else
                findLexicalScope(tree, tags, name_token);
            if (!is_root and !scope.contains(reference_token)) continue;

            const candidate = BindingCandidate{
                .scope = scope,
                .name_token = name_token,
                .resolution = .{
                    .found = true,
                    .declaration_node = @intCast(node_index),
                },
            };
            if (isBetterBinding(candidate, best)) best = candidate;
        }

        for (tags, 0..) |tag, node_index| {
            const proto_node = switch (tag) {
                .fn_decl => @intFromEnum(tree.nodes.items(.data)[node_index].node_and_node[0]),
                .fn_proto,
                .fn_proto_simple,
                .fn_proto_one,
                .fn_proto_multi,
                => @as(u32, @intCast(node_index)),
                else => continue,
            };
            const function_scope = nodeTokenRange(tree, @intCast(node_index)) orelse continue;
            if (!function_scope.contains(reference_token)) continue;
            if (tag == .fn_decl) {
                if (reference_function == null or reference_function.? != @as(u32, @intCast(node_index))) continue;
            }
            self.considerFunctionParameters(proto_node, name, reference_token, function_scope, &best);
        }
        return if (best) |candidate| candidate.resolution else .{};
    }

    const BindingCandidate = struct {
        scope: ScopeRange,
        name_token: u32,
        resolution: BindingResolution,
    };

    fn isBetterBinding(candidate: BindingCandidate, current: ?BindingCandidate) bool {
        const previous = current orelse return true;
        if (candidate.scope.span() < previous.scope.span()) return true;
        if (candidate.scope.span() > previous.scope.span()) return false;
        return candidate.name_token > previous.name_token;
    }

    fn varDeclIsTypeNamespace(
        self: ProjectTypeResolver,
        full: std.zig.Ast.full.VarDecl,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (full.ast.type_node.unwrap()) |type_node| {
            return isTypeKeywordNode(tree, tags, @intFromEnum(type_node));
        }
        const init_node = full.ast.init_node.unwrap() orelse return false;
        const init_index = @intFromEnum(init_node);
        if (init_index >= tags.len) return false;
        return switch (tags[init_index]) {
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
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => isTypeNamespaceBuiltin(tree, tags, init_index),
            .identifier, .field_access => self.isTypeNamespaceExpr(init_index),
            else => false,
        };
    }

    fn isTypeNamespaceExpr(self: ProjectTypeResolver, node: usize) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return false;
        return switch (tags[node]) {
            .identifier => blk: {
                const name = import_resolver.identifierName(tree, node) orelse break :blk false;
                const binding = self.resolveNearestBindingType(name, node);
                break :blk binding.found and binding.is_type_namespace;
            },
            .field_access => self.isTypeNamespaceExpr(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
            ),
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => isTypeNamespaceBuiltin(tree, tags, node),
            else => false,
        };
    }

    fn considerFunctionParameters(
        self: ProjectTypeResolver,
        proto_node: u32,
        name: []const u8,
        reference_token: u32,
        function_scope: ScopeRange,
        best: *?BindingCandidate,
    ) void {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (proto_node >= tags.len) return;

        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        switch (tags[proto_node]) {
            .fn_proto => self.considerParameterList(
                tree.fnProto(@enumFromInt(proto_node)).ast.params,
                name,
                reference_token,
                function_scope,
                best,
            ),
            .fn_proto_simple => self.considerParameterList(
                tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)).ast.params,
                name,
                reference_token,
                function_scope,
                best,
            ),
            .fn_proto_one => self.considerParameterList(
                tree.fnProtoOne(&buffer, @enumFromInt(proto_node)).ast.params,
                name,
                reference_token,
                function_scope,
                best,
            ),
            .fn_proto_multi => self.considerParameterList(
                tree.fnProtoMulti(@enumFromInt(proto_node)).ast.params,
                name,
                reference_token,
                function_scope,
                best,
            ),
            else => {},
        }
    }

    fn considerParameterList(
        self: ProjectTypeResolver,
        params: []const std.zig.Ast.Node.Index,
        name: []const u8,
        reference_token: u32,
        function_scope: ScopeRange,
        best: *?BindingCandidate,
    ) void {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        for (params) |param_node| {
            const parameter_index = @intFromEnum(param_node);
            if (parameter_index >= tags.len) continue;
            const name_token = parameterNameToken(tree, tags, parameter_index) orelse continue;
            if (name_token >= tree.tokens.len) continue;
            if (!std.mem.eql(
                u8,
                import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)),
                name,
            )) continue;
            if (name_token > reference_token) continue;

            const parameter_type = parameterTypeNode(tree, tags, parameter_index) orelse continue;
            const parameter_resolution = if (import_resolver.isVarDeclTag(tags[parameter_index]))
                self.resolveVarDeclType(
                    tree.fullVarDecl(param_node) orelse continue,
                    parameter_index,
                    name,
                )
            else
                self.resolveTypeNode(parameter_type);

            const candidate = BindingCandidate{
                .scope = function_scope,
                .name_token = name_token,
                .resolution = .{
                    .found = true,
                    .resolved = parameter_resolution,
                    .declaration_node = @intCast(parameter_index),
                    .is_type_namespace = isTypeKeywordNode(tree, tags, parameter_type),
                },
            };
            if (isBetterBinding(candidate, best.*)) best.* = candidate;
        }
    }

    fn tokenForNode(tree: *const std.zig.Ast, node: usize) ?u32 {
        const main_tokens = tree.nodes.items(.main_token);
        if (node >= main_tokens.len) return null;
        const token = main_tokens[node];
        if (token >= tree.tokens.len) return null;
        return token;
    }

    fn rootScope(tree: *const std.zig.Ast) ScopeRange {
        return .{
            .first_token = 0,
            .last_token = if (tree.tokens.len == 0) 0 else @intCast(tree.tokens.len - 1),
        };
    }

    fn nodeTokenRange(tree: *const std.zig.Ast, node: u32) ?ScopeRange {
        if (node == 0 or node >= tree.nodes.len or tree.tokens.len == 0) return null;
        const first_token = tree.firstToken(@enumFromInt(node));
        const last_token = tree.lastToken(@enumFromInt(node));
        if (first_token > last_token or last_token >= tree.tokens.len) return null;
        return .{
            .first_token = first_token,
            .last_token = last_token,
        };
    }

    fn findEnclosingFunction(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        token: u32,
    ) ?u32 {
        var best: ?u32 = null;
        var best_span: u32 = std.math.maxInt(u32);
        for (tags, 0..) |tag, node_index| {
            if (tag != .fn_decl) continue;
            const scope = nodeTokenRange(tree, @intCast(node_index)) orelse continue;
            if (!scope.contains(token)) continue;
            if (scope.span() < best_span) {
                best = @intCast(node_index);
                best_span = scope.span();
            }
        }
        return best;
    }

    fn findLexicalScope(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        token: u32,
    ) ScopeRange {
        var best: ?ScopeRange = null;
        for (tags, 0..) |tag, node_index| {
            if (!isBlockTag(tag) and !isContainerTag(tag)) continue;
            const scope = nodeTokenRange(tree, @intCast(node_index)) orelse continue;
            if (!scope.contains(token)) continue;
            if (best == null or scope.span() < best.?.span()) best = scope;
        }
        return best orelse rootScope(tree);
    }

    fn isBlockTag(tag: std.zig.Ast.Node.Tag) bool {
        return switch (tag) {
            .block,
            .block_semicolon,
            .block_two,
            .block_two_semicolon,
            => true,
            else => false,
        };
    }

    fn parameterNameToken(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        node: usize,
    ) ?u32 {
        if (node >= tags.len) return null;
        if (import_resolver.isVarDeclTag(tags[node])) {
            const full = tree.fullVarDecl(@enumFromInt(node)) orelse return null;
            const name_token = full.ast.mut_token + 1;
            if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
            return name_token;
        }
        const name_token = import_resolver.paramNameTokenBeforeType(tree, node) orelse return null;
        return @intCast(name_token);
    }

    fn parameterTypeNode(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        node: usize,
    ) ?u32 {
        if (node >= tags.len) return null;
        if (import_resolver.isVarDeclTag(tags[node])) {
            const full = tree.fullVarDecl(@enumFromInt(node)) orelse return null;
            return @intFromEnum(full.ast.type_node.unwrap() orelse return null);
        }
        return @intCast(node);
    }

    fn isTypeKeywordNode(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        node: u32,
    ) bool {
        if (node >= tags.len or tags[node] != .identifier) return false;
        const token = tree.nodes.items(.main_token)[node];
        if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return false;
        return std.mem.eql(u8, tree.tokenSlice(token), "type");
    }

    fn isTypeNamespaceBuiltin(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        node: usize,
    ) bool {
        if (node >= tags.len or !import_resolver.isBuiltinCallTag(tags[node])) return false;
        const token = tree.nodes.items(.main_token)[node];
        if (token >= tree.tokens.len or tree.tokenTag(token) != .builtin) return false;
        const name = tree.tokenSlice(token);
        return std.mem.eql(u8, name, "@This") or
            std.mem.eql(u8, name, "@Type") or
            std.mem.eql(u8, name, "@OpaqueType") or
            std.mem.eql(u8, name, "@Vector") or
            std.mem.eql(u8, name, "@Struct") or
            std.mem.eql(u8, name, "@Enum") or
            std.mem.eql(u8, name, "@Union") or
            std.mem.eql(u8, name, "@import");
    }

    fn resolveVarDeclType(
        self: ProjectTypeResolver,
        full: std.zig.Ast.full.VarDecl,
        node_index: usize,
        decl_name: []const u8,
    ) ?ResolvedType {
        var frame: BindingFrame = undefined;
        const resolver = self.enterBinding(decl_name, node_index, &frame) orelse return null;
        if (full.ast.type_node.unwrap()) |type_node| {
            if (resolver.resolveTypeNode(@intFromEnum(type_node))) |resolved| return resolved;
        }

        const init_node = full.ast.init_node.unwrap() orelse return null;
        const init_index = @intFromEnum(init_node);
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (init_index >= tags.len) return null;
        if (import_resolver.isBuiltinCallTag(tags[init_index])) {
            return resolver.resolveBuiltinType(@intCast(init_index));
        }
        if (isContainerTag(tags[init_index])) {
            return .{ .file_index = self.file_index, .type_name = decl_name, .container_node = @intCast(init_index) };
        }
        if (self.isRootDeclaration(node_index) and !resolver.varDeclIsTypeNamespace(full)) return null;
        return resolver.resolveInitializerType(init_index);
    }

    fn resolveInitializerType(self: ProjectTypeResolver, node: usize) ?ResolvedType {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;

        return switch (tags[node]) {
            .identifier, .field_access => self.resolveExprType(node),
            .call, .call_comma, .call_one, .call_one_comma => self.resolveCallType(@intCast(node)),
            .@"try",
            .address_of,
            .deref,
            .optional_type,
            => self.resolveInitializerType(@intFromEnum(tree.nodes.items(.data)[node].node)),
            .grouped_expression,
            .unwrap_optional,
            => self.resolveInitializerType(@intFromEnum(tree.nodes.items(.data)[node].node_and_token[0])),
            .struct_init,
            .struct_init_comma,
            .struct_init_one,
            .struct_init_one_comma,
            .struct_init_dot,
            .struct_init_dot_comma,
            .struct_init_dot_two,
            .struct_init_dot_two_comma,
            => self.resolveStructInitType(@intCast(node)),
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => self.resolveBuiltinType(@intCast(node)),
            else => null,
        };
    }

    fn initializerReferencesExpectedTypeMethod(
        self: ProjectTypeResolver,
        node: usize,
        method_name: []const u8,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return false;

        return switch (tags[node]) {
            .call,
            .call_comma,
            .call_one,
            .call_one_comma,
            => self.callUsesImplicitResultMethod(@intCast(node), method_name),
            .@"try",
            .address_of,
            .deref,
            .optional_type,
            => self.initializerReferencesExpectedTypeMethod(@intFromEnum(tree.nodes.items(.data)[node].node), method_name),
            .grouped_expression,
            .unwrap_optional,
            => self.initializerReferencesExpectedTypeMethod(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                method_name,
            ),
            .@"catch" => self.initializerReferencesExpectedTypeMethod(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]),
                method_name,
            ),
            else => false,
        };
    }

    fn callUsesImplicitResultMethod(self: ProjectTypeResolver, node: u32, method_name: []const u8) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return false;

        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return false;
        const callee = @intFromEnum(call.ast.fn_expr);
        if (callee >= tags.len or tags[callee] != .enum_literal) return false;

        const token = tree.nodes.items(.main_token)[callee];
        if (token >= tree.tokens.len) return false;
        return std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(token)), method_name);
    }

    fn resolveCallType(self: ProjectTypeResolver, node: u32) ?ResolvedType {
        if (self.resolveCallReturnTypeNode(node)) |return_type| {
            const return_resolver = self.forFile(return_type.file_index);
            if (return_resolver.resolveTypeNode(return_type.node_index)) |resolved| {
                return resolved;
            }
        }

        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;

        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return null;
        const callee = @intFromEnum(call.ast.fn_expr);
        if (callee >= tags.len or tags[callee] != .field_access) return null;

        if (self.resolveAllocatorCreateType(node, callee)) |created_type| {
            return created_type;
        }

        return null;
    }

    fn resolveAllocatorCreateType(self: ProjectTypeResolver, call_node: u32, callee_node: u32) ?ResolvedType {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        const access = tree.nodes.items(.data)[callee_node].node_and_token;
        const method_name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
        if (!std.mem.eql(u8, method_name, "create")) return null;

        const receiver_node = @intFromEnum(access[0]);
        if (!self.isStdAllocatorExpr(receiver_node)) return null;

        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse return null;
        if (call.ast.params.len != 1) return null;
        const type_node = @intFromEnum(call.ast.params[0]);
        if (type_node >= tags.len) return null;
        return self.resolveTypeNode(type_node);
    }

    fn isStdAllocatorExpr(self: ProjectTypeResolver, node: usize) bool {
        var visited: [resolution_budget_frames]u32 = undefined;
        return self.isStdAllocatorExprVisited(node, &visited, 0);
    }

    fn isStdAllocatorExprVisited(
        self: ProjectTypeResolver,
        node: usize,
        visited: *[resolution_budget_frames]u32,
        depth: usize,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return false;
        if (depth >= visited.len) {
            reportResolutionBudget("std.mem.Allocator expression walk", resolution_budget_frames, self.currentFile().path);
            return false;
        }

        switch (tags[node]) {
            .field_access => {
                const access = tree.nodes.items(.data)[node].node_and_token;
                const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                if (!std.mem.eql(u8, member_name, "Allocator")) return false;
                return self.isStdMemExprVisited(@intFromEnum(access[0]), visited, depth);
            },
            .identifier => {
                const declaration_node = self.resolveBindingDeclaration(node) orelse return false;
                return self.isStdAllocatorBinding(declaration_node, visited, depth);
            },
            .grouped_expression,
            .unwrap_optional,
            => return self.isStdAllocatorExprVisited(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                visited,
                depth,
            ),
            .@"try",
            .address_of,
            .deref,
            .optional_type,
            => return self.isStdAllocatorExprVisited(
                @intFromEnum(tree.nodes.items(.data)[node].node),
                visited,
                depth,
            ),
            .ptr_type,
            .ptr_type_aligned,
            .ptr_type_bit_range,
            .ptr_type_sentinel,
            => {
                const ptr = tree.fullPtrType(@enumFromInt(node)) orelse return false;
                return self.isStdAllocatorExprVisited(@intFromEnum(ptr.ast.child_type), visited, depth);
            },
            else => return false,
        }
    }

    fn isStdAllocatorBinding(
        self: ProjectTypeResolver,
        declaration_node: u32,
        visited: *[resolution_budget_frames]u32,
        depth: usize,
    ) bool {
        if (!self.recordVisitedBinding(visited, depth, declaration_node, "std.mem.Allocator binding walk")) return false;

        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (declaration_node >= tags.len) return false;
        if (!import_resolver.isVarDeclTag(tags[declaration_node])) {
            const type_node = parameterTypeNode(tree, tags, declaration_node) orelse return false;
            return self.isStdAllocatorExprVisited(type_node, visited, depth + 1);
        }
        const full = tree.fullVarDecl(@enumFromInt(declaration_node)) orelse return false;
        if (full.ast.type_node.unwrap()) |type_node| {
            if (self.isStdAllocatorExprVisited(@intFromEnum(type_node), visited, depth + 1)) return true;
        }
        if (full.ast.init_node.unwrap()) |init_node| {
            if (self.isStdAllocatorExprVisited(@intFromEnum(init_node), visited, depth + 1)) return true;
        }
        return false;
    }

    fn isStdMemExprVisited(
        self: ProjectTypeResolver,
        node: usize,
        visited: *[resolution_budget_frames]u32,
        depth: usize,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return false;
        if (depth >= visited.len) {
            reportResolutionBudget("std.mem namespace walk", resolution_budget_frames, self.currentFile().path);
            return false;
        }

        switch (tags[node]) {
            .field_access => {
                const access = tree.nodes.items(.data)[node].node_and_token;
                const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                if (!std.mem.eql(u8, member_name, "mem")) return false;
                return self.isVerifiedImportExprVisited(@intFromEnum(access[0]), "std", visited, depth, false);
            },
            .identifier => {
                const declaration_node = self.resolveBindingDeclaration(node) orelse return false;
                return self.isStdMemBinding(declaration_node, visited, depth);
            },
            else => return false,
        }
    }

    fn isStdMemBinding(
        self: ProjectTypeResolver,
        declaration_node: u32,
        visited: *[resolution_budget_frames]u32,
        depth: usize,
    ) bool {
        if (!self.recordVisitedBinding(visited, depth, declaration_node, "std.mem binding walk")) return false;

        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (declaration_node >= tags.len) return false;
        if (!import_resolver.isVarDeclTag(tags[declaration_node])) {
            const type_node = parameterTypeNode(tree, tags, declaration_node) orelse return false;
            return self.isStdMemExprVisited(type_node, visited, depth + 1);
        }
        const full = tree.fullVarDecl(@enumFromInt(declaration_node)) orelse return false;
        if (full.ast.type_node.unwrap()) |type_node| {
            if (self.isStdMemExprVisited(@intFromEnum(type_node), visited, depth + 1)) return true;
        }
        if (full.ast.init_node.unwrap()) |init_node| {
            if (self.isStdMemExprVisited(@intFromEnum(init_node), visited, depth + 1)) return true;
        }
        return false;
    }

    fn resolveArrayAccessType(self: ProjectTypeResolver, node: u32) ?ResolvedType {
        const pair = self.currentFile().tree.nodes.items(.data)[node].node_and_node;
        const base_node = @intFromEnum(pair[0]);
        const type_node = self.resolveExprTypeNode(base_node) orelse return null;
        const resolver = self.forFile(type_node.file_index);
        return resolver.resolveTypeNode(type_node.node_index);
    }

    fn resolveExprTypeNode(self: ProjectTypeResolver, node: usize) ?ResolvedTypeNode {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;

        switch (tags[node]) {
            .identifier => {
                const name = import_resolver.identifierName(tree, node) orelse return null;
                const declaration_node = self.findNearestBinding(name, node).declaration_node orelse return null;
                if (declaration_node >= tags.len) return null;
                if (!import_resolver.isVarDeclTag(tags[declaration_node])) {
                    const type_node = parameterTypeNode(tree, tags, declaration_node) orelse return null;
                    return .{ .file_index = self.file_index, .node_index = type_node };
                }
                const full = tree.fullVarDecl(@enumFromInt(declaration_node)) orelse return null;
                if (full.ast.type_node.unwrap()) |type_node| {
                    return .{ .file_index = self.file_index, .node_index = @intFromEnum(type_node) };
                }
                const init_node = full.ast.init_node.unwrap() orelse return null;
                return self.resolveInitializerResultTypeNode(@intFromEnum(init_node));
            },
            .field_access => {
                const access = tree.nodes.items(.data)[node].node_and_token;
                const base_type = self.resolveExprType(@intFromEnum(access[0])) orelse return null;
                const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                return self.resolveFieldTypeNode(base_type, member_name);
            },
            .array_access => {
                const pair = tree.nodes.items(.data)[node].node_and_node;
                const base_type = self.resolveExprTypeNode(@intFromEnum(pair[0])) orelse return null;
                const base_resolver = self.forFile(base_type.file_index);
                var visited: [resolution_budget_frames]u32 = undefined;
                return base_resolver.resolveArrayElementTypeNode(base_type.node_index, &visited, 0);
            },
            .call,
            .call_comma,
            .call_one,
            .call_one_comma,
            => {
                const return_type = self.resolveCallReturnTypeNode(@intCast(node)) orelse return null;
                return .{
                    .file_index = return_type.file_index,
                    .node_index = return_type.node_index,
                };
            },
            .@"try",
            .address_of,
            .deref,
            .optional_type,
            => return self.resolveExprTypeNode(@intFromEnum(tree.nodes.items(.data)[node].node)),
            .grouped_expression,
            .unwrap_optional,
            => return self.resolveExprTypeNode(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
            ),
            .@"catch" => return self.resolveExprTypeNode(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]),
            ),
            .struct_init,
            .struct_init_comma,
            .struct_init_one,
            .struct_init_one_comma,
            .struct_init_dot,
            .struct_init_dot_comma,
            .struct_init_dot_two,
            .struct_init_dot_two_comma,
            => {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const init = tree.fullStructInit(&buffer, @enumFromInt(node)) orelse return null;
                const type_node = init.ast.type_expr.unwrap() orelse return null;
                return .{ .file_index = self.file_index, .node_index = @intFromEnum(type_node) };
            },
            .array_init,
            .array_init_comma,
            .array_init_one,
            .array_init_one_comma,
            .array_init_dot,
            .array_init_dot_comma,
            .array_init_dot_two,
            .array_init_dot_two_comma,
            => {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const init = tree.fullArrayInit(&buffer, @enumFromInt(node)) orelse return null;
                const type_node = init.ast.type_expr.unwrap() orelse return null;
                return .{ .file_index = self.file_index, .node_index = @intFromEnum(type_node) };
            },
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => return .{ .file_index = self.file_index, .node_index = @intCast(node) },
            else => return null,
        }
    }

    fn resolveInitializerResultTypeNode(self: ProjectTypeResolver, node: usize) ?ResolvedTypeNode {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;

        return switch (tags[node]) {
            .identifier,
            .field_access,
            .array_access,
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
            => self.resolveExprTypeNode(node),
            .@"try",
            .address_of,
            .deref,
            .optional_type,
            => self.resolveInitializerResultTypeNode(@intFromEnum(tree.nodes.items(.data)[node].node)),
            .slice,
            .slice_open,
            .slice_sentinel,
            .array_type,
            .array_type_sentinel,
            .ptr_type,
            .ptr_type_aligned,
            .ptr_type_bit_range,
            .ptr_type_sentinel,
            => .{ .file_index = self.file_index, .node_index = @intCast(node) },
            .@"catch" => self.resolveInitializerResultTypeNode(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]),
            ),
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => .{ .file_index = self.file_index, .node_index = @intCast(node) },
            else => null,
        };
    }

    fn resolveArrayElementTypeNode(
        self: ProjectTypeResolver,
        node: usize,
        visited: *[resolution_budget_frames]u32,
        depth: usize,
    ) ?ResolvedTypeNode {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;
        if (depth >= visited.len) {
            reportResolutionBudget("array element type walk", resolution_budget_frames, self.currentFile().path);
            return null;
        }

        switch (tags[node]) {
            .slice,
            .slice_open,
            .slice_sentinel,
            => {
                const slice = tree.fullSlice(@enumFromInt(node)) orelse return null;
                const element = @intFromEnum(slice.ast.sliced);
                if (element == 0) return null;
                return .{ .file_index = self.file_index, .node_index = element };
            },
            .array_type,
            .array_type_sentinel,
            => {
                const array = tree.fullArrayType(@enumFromInt(node)) orelse return null;
                return .{
                    .file_index = self.file_index,
                    .node_index = @intFromEnum(array.ast.elem_type),
                };
            },
            .ptr_type,
            .ptr_type_aligned,
            .ptr_type_bit_range,
            .ptr_type_sentinel,
            => {
                const ptr = tree.fullPtrType(@enumFromInt(node)) orelse return null;
                return self.resolveArrayElementTypeNode(@intFromEnum(ptr.ast.child_type), visited, depth);
            },
            .optional_type => return self.resolveArrayElementTypeNode(
                @intFromEnum(tree.nodes.items(.data)[node].node),
                visited,
                depth,
            ),
            .error_union => return self.resolveArrayElementTypeNode(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_node[1]),
                visited,
                depth,
            ),
            .grouped_expression,
            .unwrap_optional,
            => return self.resolveArrayElementTypeNode(
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                visited,
                depth,
            ),
            .identifier => {
                const name = import_resolver.identifierName(tree, node) orelse return null;
                const declaration_node = self.findNearestBinding(name, node).declaration_node orelse return null;
                if (declaration_node >= tags.len) return null;
                if (std.mem.indexOfScalar(u32, visited[0..depth], declaration_node) != null) return null;
                visited[depth] = declaration_node;
                if (!import_resolver.isVarDeclTag(tags[declaration_node])) return null;
                const full = tree.fullVarDecl(@enumFromInt(declaration_node)) orelse return null;
                if (full.ast.type_node.unwrap()) |type_node| {
                    return self.resolveArrayElementTypeNode(
                        @intFromEnum(type_node),
                        visited,
                        depth + 1,
                    );
                }
                const init_node = full.ast.init_node.unwrap() orelse return null;
                const init_type = self.resolveInitializerResultTypeNode(@intFromEnum(init_node)) orelse return null;
                const init_resolver = self.forFile(init_type.file_index);
                return init_resolver.resolveArrayElementTypeNode(init_type.node_index, visited, depth + 1);
            },
            .field_access => {
                const type_ref = self.resolveExprTypeNode(node) orelse return null;
                const type_resolver = self.forFile(type_ref.file_index);
                return type_resolver.resolveArrayElementTypeNode(type_ref.node_index, visited, depth + 1);
            },
            else => return null,
        }
    }

    pub fn resolveFieldTypeNode(self: ProjectTypeResolver, base_type: ResolvedType, field_name: []const u8) ?ResolvedTypeNode {
        if (self.files[base_type.file_index].tree.errors.len != 0) return null;
        const target = self.forFile(base_type.file_index);
        if (base_type.container_node) |container_node| {
            return target.resolveContainerFieldTypeNode(
                base_type.file_index,
                container_node,
                field_name,
            );
        }
        return target.resolveRootFieldTypeNode(base_type.file_index, field_name);
    }

    fn resolveRootFieldTypeNode(self: ProjectTypeResolver, file_index: usize, field_name: []const u8) ?ResolvedTypeNode {
        const tree = self.files[file_index].tree;
        const tags = tree.nodes.items(.tag);
        const target = self.forFile(file_index);
        for (tree.rootDecls()) |decl_node| {
            const node = @intFromEnum(decl_node);
            if (node >= tags.len) continue;
            switch (tags[node]) {
                .container_field,
                .container_field_init,
                .container_field_align,
                => if (target.resolveContainerFieldNodeTypeNode(file_index, @intCast(node), field_name)) |resolved| return resolved,
                else => {},
            }
        }
        return null;
    }

    fn resolveContainerFieldTypeNode(
        self: ProjectTypeResolver,
        file_index: usize,
        container_node: u32,
        field_name: []const u8,
    ) ?ResolvedTypeNode {
        const tree = self.files[file_index].tree;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, @enumFromInt(container_node)) orelse return null;
        for (container.ast.members) |member_node| {
            if (self.resolveContainerFieldNodeTypeNode(
                file_index,
                @intCast(@intFromEnum(member_node)),
                field_name,
            )) |resolved| return resolved;
        }
        return null;
    }

    fn resolveContainerFieldNodeTypeNode(
        self: ProjectTypeResolver,
        file_index: usize,
        node: u32,
        field_name: []const u8,
    ) ?ResolvedTypeNode {
        const tree = self.files[file_index].tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;

        if (import_resolver.isVarDeclTag(tags[node])) {
            const full = tree.fullVarDecl(@enumFromInt(node)) orelse return null;
            const name_token = full.ast.mut_token + 1;
            if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
            if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), field_name)) return null;
            if (full.ast.type_node.unwrap()) |type_node| {
                return .{ .file_index = file_index, .node_index = @intFromEnum(type_node) };
            }
            const init_node = full.ast.init_node.unwrap() orelse return null;
            return self.resolveInitializerResultTypeNode(@intFromEnum(init_node));
        }

        const field = tree.fullContainerField(@enumFromInt(node)) orelse return null;
        if (field.ast.tuple_like) return null;
        const name_token = field.ast.main_token;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
        if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), field_name)) return null;
        if (field.ast.type_expr.unwrap()) |type_node| {
            return .{ .file_index = file_index, .node_index = @intFromEnum(type_node) };
        }
        const value_node = field.ast.value_expr.unwrap() orelse return null;
        return self.resolveInitializerResultTypeNode(@intFromEnum(value_node));
    }

    fn resolveStructInitType(self: ProjectTypeResolver, node: u32) ?ResolvedType {
        const tree = self.currentFile().tree;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        const init = tree.fullStructInit(&buffer, @enumFromInt(node)) orelse return null;
        const type_node = init.ast.type_expr.unwrap() orelse return null;
        return self.resolveTypeNode(@intFromEnum(type_node));
    }

    fn resolveBuiltinType(self: ProjectTypeResolver, node: u32) ?ResolvedType {
        const tree = self.currentFile().tree;
        if (import_resolver.importPathFromBuiltinCall(tree, node)) |import_path| {
            if (import_resolver.resolveImportToFileIndex(self.files, self.currentFile().path, import_path)) |file_index| {
                if (self.files[file_index].tree.errors.len != 0) return null;
                return .{ .file_index = file_index };
            }
        }
        if (isThisBuiltinCall(tree, node)) {
            const reference = tree.nodeMainToken(@enumFromInt(node));
            const tags = tree.nodes.items(.tag);
            if (self.currentFile().lexical_index) |index| {
                if (index.smallestEnclosingContainer(tags, reference)) |container| {
                    return .{ .file_index = self.file_index, .container_node = container };
                }
            }
            // No index, or none that names a container: the scan decides, so the
            // root namespace and an inert index keep the unindexed answer.
            return .{
                .file_index = self.file_index,
                .container_node = smallestContainingContainer(tree, tags, reference),
            };
        }
        return null;
    }

    fn resolveMemberType(self: ProjectTypeResolver, base_type: ResolvedType, member_name: []const u8) ?ResolvedType {
        if (self.files[base_type.file_index].tree.errors.len != 0) return null;
        const member_resolver = self.forFile(base_type.file_index);
        if (base_type.container_node) |container_node| {
            return member_resolver.resolveContainerFieldType(
                base_type.file_index,
                container_node,
                member_name,
            );
        }
        if (member_resolver.resolveNamedDeclType(base_type.file_index, member_name)) |resolved| {
            return resolved;
        }
        return member_resolver.resolveRootFieldType(base_type.file_index, member_name);
    }

    fn resolveNamedDeclType(self: ProjectTypeResolver, file_index: usize, name: []const u8) ?ResolvedType {
        const file = self.files[file_index];
        const tree = file.tree;
        const tags = tree.nodes.items(.tag);
        if (file.lexical_index) |index| {
            const resolver = self.forFile(file_index);
            for (index.namedCandidates(name)) |candidate| {
                if (candidate.kind != .variable or !candidate.is_root) continue;
                const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse continue;
                if (resolver.resolveVarDeclType(full, candidate.node, candidate.name)) |resolved| return resolved;
            }
            return null;
        }

        for (tree.rootDecls()) |decl_idx| {
            const node_index = @intFromEnum(decl_idx);
            if (node_index >= tags.len or !import_resolver.isVarDeclTag(tags[node_index])) continue;
            const full = tree.fullVarDecl(decl_idx) orelse continue;
            const name_token = full.ast.mut_token + 1;
            if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
            const decl_name = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token));
            if (!std.mem.eql(u8, decl_name, name)) continue;

            const nested_resolver = self.forFile(file_index);
            if (nested_resolver.resolveVarDeclType(full, node_index, decl_name)) |resolved| return resolved;
        }
        return null;
    }

    fn resolveRootFieldType(self: ProjectTypeResolver, file_index: usize, field_name: []const u8) ?ResolvedType {
        const file = self.files[file_index];
        const tree = file.tree;
        const tags = tree.nodes.items(.tag);

        for (tree.rootDecls()) |decl_idx| {
            const node_index = @intFromEnum(decl_idx);
            if (node_index >= tags.len) continue;
            switch (tags[node_index]) {
                .container_field,
                .container_field_init,
                .container_field_align,
                => if (self.resolveContainerFieldNodeType(file_index, @intCast(node_index), field_name)) |resolved| return resolved,
                else => {},
            }
        }
        return null;
    }

    fn resolveContainerFieldType(self: ProjectTypeResolver, file_index: usize, container_node: u32, field_name: []const u8) ?ResolvedType {
        const file = self.files[file_index];
        const tree = file.tree;

        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        const container = tree.fullContainerDecl(&buffer, @enumFromInt(container_node)) orelse return null;
        for (container.ast.members) |member_node| {
            const member = @intFromEnum(member_node);
            if (self.resolveContainerFieldNodeType(file_index, @intCast(member), field_name)) |resolved| return resolved;
        }
        return null;
    }

    fn resolveContainerFieldNodeType(self: ProjectTypeResolver, file_index: usize, node: u32, field_name: []const u8) ?ResolvedType {
        const file = self.files[file_index];
        const tree = file.tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;

        if (import_resolver.isVarDeclTag(tags[node])) {
            const full = tree.fullVarDecl(@enumFromInt(node)) orelse return null;
            const name_token = full.ast.mut_token + 1;
            if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
            const name = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token));
            if (!std.mem.eql(u8, name, field_name)) return null;

            const nested_resolver = self.forFile(file_index);
            return nested_resolver.resolveVarDeclType(full, node, name);
        }

        const field = tree.fullContainerField(@enumFromInt(node)) orelse return null;
        if (field.ast.tuple_like) return null;
        const name_token = field.ast.main_token;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;

        if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), field_name)) return null;

        const nested_resolver = self.forFile(file_index);
        if (field.ast.type_expr.unwrap()) |type_node| {
            return nested_resolver.resolveTypeNode(@intFromEnum(type_node));
        }
        if (field.ast.value_expr.unwrap()) |value_node| {
            return nested_resolver.resolveInitializerType(@intFromEnum(value_node));
        }
        return null;
    }
};

const VisitedBinding = enum {
    /// Recorded on the current chain; the walk may continue.
    recorded,
    /// Already on the current chain; an alias cycle ends the walk.
    repeated,
    /// The chain budget ran out; the walk is truncated, not cycled.
    exhausted,
};

/// Name a walk that stopped at its frame budget. The answer stays
/// conservative, but the cut-off is reported so a truncated search is never
/// read as a chain that does not exist.
fn reportResolutionBudget(walk: []const u8, frames: usize, path: ?[]const u8) void {
    const file = if (path) |candidate| candidate else "";
    if (file.len == 0) {
        log.warn("resolution budget exceeded: {s} stopped at the {d}-frame limit; the answer stays conservative", .{
            walk,
            frames,
        });
        return;
    }
    log.warn("resolution budget exceeded: {s} stopped at the {d}-frame limit in {s}; the answer stays conservative", .{
        walk,
        frames,
        file,
    });
}

/// Record `declaration_node` on the current trusted-import resolution chain.
/// Returns `repeated` when the binding is already recorded and `exhausted`
/// when the chain budget ran out; either one stops the walk, and only the
/// second is a budget report.
fn pushVisitedBinding(visited: *[resolution_budget_frames]u32, depth: usize, declaration_node: u32) VisitedBinding {
    if (depth >= visited.len) return .exhausted;
    if (std.mem.indexOfScalar(u32, visited[0..depth], declaration_node) != null) return .repeated;
    visited[depth] = declaration_node;
    return .recorded;
}

fn functionProtoNode(tree: *const std.zig.Ast, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return null;
    return switch (tags[node]) {
        .fn_decl => @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]),
        .fn_proto,
        .fn_proto_simple,
        .fn_proto_one,
        .fn_proto_multi,
        => node,
        else => null,
    };
}

fn functionProtoName(tree: *const std.zig.Ast, proto_node: u32) ?[]const u8 {
    const tags = tree.nodes.items(.tag);
    if (proto_node >= tags.len) return null;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const name_token = switch (tags[proto_node]) {
        .fn_proto => tree.fnProto(@enumFromInt(proto_node)).name_token,
        .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)).name_token,
        .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(proto_node)).name_token,
        .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)).name_token,
        else => return null,
    } orelse return null;
    if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
    return tree.tokenSlice(name_token);
}

/// The declared type of the parameter written at `parameter_index`, counted in
/// the order the prototype writes its parameters rather than over the typed
/// subset `ast.params` holds.
///
/// `ast.params` omits `anytype` and `...` slots entirely, so indexing it with a
/// written ordinal silently answers with the next parameter's declaration. The
/// full-prototype iterator reports those slots in place with no type
/// expression, so an inferred slot answers `null` instead of borrowing its
/// neighbour, and a written ordinal after one still lands on its own parameter.
fn protoParamTypeNode(
    tree: *const std.zig.Ast,
    proto_node: u32,
    parameter_index: usize,
) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (proto_node >= tags.len) return null;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const fn_proto = tree.fullFnProto(&buffer, @enumFromInt(proto_node)) orelse return null;
    var params = fn_proto.iterate(tree);
    var written: usize = 0;
    while (params.next()) |param| : (written += 1) {
        if (written != parameter_index) continue;
        const parameter_node = param.type_expr orelse return null;
        if (@intFromEnum(parameter_node) >= tags.len) return null;
        if (import_resolver.isVarDeclTag(tags[@intFromEnum(parameter_node)])) {
            const full = tree.fullVarDecl(parameter_node) orelse return null;
            return @intFromEnum(full.ast.type_node.unwrap() orelse return null);
        }
        return @intFromEnum(parameter_node);
    }
    return null;
}

/// Whether the prototype's first written parameter is an inferred one, written
/// `anytype` or `...`. Such a slot is absent from `ast.params`, so this reads
/// the written order rather than that slice, and a prototype with no
/// parameters at all is not inferred: it simply has no receiver slot.
fn protoFirstParamIsInferred(tree: *const std.zig.Ast, proto_node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (proto_node >= tags.len) return false;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const fn_proto = tree.fullFnProto(&buffer, @enumFromInt(proto_node)) orelse return false;
    var params = fn_proto.iterate(tree);
    const first = params.next() orelse return false;
    return first.type_expr == null;
}

pub fn resolvedTypesEqual(lhs: ResolvedType, rhs: ResolvedType) bool {
    return lhs.file_index == rhs.file_index and lhs.container_node == rhs.container_node;
}

pub fn typeInfoFromTypeNode(
    tree: *const std.zig.Ast,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    type_node: u32,
) ?TypeInfo {
    if (type_node >= tags.len) return null;
    return switch (tags[type_node]) {
        .error_union => {
            const pair = datas[type_node].node_and_node;
            return typeInfoFromTypeNode(tree, tags, datas, @intFromEnum(pair[1]));
        },
        .optional_type => {
            const child = datas[type_node].node;
            return typeInfoFromTypeNode(tree, tags, datas, @intFromEnum(child));
        },
        .ptr_type_sentinel, .ptr_type, .ptr_type_aligned, .ptr_type_bit_range => {
            if (tree.fullPtrType(@enumFromInt(type_node))) |pt| {
                const has_sentinel = pt.ast.sentinel != .none;
                return .{
                    .kind = if (pt.size == .slice) .slice else .pointer,
                    .sentinel = if (has_sentinel) .{ .value = 0 } else null,
                };
            }
            return TypeInfo.initPointer();
        },
        .slice_sentinel, .array_type_sentinel => TypeInfo{ .kind = .slice, .sentinel = .{ .value = 0 } },
        .slice, .slice_open => TypeInfo{ .kind = .slice },
        else => null,
    };
}

pub fn isAssignTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .assign,
        .assign_mul,
        .assign_div,
        .assign_mod,
        .assign_add,
        .assign_sub,
        .assign_shl,
        .assign_shl_sat,
        .assign_shr,
        .assign_bit_and,
        .assign_bit_xor,
        .assign_bit_or,
        .assign_mul_wrap,
        .assign_add_wrap,
        .assign_sub_wrap,
        .assign_mul_sat,
        .assign_add_sat,
        .assign_sub_sat,
        => true,
        else => false,
    };
}

pub fn isContainerTag(tag: std.zig.Ast.Node.Tag) bool {
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

fn appendFqnPart(buffer: *[256]u8, part: []const u8, pos: *usize) bool {
    if (part.len == 0) return false;
    if (pos.* + part.len > buffer.len) return false;
    std.mem.copyForwards(u8, buffer[pos.* .. pos.* + part.len], part);
    pos.* += part.len;
    return true;
}

fn appendFqnSeparator(buffer: *[256]u8, pos: *usize) bool {
    if (pos.* >= buffer.len) return false;
    buffer[pos.*] = '.';
    pos.* += 1;
    return true;
}

fn builtinCallName(
    tree: *const std.zig.Ast,
    tags: []const std.zig.Ast.Node.Tag,
    token_tags: []const std.zig.Token.Tag,
    node_idx: u32,
) ?[]const u8 {
    if (!import_resolver.isBuiltinCallTag(tags[node_idx])) return null;

    const builtin_token = tree.nodes.items(.main_token)[node_idx];
    if (builtin_token >= token_tags.len) return null;
    if (token_tags[builtin_token] != .builtin) return null;
    return tree.tokenSlice(builtin_token);
}

fn isUnknownTypeInfo(info: TypeInfo) bool {
    return info.kind == .unknown and info.type_str == null and !info.hasSentinel();
}

fn findAncestorFn(
    type_ctx: *TypeContext,
    tree: *const std.zig.Ast,
    parent_map: []const u32,
    start_node: u32,
) ?u32 {
    const tags = tree.nodes.items(.tag);
    var node = start_node;
    var depth: u32 = 0;
    while (node < parent_map.len) {
        if (depth >= resolution_budget_frames) {
            reportResolutionBudget("enclosing-function parent climb", resolution_budget_frames, typeContextFilePath(type_ctx, tree));
            return null;
        }
        depth += 1;
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) return null;
        if (tags[parent] == .fn_decl) return parent;
        node = parent;
    }
    return null;
}

fn returnTypeInfoFromFn(
    tree: *const std.zig.Ast,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    fn_node: u32,
) ?TypeInfo {
    if (fn_node >= tags.len or tags[fn_node] != .fn_decl) return null;
    var buf: [1]std.zig.Ast.Node.Index = undefined;
    const fn_proto = tree.fullFnProto(&buf, @enumFromInt(fn_node)) orelse return null;
    const ret_type_node = @intFromEnum(fn_proto.ast.return_type);
    return typeInfoFromTypeNode(tree, tags, datas, ret_type_node);
}

fn isRootDeclNode(tree: *const std.zig.Ast, node_index: usize) bool {
    for (tree.rootDecls()) |decl| {
        if (@intFromEnum(decl) == node_index) return true;
    }
    return false;
}

fn isThisBuiltinCall(tree: *const std.zig.Ast, node: usize) bool {
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= main_tokens.len) return false;
    const token = main_tokens[node];
    if (token >= tree.tokens.len) return false;
    return std.mem.eql(u8, tree.tokenSlice(token), "@This");
}

/// Smallest container whose token range holds `token`, or null for the root
/// namespace. The span rule is the tie break the indexed walk has to match: a
/// strictly smaller span wins, so equal spans keep the lowest node index.
fn smallestContainingContainer(
    tree: *const std.zig.Ast,
    tags: []const std.zig.Ast.Node.Tag,
    token: u32,
) ?u32 {
    var enclosing: ?u32 = null;
    var smallest_span: usize = tree.tokens.len;
    for (tags, 0..) |tag, index| {
        if (!isContainerTag(tag)) continue;
        const container: std.zig.Ast.Node.Index = @enumFromInt(index);
        const first = tree.firstToken(container);
        const last = tree.lastToken(container);
        if (token < first or token > last) continue;
        const span = @as(usize, last) - first;
        if (span >= smallest_span) continue;
        smallest_span = span;
        enclosing = @intCast(index);
    }
    return enclosing;
}

fn nodeIsAncestor(ancestor: u32, descendant: u32, parent_map: []const u32) bool {
    if (ancestor == descendant) return true;
    var node = descendant;
    var depth: u32 = 0;
    while (node < parent_map.len) {
        if (depth >= ancestor_map_budget_frames) {
            reportResolutionBudget("ancestor-map climb", ancestor_map_budget_frames, null);
            return false;
        }
        depth += 1;
        const parent = parent_map[node];
        if (parent == 0 or parent >= parent_map.len) return false;
        if (parent == ancestor) return true;
        node = parent;
    }
    return false;
}

fn findParentNode(tree: *const std.zig.Ast, child: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (child == 0 or child >= tags.len) return null;
    const child_first = tree.firstToken(@enumFromInt(child));
    const child_last = tree.lastToken(@enumFromInt(child));
    const Match = struct {
        child: u32,
        stop: bool = false,

        fn visit(_: *const std.zig.Ast, node: u32, match: *@This()) error{}!void {
            if (node == match.child) match.stop = true;
        }
    };
    for (1..tags.len) |index| {
        if (index == child) continue;
        const candidate: std.zig.Ast.Node.Index = @enumFromInt(index);
        if (tree.firstToken(candidate) > child_first or tree.lastToken(candidate) < child_last) continue;
        var match = Match{ .child = child };
        ast_walk.walkChildren(Match, tree, @intCast(index), &match, Match.visit) catch unreachable;
        if (match.stop) return @intCast(index);
    }
    return null;
}

test "project resolution rejects malformed imports without hiding valid siblings" {
    const allocator = std.testing.allocator;
    var source = try std.zig.Ast.parse(allocator,
        \\const malformed = @import("malformed.zig");
        \\const valid = @import("valid.zig");
        \\const bad_value: malformed = undefined;
        \\const good_value: valid = undefined;
        \\const bad_field = bad_value.wrapped;
        \\const good_field = good_value.wrapped;
        \\const bad_type = malformed.Container;
        \\const good_type = valid.Container;
        \\const bad_alias = malformed.Alias;
        \\const good_alias = valid.Alias;
        \\const bad_call = malformed.make();
        \\const good_call = valid.make();
        \\const bad_method = malformed.Container.make();
        \\const good_method = valid.Container.make();
        \\const bad_cycle = valid.Cycle;
    , .zig);
    defer source.deinit(allocator);
    var malformed = try std.zig.Ast.parse(allocator,
        \\wrapped: @import("valid.zig"),
        \\pub const Container = struct {
        \\    wrapped: @import("valid.zig"),
        \\    pub fn make() @import("valid.zig") { return undefined; }
        \\};
        \\pub const Alias = Container;
        \\pub const Cycle = @import("valid.zig").Cycle;
        \\pub fn make() @import("valid.zig") { return undefined; }
        \\const broken = ;
    , .zig);
    defer malformed.deinit(allocator);
    var valid = try std.zig.Ast.parse(allocator,
        \\wrapped: Container,
        \\pub const Container = struct {
        \\    wrapped: u8,
        \\    pub fn make() Container { return undefined; }
        \\};
        \\pub const Alias = Container;
        \\pub const Cycle = @import("malformed.zig").Cycle;
        \\pub fn make() Container { return undefined; }
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
    var files = [_]import_resolver.File{
        .{ .path = "source.zig", .tree = &source },
        .{ .path = "malformed.zig", .tree = &malformed },
        .{ .path = "valid.zig", .tree = &valid },
    };
    var paths = try import_resolver.PathIndex.init(allocator, &files);
    defer paths.deinit(allocator);
    for ([_]bool{ false, true }) |indexed| {
        files[0].lexical_index = if (indexed) &source_index else null;
        files[1].lexical_index = if (indexed) &malformed_index else null;
        files[2].lexical_index = if (indexed) &valid_index else null;
        for (&files) |*file| file.path_index = if (indexed) &paths else null;
        const resolver: ProjectTypeResolver = .{ .files = &files, .file_index = 0 };
        try std.testing.expectEqual(@as(?usize, 1), import_resolver.findFileIndexByPath(&files, "malformed.zig"));
        try std.testing.expectEqual(@as(?usize, 2), import_resolver.findFileIndexByPath(&files, "valid.zig"));

        for (source.rootDecls()[4..]) |declaration| {
            const full = source.fullVarDecl(declaration) orelse return error.TestUnexpectedResult;
            const name = source.tokenSlice(full.ast.mut_token + 1);
            const node = @intFromEnum(full.ast.init_node.unwrap() orelse return error.TestUnexpectedResult);
            const resolved = resolver.resolveExprType(node);
            if (std.mem.startsWith(u8, name, "good_")) {
                const result = resolved orelse return error.MissingValidType;
                try std.testing.expectEqual(@as(usize, 2), result.file_index);
                try std.testing.expectEqualStrings("Container", result.type_name orelse return error.TestUnexpectedResult);
            } else {
                try std.testing.expect(resolved == null);
            }
            if (isCallNode(source.nodeTag(@enumFromInt(node)))) {
                const returned = resolver.resolveCallReturnTypeNode(node);
                if (std.mem.startsWith(u8, name, "good_")) {
                    const result = returned orelse return error.MissingValidReturnType;
                    try std.testing.expectEqual(@as(usize, 2), result.file_index);
                    try std.testing.expectEqualStrings("Container", valid.getNodeSource(@enumFromInt(result.node_index)));
                } else {
                    try std.testing.expect(returned == null);
                }
            } else if (std.mem.endsWith(u8, name, "_type") or std.mem.endsWith(u8, name, "_alias")) {
                const alias = resolver.resolveTypeAliasNode(node);
                if (std.mem.startsWith(u8, name, "good_")) {
                    try std.testing.expectEqual(@as(usize, 2), (alias orelse return error.MissingValidAlias).file_index);
                } else {
                    try std.testing.expect(alias == null);
                }
            }
        }

        const bad_root: ResolvedType = .{ .file_index = 1 };
        try std.testing.expect(resolver.resolveFieldTypeNode(bad_root, "wrapped") == null);
        try std.testing.expect(resolver.resolveMemberReturnTypeNode(bad_root, "make") == null);
        const good_root: ResolvedType = .{ .file_index = 2 };
        const field = resolver.resolveFieldTypeNode(good_root, "wrapped") orelse return error.MissingValidField;
        try std.testing.expectEqual(@as(usize, 2), field.file_index);
        try std.testing.expectEqualStrings("Container", valid.getNodeSource(@enumFromInt(field.node_index)));

        const invalid: ProjectTypeResolver = .{ .files = &files, .file_index = 1 };
        for (malformed.nodes.items(.tag), 0..) |tag, node| {
            try std.testing.expect(invalid.resolveExprType(node) == null);
            try std.testing.expect(invalid.resolveTypeNode(node) == null);
            try std.testing.expect(invalid.resolveTypeAliasNode(@intCast(node)) == null);
            try std.testing.expect(invalid.resolveDeclarationNode(node) == null);
            try std.testing.expect(invalid.resolveCallReturnTypeNode(@intCast(node)) == null);
            try std.testing.expect(invalid.resolveCallArgumentTypeNode(@intCast(node), @intCast(node), &.{}) == null);
            try std.testing.expect(invalid.resolveResultLocationTypeNode(@intCast(node)) == null);
            if (isContainerTag(tag)) {
                const container: ResolvedType = .{ .file_index = 1, .container_node = @intCast(node) };
                try std.testing.expect(resolver.resolveFieldTypeNode(container, "wrapped") == null);
                try std.testing.expect(resolver.resolveMemberReturnTypeNode(container, "make") == null);
            }
        }
    }
}

test "indexed lexical bindings preserve unindexed scope and alias resolution" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const forward = Later;
        \\const Later = struct {};
        \\const Other = struct {};
        \\const CycleA = CycleB;
        \\const CycleB = CycleA;
        \\fn run(value: Later, @"quoted value": Other, cycle: CycleA) void {
        \\    value.outer();
        \\    @"quoted value".quoted();
        \\    cycle.cyclic();
        \\    {
        \\        value.before();
        \\        const value: Other = undefined;
        \\        value.inner();
        \\    }
        \\    value.after();
        \\    forward.forwarded();
        \\    const Nested = struct {
        \\        fn nested(value: Other) void { value.nested(); }
        \\    };
        \\    _ = Nested;
        \\}
        \\fn unrelated(value: Other) void { value.unrelated(); }
    ;
    var tree = try std.zig.Ast.parse(allocator, code, .zig);
    defer tree.deinit(allocator);
    var index = try LexicalIndex.init(allocator, &tree);
    defer index.deinit(allocator);
    const indexed_files = [_]import_resolver.File{.{ .path = "api.zig", .tree = &tree, .lexical_index = &index }};
    const plain_files = [_]import_resolver.File{.{ .path = "api.zig", .tree = &tree }};
    const indexed: ProjectTypeResolver = .{ .files = &indexed_files, .file_index = 0 };
    const plain: ProjectTypeResolver = .{ .files = &plain_files, .file_index = 0 };
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, node| {
        if (tag != .field_access) continue;
        const access = tree.nodes.items(.data)[node].node_and_token;
        const receiver = @intFromEnum(access[0]);
        const method = tree.tokenSlice(access[1]);
        try std.testing.expectEqual(plain.resolveDeclarationNode(receiver), indexed.resolveDeclarationNode(receiver));
        const expected = plain.resolveExprType(receiver);
        const actual = indexed.resolveExprType(receiver);
        if (std.mem.eql(u8, method, "cyclic")) {
            try std.testing.expectEqual(@as(?ResolvedType, null), actual);
        } else {
            const resolved = actual orelse return error.MissingIndexedType;
            try std.testing.expect(resolvedTypesEqual(expected orelse return error.MissingUnindexedType, resolved));
            const uses_other = std.mem.eql(u8, method, "quoted") or std.mem.eql(u8, method, "inner") or
                std.mem.eql(u8, method, "nested") or std.mem.eql(u8, method, "unrelated");
            try std.testing.expectEqualStrings(if (uses_other) "Other" else "Later", resolved.type_name orelse return error.TestUnexpectedResult);
        }
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 9), checked);
}

test "indexed result locations preserve scoped calls and return types" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Value = struct {
        \\    fn init() Value { return undefined; }
        \\};
        \\fn accept(value: Value) void { _ = value; }
        \\fn run() Value {
        \\    const value: Value = .init();
        \\    accept(.init());
        \\    _ = value;
        \\    return .init();
        \\}
    ;
    var tree = try std.zig.Ast.parse(allocator, code, .zig);
    defer tree.deinit(allocator);
    var index = try LexicalIndex.init(allocator, &tree);
    defer index.deinit(allocator);
    const indexed_files = [_]import_resolver.File{.{ .path = "api.zig", .tree = &tree, .lexical_index = &index }};
    const plain_files = [_]import_resolver.File{.{ .path = "api.zig", .tree = &tree }};
    const indexed: ProjectTypeResolver = .{ .files = &indexed_files, .file_index = 0 };
    const plain: ProjectTypeResolver = .{ .files = &plain_files, .file_index = 0 };
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, node| {
        if (!isCallNode(tag)) continue;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return error.TestUnexpectedResult;
        if (tree.nodeTag(call.ast.fn_expr) != .enum_literal) continue;
        const expected = plain.resolveResultLocationTypeNode(@intCast(node)) orelse return error.MissingUnindexedResult;
        const actual = indexed.resolveResultLocationTypeNode(@intCast(node)) orelse return error.MissingIndexedResult;
        try std.testing.expectEqualDeep(expected, actual);
        try std.testing.expectEqualStrings("Value", tree.getNodeSource(@enumFromInt(actual.node_index)));
        const result = indexed.resolveCallReturnTypeNode(@intCast(node)) orelse return error.MissingReturnType;
        try std.testing.expectEqualDeep(plain.resolveCallReturnTypeNode(@intCast(node)) orelse return error.TestUnexpectedResult, result);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), checked);
}

test "ProjectTypeResolver rejects cyclic aliases without hiding valid receivers" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const A = B;
        \\const B = A;
        \\const Good = struct {};
        \\fn run(x: A, good: Good) void { x.run(); good.run(); }
    ;
    var tree = try std.zig.Ast.parse(allocator, code, .zig);
    defer tree.deinit(allocator);
    const files = [_]import_resolver.File{.{ .path = "api.zig", .tree = &tree }};
    const resolver: ProjectTypeResolver = .{ .files = &files, .file_index = 0 };
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, node| {
        if (tag != .field_access) continue;
        const receiver = @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]);
        const name = import_resolver.identifierName(&tree, receiver) orelse continue;
        const resolved = resolver.resolveExprType(receiver);
        if (std.mem.eql(u8, name, "x")) {
            try std.testing.expectEqual(@as(?ResolvedType, null), resolved);
        } else {
            const good = resolved orelse return error.TestUnexpectedResult;
            try std.testing.expectEqualStrings("Good", good.type_name orelse return error.TestUnexpectedResult);
        }
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), checked);
}

test "ProjectTypeResolver rejects cross-file member alias cycles" {
    const allocator = std.testing.allocator;
    var first = try std.zig.Ast.parse(allocator,
        \\const b = @import("b.zig");
        \\pub const A = b.B;
        \\fn run(x: A) void { x.run(); }
    , .zig);
    defer first.deinit(allocator);
    var second = try std.zig.Ast.parse(allocator,
        \\const a = @import("a.zig");
        \\pub const B = a.A;
    , .zig);
    defer second.deinit(allocator);
    var first_index = try LexicalIndex.init(allocator, &first);
    defer first_index.deinit(allocator);
    var second_index = try LexicalIndex.init(allocator, &second);
    defer second_index.deinit(allocator);
    const files = [_]import_resolver.File{
        .{ .path = "a.zig", .tree = &first, .lexical_index = &first_index },
        .{ .path = "b.zig", .tree = &second, .lexical_index = &second_index },
    };
    const resolver: ProjectTypeResolver = .{ .files = &files, .file_index = 0 };
    for (first.nodes.items(.tag), 0..) |tag, node| {
        if (tag != .field_access) continue;
        const receiver = @intFromEnum(first.nodes.items(.data)[node].node_and_token[0]);
        const name = import_resolver.identifierName(&first, receiver) orelse continue;
        if (!std.mem.eql(u8, name, "x")) continue;
        try std.testing.expectEqual(@as(?ResolvedType, null), resolver.resolveExprType(receiver));
        return;
    }
    return error.TestUnexpectedResult;
}

test "indexed This containers match the unindexed scan" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Root = struct {
        \\    self: @This() = .{},
        \\    const Inner = struct {
        \\        self: @This() = .{},
        \\        fn scoped() @This() {
        \\            return .{};
        \\        }
        \\        fn use() void {
        \\            const local: @This() = .{};
        \\            _ = local;
        \\            {
        \\                const deeper: @This() = .{};
        \\                _ = deeper;
        \\            }
        \\        }
        \\    };
        \\    fn run() void {
        \\        {
        \\            const in_block: @This() = .{};
        \\            _ = in_block;
        \\        }
        \\        Inner.use();
        \\    }
        \\    fn makeChild() struct { value: @This() } {
        \\        return .{ .value = .{} };
        \\    }
        \\};
        \\fn topLevel() void {
        \\    const root_scope: @This() = .{};
        \\    _ = root_scope;
        \\}
    ;
    var tree = try std.zig.Ast.parse(allocator, code, .zig);
    defer tree.deinit(allocator);
    // An inert index would make every comparison below trivially equal.
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var index = try LexicalIndex.init(allocator, &tree);
    defer index.deinit(allocator);
    // Expected containers come from the declarations that create them, never
    // from the text of the file.
    const Declared = struct {
        fn containerInitializer(ast: *const std.zig.Ast, name: []const u8) ?u32 {
            for (ast.nodes.items(.tag), 0..) |tag, node| {
                if (!import_resolver.isVarDeclTag(tag)) continue;
                const full = ast.fullVarDecl(@enumFromInt(node)) orelse continue;
                const name_token = full.ast.mut_token + 1;
                if (name_token >= ast.tokens.len or ast.tokenTag(name_token) != .identifier) continue;
                if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(ast.tokenSlice(name_token)), name)) continue;
                return @intFromEnum(full.ast.init_node.unwrap() orelse return null);
            }
            return null;
        }

        fn returnedContainer(ast: *const std.zig.Ast, name: []const u8) ?u32 {
            for (ast.nodes.items(.tag), 0..) |tag, node| {
                if (tag != .fn_decl) continue;
                const proto = functionProtoNode(ast, @intCast(node)) orelse continue;
                const declared = functionProtoName(ast, proto) orelse continue;
                if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(declared), name)) continue;
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const full = ast.fullFnProto(&buffer, @enumFromInt(proto)) orelse continue;
                return @intFromEnum(full.ast.return_type.unwrap() orelse return null);
            }
            return null;
        }
    };
    const root_container = Declared.containerInitializer(&tree, "Root") orelse return error.MissingRootContainer;
    const inner_container = Declared.containerInitializer(&tree, "Inner") orelse return error.MissingInnerContainer;
    const child_container = Declared.returnedContainer(&tree, "makeChild") orelse return error.MissingChildContainer;
    try std.testing.expect(isContainerTag(tree.nodeTag(@enumFromInt(root_container))));
    try std.testing.expect(isContainerTag(tree.nodeTag(@enumFromInt(inner_container))));
    try std.testing.expect(isContainerTag(tree.nodeTag(@enumFromInt(child_container))));
    try std.testing.expect(root_container != inner_container and inner_container != child_container);
    const indexed_files = [_]import_resolver.File{.{ .path = "api.zig", .tree = &tree, .lexical_index = &index }};
    const plain_files = [_]import_resolver.File{.{ .path = "api.zig", .tree = &tree }};
    const indexed: ProjectTypeResolver = .{ .files = &indexed_files, .file_index = 0 };
    const plain: ProjectTypeResolver = .{ .files = &plain_files, .file_index = 0 };
    // Sites in source order: Root's field, Inner's field, Inner's returned
    // type, two Inner locals, one Root local inside a block, the returned
    // anonymous container's field, and one site outside every container.
    const expected_containers = [_]?u32{
        root_container,
        inner_container,
        inner_container,
        inner_container,
        inner_container,
        root_container,
        child_container,
        null,
    };
    var this_nodes: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, node| {
        if (!isThisBuiltinCall(&tree, node)) continue;
        try std.testing.expect(this_nodes < expected_containers.len);
        const expected = expected_containers[this_nodes];
        this_nodes += 1;
        try std.testing.expectEqualDeep(plain.resolveTypeNode(node), indexed.resolveTypeNode(node));
        try std.testing.expectEqualDeep(plain.resolveExprType(node), indexed.resolveExprType(node));
        const resolved = indexed.resolveTypeNode(node) orelse return error.MissingThisType;
        try std.testing.expectEqual(@as(usize, 0), resolved.file_index);
        try std.testing.expectEqual(expected, resolved.container_node);
        if (resolved.container_node) |container| {
            try std.testing.expect(isContainerTag(tree.nodeTag(@enumFromInt(container))));
        }
    }
    // Root, Inner and the returned anonymous container each own sites, and the
    // only site outside every container is the root-level function.
    try std.testing.expectEqual(expected_containers.len, this_nodes);
}

test "an inert lexical index leaves This answers to the scan" {
    const allocator = std.testing.allocator;
    var tree = try std.zig.Ast.parse(allocator,
        \\const Broken = struct {
        \\    self: @This() = .{},
        \\    fn use() void {
        \\        const scoped: @This() = .{};
        \\        _ = scoped;
        \\    }
        \\    const dangling =
    , .zig);
    defer tree.deinit(allocator);
    try std.testing.expect(tree.errors.len != 0);
    var index = try LexicalIndex.init(allocator, &tree);
    defer index.deinit(allocator);
    const indexed_files = [_]import_resolver.File{.{ .path = "broken.zig", .tree = &tree, .lexical_index = &index }};
    const plain_files = [_]import_resolver.File{.{ .path = "broken.zig", .tree = &tree }};
    const indexed: ProjectTypeResolver = .{ .files = &indexed_files, .file_index = 0 };
    const plain: ProjectTypeResolver = .{ .files = &plain_files, .file_index = 0 };
    // Parser recovery decides which nodes survive, so only the surviving sites
    // are compared; each one must stay unanswered on both paths.
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |_, node| {
        if (!isThisBuiltinCall(&tree, node)) continue;
        try std.testing.expectEqual(@as(?ResolvedType, null), plain.resolveTypeNode(node));
        try std.testing.expectEqual(@as(?ResolvedType, null), indexed.resolveTypeNode(node));
        checked += 1;
    }
    try std.testing.expect(checked != 0);

    // The same shape without the recovery site answers with a real container,
    // which is what makes the recovered-tree silence meaningful.
    var whole = try std.zig.Ast.parse(allocator,
        \\const Broken = struct {
        \\    self: @This() = .{},
        \\    fn use() void {
        \\        const scoped: @This() = .{};
        \\        _ = scoped;
        \\    }
        \\};
    , .zig);
    defer whole.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 0), whole.errors.len);
    var whole_index = try LexicalIndex.init(allocator, &whole);
    defer whole_index.deinit(allocator);
    const whole_indexed_files = [_]import_resolver.File{.{ .path = "broken.zig", .tree = &whole, .lexical_index = &whole_index }};
    const whole_plain_files = [_]import_resolver.File{.{ .path = "broken.zig", .tree = &whole }};
    const whole_indexed: ProjectTypeResolver = .{ .files = &whole_indexed_files, .file_index = 0 };
    const whole_plain: ProjectTypeResolver = .{ .files = &whole_plain_files, .file_index = 0 };
    // The same shape without the recovery site answers with the container its
    // own declaration creates, which is what makes the silence above mean
    // something.
    var whole_container: ?u32 = null;
    for (whole.nodes.items(.tag), 0..) |tag, node| {
        if (!import_resolver.isVarDeclTag(tag)) continue;
        const full = whole.fullVarDecl(@enumFromInt(node)) orelse continue;
        const name_token = full.ast.mut_token + 1;
        if (name_token >= whole.tokens.len or whole.tokenTag(name_token) != .identifier) continue;
        if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(whole.tokenSlice(name_token)), "Broken")) continue;
        whole_container = @intFromEnum(full.ast.init_node.unwrap() orelse return error.MissingContainerInitializer);
        break;
    }
    const broken_container = whole_container orelse return error.MissingBrokenContainer;
    try std.testing.expect(isContainerTag(whole.nodeTag(@enumFromInt(broken_container))));
    var answered: usize = 0;
    for (whole.nodes.items(.tag), 0..) |_, node| {
        if (!isThisBuiltinCall(&whole, node)) continue;
        const resolved = whole_indexed.resolveTypeNode(node) orelse return error.MissingThisType;
        try std.testing.expectEqual(@as(usize, 0), resolved.file_index);
        try std.testing.expectEqual(@as(?u32, broken_container), resolved.container_node);
        try std.testing.expectEqualDeep(whole_plain.resolveTypeNode(node), resolved);
        answered += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), answered);
}

test "a written parameter after an anytype slot keeps its own declared type" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Marker = struct {
        \\    id: u32,
        \\};
        \\const Box = struct {
        \\    payload: []u8,
        \\    fn passthrough(self: anytype, sink: anytype, target: *Box, marker: *Marker) *Box {
        \\        _ = self;
        \\        _ = sink;
        \\        _ = marker;
        \\        return target;
        \\    }
        \\};
        \\fn instance(box: *Box, first: *Box, second: *Box, third: *Marker) void {
        \\    _ = box.passthrough(first, second, third);
        \\}
        \\fn namespaced(receiver: *Box, sink: *Marker, target: *Box, marker: *Marker) void {
        \\    _ = Box.passthrough(receiver, sink, target, marker);
        \\}
    ;
    var tree = try std.zig.Ast.parse(allocator, code, .zig);
    defer tree.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    const files = [_]import_resolver.File{.{ .path = "written.zig", .tree = &tree }};
    const resolver: ProjectTypeResolver = .{ .files = &files, .file_index = 0 };

    // Both calls are found by the method they name; the instance call is the
    // one whose receiver is a value, the namespace call the one whose receiver
    // is the container itself.
    var instance_call: ?u32 = null;
    var namespace_call: ?u32 = null;
    var box_container: ?u32 = null;
    var marker_container: ?u32 = null;
    for (tree.nodes.items(.tag), 0..) |tag, node| {
        if (isCallNode(tag)) {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse continue;
            if (tree.nodeTag(call.ast.fn_expr) != .field_access) continue;
            const access = tree.nodes.items(.data)[@intFromEnum(call.ast.fn_expr)].node_and_token;
            const receiver = @intFromEnum(access[0]);
            if (tree.nodeTag(@enumFromInt(receiver)) != .identifier) continue;
            const receiver_name = import_resolver.identifierName(&tree, receiver) orelse continue;
            if (std.mem.eql(u8, receiver_name, "box")) {
                instance_call = @intCast(node);
            } else if (std.mem.eql(u8, receiver_name, "Box")) {
                namespace_call = @intCast(node);
            }
            continue;
        }
        if (!import_resolver.isVarDeclTag(tag)) continue;
        const full = tree.fullVarDecl(@enumFromInt(node)) orelse continue;
        const name_token = full.ast.mut_token + 1;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
        const initializer = @intFromEnum(full.ast.init_node.unwrap() orelse continue);
        if (std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), "Box")) {
            box_container = initializer;
        } else if (std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), "Marker")) {
            marker_container = initializer;
        }
    }
    const instance = instance_call orelse return error.MissingInstanceCall;
    const namespaced = namespace_call orelse return error.MissingNamespaceCall;
    const container = box_container orelse return error.MissingBoxContainer;
    const marker = marker_container orelse return error.MissingMarkerContainer;

    // Both call shapes name one declaration and differ only in how many leading
    // parameters the receiver consumed, which is what shifts the credit. The
    // callee is the prototype the method name reaches, and this file owns it.
    const callable = resolver.resolveCallableAtCall(instance) orelse return error.MissingInstanceCallable;
    try std.testing.expectEqual(@as(usize, 1), callable.implicit_self_count);
    try std.testing.expectEqual(@as(usize, 0), callable.file_index);
    try std.testing.expectEqualStrings("passthrough", functionProtoName(&tree, callable.proto_node) orelse
        return error.MissingProtoName);
    const static_callable = resolver.resolveCallableAtCall(namespaced) orelse return error.MissingNamespaceCallable;
    try std.testing.expectEqual(@as(usize, 0), static_callable.implicit_self_count);
    try std.testing.expectEqual(callable.file_index, static_callable.file_index);
    try std.testing.expectEqual(callable.proto_node, static_callable.proto_node);

    // Each written argument is checked against the prototype slot it occupies.
    // The receiver is written `anytype`, so the instance call supplies it: its
    // three arguments are slots one to three, and the inferred slot one names no
    // type. The namespace call supplies nothing, so its four arguments are slots
    // zero to three and both inferred slots name none. The two typed slots that
    // follow keep the distinct pointees the prototype wrote for them, so a credit
    // shifted by the receiver hands an argument its neighbour's pointee, and
    // indexing the typed-only parameter slice answers the first typed argument
    // with no type at all.
    //
    // Every check runs through the public API and then through the type it names,
    // so what is asserted is what a consumer observes, not the pointer node kind
    // the frontend emitted for the written type.
    var instance_buffer: [1]std.zig.Ast.Node.Index = undefined;
    var namespace_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const shapes = [_]struct {
        call: u32,
        params: []const std.zig.Ast.Node.Index,
        pointees: []const ?u32,
    }{
        .{
            .call = instance,
            .params = (tree.fullCall(&instance_buffer, @enumFromInt(instance)) orelse
                return error.MissingInstanceCall).ast.params,
            .pointees = &.{ null, container, marker },
        },
        .{
            .call = namespaced,
            .params = (tree.fullCall(&namespace_buffer, @enumFromInt(namespaced)) orelse
                return error.MissingNamespaceCall).ast.params,
            .pointees = &.{ null, null, container, marker },
        },
    };
    for (shapes) |shape| {
        try std.testing.expectEqual(shape.pointees.len, shape.params.len);
        for (shape.params, shape.pointees) |argument, pointee| {
            const declared = resolver.resolveCallArgumentTypeNode(
                shape.call,
                @intFromEnum(argument),
                &.{},
            );
            if (pointee == null) {
                try std.testing.expect(declared == null);
                continue;
            }
            const named = resolver.resolveTypeNode(declared orelse return error.MissingTypedArgument) orelse
                return error.MissingPointerTarget;
            try std.testing.expectEqual(@as(usize, 0), named.file_index);
            try std.testing.expectEqual(pointee, named.container_node);
        }
    }
}
