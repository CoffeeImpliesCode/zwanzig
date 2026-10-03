const std = @import("std");
const import_resolver = @import("import_resolver.zig");
const ast_walk = @import("../ast_walk.zig");
const TypeContext = @import("../type_context.zig").TypeContext;
const TypeInfo = @import("../zir_bridge.zig").TypeInfo;

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
    while (node < parent_map.len and depth < 64) : (depth += 1) {
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
                if (findAncestorFn(tags, parent_map, parent)) |fn_node| {
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
    const files = [_]import_resolver.File{
        .{ .path = "", .tree = tree },
    };
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

const ScopeRange = struct {
    first_token: u32,
    last_token: u32,

    fn span(self: ScopeRange) u32 {
        return self.last_token - self.first_token;
    }

    fn contains(self: ScopeRange, token: u32) bool {
        return token >= self.first_token and token <= self.last_token;
    }
};

const CallableInfo = struct {
    proto_node: u32,
    file_index: usize,
    implicit_self_count: usize,
};

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

    pub fn resolveExprType(self: ProjectTypeResolver, node: usize) ?ResolvedType {
        const tree = self.currentFile().tree;
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
        if (depth >= 64) return null;
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var node = expression;
        for (0..64) |_| {
            const parent = findParentNode(tree, node) orelse return null;
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
                    const function = findEnclosingFunction(tree, tags, token) orelse return null;
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
        return null;
    }

    fn resolveArgumentTypeAtNode(self: ProjectTypeResolver, call_node: u32, argument: u32, depth: u8) ?ResolvedTypeNode {
        if (depth >= 64) return null;
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
        const name = import_resolver.identifierName(self.currentFile().tree, node) orelse return null;
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

    pub fn isVerifiedImportBinding(
        self: ProjectTypeResolver,
        node: usize,
        import_path: []const u8,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        const declaration_node = self.resolveDeclarationNode(node) orelse return false;
        if (declaration_node >= tags.len or !import_resolver.isVarDeclTag(tags[declaration_node])) return false;
        const full = tree.fullVarDecl(@enumFromInt(declaration_node)) orelse return false;
        const init_node = full.ast.init_node.unwrap() orelse return false;
        const declared_path = import_resolver.importPathFromBuiltinCall(
            tree,
            @intFromEnum(init_node),
        ) orelse return false;
        return std.mem.eql(u8, declared_path, import_path);
    }

    fn resolveCallableAtCall(self: ProjectTypeResolver, call_node: u32) ?CallableInfo {
        return self.resolveCallableAtCallDepth(call_node, 0);
    }

    fn resolveCallableAtCallDepth(self: ProjectTypeResolver, call_node: u32, depth: u8) ?CallableInfo {
        if (depth >= 64) return null;
        const tree = self.currentFile().tree;
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

    fn implicitSelfCount(self: ProjectTypeResolver, proto_node: u32, receiver_type: ResolvedType) usize {
        const tree = self.currentFile().tree;
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
        if (isRootDeclNode(tree, node_index) and !resolver.varDeclIsTypeNamespace(full)) return null;
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
        var visited: [64]u32 = undefined;
        return self.isStdAllocatorExprVisited(node, &visited, 0);
    }

    fn isStdAllocatorExprVisited(
        self: ProjectTypeResolver,
        node: usize,
        visited: *[64]u32,
        depth: usize,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len or depth >= visited.len) return false;

        switch (tags[node]) {
            .field_access => {
                const access = tree.nodes.items(.data)[node].node_and_token;
                const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                if (!std.mem.eql(u8, member_name, "Allocator")) return false;
                return self.isStdMemExprVisited(@intFromEnum(access[0]), visited, depth);
            },
            .identifier => {
                const name = import_resolver.identifierName(tree, node) orelse return false;
                const declaration_node = self.findNearestBinding(name, node).declaration_node orelse return false;
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
        visited: *[64]u32,
        depth: usize,
    ) bool {
        if (depth >= visited.len) return false;
        if (std.mem.indexOfScalar(u32, visited[0..depth], declaration_node) != null) return false;
        visited[depth] = declaration_node;

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
        visited: *[64]u32,
        depth: usize,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len or depth >= visited.len) return false;

        switch (tags[node]) {
            .field_access => {
                const access = tree.nodes.items(.data)[node].node_and_token;
                const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                if (!std.mem.eql(u8, member_name, "mem")) return false;
                return self.isStdImportExprVisited(@intFromEnum(access[0]), visited, depth);
            },
            .identifier => {
                const name = import_resolver.identifierName(tree, node) orelse return false;
                const declaration_node = self.findNearestBinding(name, node).declaration_node orelse return false;
                return self.isStdMemBinding(declaration_node, visited, depth);
            },
            else => return false,
        }
    }

    fn isStdMemBinding(
        self: ProjectTypeResolver,
        declaration_node: u32,
        visited: *[64]u32,
        depth: usize,
    ) bool {
        if (depth >= visited.len) return false;
        if (std.mem.indexOfScalar(u32, visited[0..depth], declaration_node) != null) return false;
        visited[depth] = declaration_node;

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

    fn isStdImportExprVisited(
        self: ProjectTypeResolver,
        node: usize,
        visited: *[64]u32,
        depth: usize,
    ) bool {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len or depth >= visited.len) return false;
        if (tags[node] != .identifier) return false;

        const name = import_resolver.identifierName(tree, node) orelse return false;
        const declaration_node = self.findNearestBinding(name, node).declaration_node orelse return false;
        if (std.mem.indexOfScalar(u32, visited[0..depth], declaration_node) != null) return false;
        visited[depth] = declaration_node;

        if (declaration_node >= tags.len or !import_resolver.isVarDeclTag(tags[declaration_node])) return false;
        const full = tree.fullVarDecl(@enumFromInt(declaration_node)) orelse return false;
        const init_node = full.ast.init_node.unwrap() orelse return false;
        if (import_resolver.importPathFromBuiltinCall(tree, @intFromEnum(init_node))) |import_path| {
            return std.mem.eql(u8, import_path, "std");
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
                var visited: [64]u32 = undefined;
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
        visited: *[64]u32,
        depth: usize,
    ) ?ResolvedTypeNode {
        const tree = self.currentFile().tree;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len or depth >= visited.len) return null;

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
                return .{ .file_index = file_index };
            }
        }
        if (isThisBuiltinCall(tree, node)) {
            var enclosing: ?u32 = null;
            var smallest_span: usize = tree.tokens.len;
            const reference = tree.nodeMainToken(@enumFromInt(node));
            for (tree.nodes.items(.tag), 0..) |tag, index| {
                if (!isContainerTag(tag)) continue;
                const container: std.zig.Ast.Node.Index = @enumFromInt(index);
                const first = tree.firstToken(container);
                const last = tree.lastToken(container);
                if (reference < first or reference > last) continue;
                const span = @as(usize, last) - first;
                if (span >= smallest_span) continue;
                smallest_span = span;
                enclosing = @intCast(index);
            }
            return .{ .file_index = self.file_index, .container_node = enclosing };
        }
        return null;
    }

    fn resolveMemberType(self: ProjectTypeResolver, base_type: ResolvedType, member_name: []const u8) ?ResolvedType {
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

fn protoParamTypeNode(
    tree: *const std.zig.Ast,
    proto_node: u32,
    parameter_index: usize,
) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (proto_node >= tags.len) return null;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const params = switch (tags[proto_node]) {
        .fn_proto => tree.fnProto(@enumFromInt(proto_node)).ast.params,
        .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)).ast.params,
        .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(proto_node)).ast.params,
        .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)).ast.params,
        else => return null,
    };
    if (parameter_index >= params.len) return null;
    const parameter_node = @intFromEnum(params[parameter_index]);
    if (parameter_node >= tags.len) return null;
    if (import_resolver.isVarDeclTag(tags[parameter_node])) {
        const full = tree.fullVarDecl(@enumFromInt(parameter_node)) orelse return null;
        return @intFromEnum(full.ast.type_node.unwrap() orelse return null);
    }
    return parameter_node;
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

fn findAncestorFn(tags: []const std.zig.Ast.Node.Tag, parent_map: []const u32, start_node: u32) ?u32 {
    var node = start_node;
    var depth: u32 = 0;
    while (node < parent_map.len and depth < 64) : (depth += 1) {
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

fn nodeIsAncestor(ancestor: u32, descendant: u32, parent_map: []const u32) bool {
    if (ancestor == descendant) return true;
    var node = descendant;
    var depth: u32 = 0;
    while (node < parent_map.len and depth < 256) : (depth += 1) {
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
            try std.testing.expectEqualStrings("Good", good.type_name.?);
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
    const files = [_]import_resolver.File{
        .{ .path = "a.zig", .tree = &first },
        .{ .path = "b.zig", .tree = &second },
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
