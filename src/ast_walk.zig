const std = @import("std");

const Ast = std.zig.Ast;
const log = std.log.scoped(.ast_walk);

/// Maximum number of block statements to process. Blocks exceeding this limit
/// will have guard detection truncated with a warning.
pub const max_block_statements = 64;

pub fn walk(
    comptime Visitor: type,
    tree: *const Ast,
    node: u32,
    visitor: *Visitor,
) @typeInfo(@TypeOf(Visitor.visit)).@"fn".return_type.? {
    const WalkError = @typeInfo(@TypeOf(Visitor.visit)).@"fn".return_type.?;

    if (visitor.stop) return;
    if (node == 0) return;

    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return;

    try visitor.visit(tree, node, tags[node]);
    if (visitor.stop) return;

    if (tree.fullSwitchCase(@enumFromInt(node))) |full_case| {
        for (full_case.ast.values) |value| {
            try walk(Visitor, tree, @intFromEnum(value), visitor);
            if (visitor.stop) return;
        }
        try walk(Visitor, tree, @intFromEnum(full_case.ast.target_expr), visitor);
        return;
    }

    const child = struct {
        fn visitChild(inner_tree: *const Ast, child_node: u32, inner_visitor: *Visitor) WalkError {
            return walk(Visitor, inner_tree, child_node, inner_visitor);
        }
    };

    try walkChildren(Visitor, tree, node, visitor, child.visitChild);
}

pub fn walkChildren(
    comptime Visitor: type,
    tree: *const Ast,
    node: u32,
    visitor: *Visitor,
    comptime child_fn: anytype,
) @typeInfo(@TypeOf(child_fn)).@"fn".return_type.? {
    if (node == 0) return;

    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return;

    if (tree.fullSwitchCase(@enumFromInt(node))) |full_case| {
        for (full_case.ast.values) |value| {
            try child_fn(tree, @intFromEnum(value), visitor);
            if (shouldStop(Visitor, visitor)) return;
        }
        try child_fn(tree, @intFromEnum(full_case.ast.target_expr), visitor);
        return;
    }

    const datas = tree.nodes.items(.data);

    switch (tags[node]) {
        .block, .block_semicolon => {
            const extra_range = datas[node].extra_range;
            const start = @intFromEnum(extra_range.start);
            const end = @intFromEnum(extra_range.end);
            const statements = tree.extra_data[start..end];
            for (statements) |stmt| {
                try child_fn(tree, stmt, visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            return;
        },
        .block_two, .block_two_semicolon => {
            const pair = datas[node].opt_node_and_opt_node;
            if (pair[0].unwrap()) |n| {
                try child_fn(tree, @intFromEnum(n), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (pair[1].unwrap()) |n| {
                try child_fn(tree, @intFromEnum(n), visitor);
            }
            return;
        },
        .fn_decl => {
            const body = @intFromEnum(datas[node].node_and_node[1]);
            if (body != 0) {
                try child_fn(tree, body, visitor);
            }
            return;
        },
        .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi => {
            var buf: [1]Ast.Node.Index = undefined;
            const proto = tree.fullFnProto(&buf, @enumFromInt(node)) orelse return;
            for (proto.ast.params) |param| {
                try child_fn(tree, @intFromEnum(param), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (proto.ast.return_type.unwrap()) |return_type| {
                try child_fn(tree, @intFromEnum(return_type), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (proto.ast.align_expr.unwrap()) |align_expr| {
                try child_fn(tree, @intFromEnum(align_expr), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (proto.ast.addrspace_expr.unwrap()) |addrspace_expr| {
                try child_fn(tree, @intFromEnum(addrspace_expr), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (proto.ast.section_expr.unwrap()) |section_expr| {
                try child_fn(tree, @intFromEnum(section_expr), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (proto.ast.callconv_expr.unwrap()) |callconv_expr| {
                try child_fn(tree, @intFromEnum(callconv_expr), visitor);
            }
            return;
        },
        .container_field, .container_field_init, .container_field_align => {
            const field = tree.fullContainerField(@enumFromInt(node)) orelse return;
            if (field.ast.type_expr.unwrap()) |type_expr| {
                try child_fn(tree, @intFromEnum(type_expr), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (field.ast.value_expr.unwrap()) |value_expr| {
                try child_fn(tree, @intFromEnum(value_expr), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (field.ast.align_expr.unwrap()) |align_expr| {
                try child_fn(tree, @intFromEnum(align_expr), visitor);
            }
            return;
        },
        .test_decl => {
            const body = @intFromEnum(datas[node].opt_token_and_node[1]);
            if (body != 0) {
                try child_fn(tree, body, visitor);
            }
            return;
        },
        .simple_var_decl, .local_var_decl, .global_var_decl, .aligned_var_decl => {
            const full = tree.fullVarDecl(@enumFromInt(node)) orelse return;
            if (full.ast.init_node.unwrap()) |init| {
                try child_fn(tree, @intFromEnum(init), visitor);
            }
            return;
        },
        .assign_destructure => {
            const destruct = tree.assignDestructure(@enumFromInt(node));
            try child_fn(tree, @intFromEnum(destruct.ast.value_expr), visitor);
            if (shouldStop(Visitor, visitor)) return;
            for (destruct.ast.variables) |variable| {
                try child_fn(tree, @intFromEnum(variable), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            return;
        },
        .@"if", .if_simple => {
            const full = tree.fullIf(@enumFromInt(node)) orelse return;
            try child_fn(tree, @intFromEnum(full.ast.cond_expr), visitor);
            if (shouldStop(Visitor, visitor)) return;
            try child_fn(tree, @intFromEnum(full.ast.then_expr), visitor);
            if (shouldStop(Visitor, visitor)) return;
            if (full.ast.else_expr.unwrap()) |else_node| {
                try child_fn(tree, @intFromEnum(else_node), visitor);
            }
            return;
        },
        .@"while", .while_simple, .while_cont => {
            const full = tree.fullWhile(@enumFromInt(node)) orelse return;
            try child_fn(tree, @intFromEnum(full.ast.cond_expr), visitor);
            if (shouldStop(Visitor, visitor)) return;
            try child_fn(tree, @intFromEnum(full.ast.then_expr), visitor);
            if (shouldStop(Visitor, visitor)) return;
            if (full.ast.else_expr.unwrap()) |else_node| {
                try child_fn(tree, @intFromEnum(else_node), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (full.ast.cont_expr.unwrap()) |cont| {
                try child_fn(tree, @intFromEnum(cont), visitor);
            }
            return;
        },
        .@"for", .for_simple => {
            const full = tree.fullFor(@enumFromInt(node)) orelse return;
            for (full.ast.inputs) |input| {
                try child_fn(tree, @intFromEnum(input), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            try child_fn(tree, @intFromEnum(full.ast.then_expr), visitor);
            if (shouldStop(Visitor, visitor)) return;
            if (full.ast.else_expr.unwrap()) |else_node| {
                try child_fn(tree, @intFromEnum(else_node), visitor);
            }
            return;
        },
        .call, .call_comma, .call_one, .call_one_comma => {
            var buf: [1]Ast.Node.Index = undefined;
            const full = tree.fullCall(&buf, @enumFromInt(node)) orelse return;
            try child_fn(tree, @intFromEnum(full.ast.fn_expr), visitor);
            if (shouldStop(Visitor, visitor)) return;
            for (full.ast.params) |param| {
                try child_fn(tree, @intFromEnum(param), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            return;
        },
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            var buf: [2]Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&buf, @enumFromInt(node)) orelse return;
            for (params) |param| {
                try child_fn(tree, @intFromEnum(param), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            return;
        },
        .struct_init,
        .struct_init_comma,
        .struct_init_one,
        .struct_init_one_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        => {
            var buf: [2]Ast.Node.Index = undefined;
            const struct_init = tree.fullStructInit(&buf, @enumFromInt(node)) orelse return;
            if (struct_init.ast.type_expr.unwrap()) |type_node| {
                try child_fn(tree, @intFromEnum(type_node), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            for (struct_init.ast.fields) |field| {
                try child_fn(tree, @intFromEnum(field), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            return;
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
            var buf: [2]Ast.Node.Index = undefined;
            const array_init = tree.fullArrayInit(&buf, @enumFromInt(node)) orelse return;
            if (array_init.ast.type_expr.unwrap()) |type_node| {
                try child_fn(tree, @intFromEnum(type_node), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            for (array_init.ast.elements) |elem| {
                try child_fn(tree, @intFromEnum(elem), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            return;
        },
        .@"switch", .switch_comma => {
            const full = tree.switchFull(@enumFromInt(node));
            try child_fn(tree, @intFromEnum(full.ast.condition), visitor);
            if (shouldStop(Visitor, visitor)) return;
            for (full.ast.cases) |case_node| {
                try child_fn(tree, @intFromEnum(case_node), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            return;
        },
        .@"return" => {
            if (datas[node].opt_node.unwrap()) |ret_node| {
                try child_fn(tree, @intFromEnum(ret_node), visitor);
            }
            return;
        },
        .@"break" => {
            if (datas[node].opt_token_and_opt_node[1].unwrap()) |break_node| {
                try child_fn(tree, @intFromEnum(break_node), visitor);
            }
            return;
        },
        .@"errdefer" => {
            const body = @intFromEnum(datas[node].opt_token_and_node[1]);
            if (body != 0) {
                try child_fn(tree, body, visitor);
            }
            return;
        },
        .for_range => {
            const pair = datas[node].node_and_opt_node;
            try child_fn(tree, @intFromEnum(pair[0]), visitor);
            if (shouldStop(Visitor, visitor)) return;
            if (pair[1].unwrap()) |end_node| {
                try child_fn(tree, @intFromEnum(end_node), visitor);
            }
            return;
        },
        .anyframe_type => {
            try child_fn(tree, @intFromEnum(datas[node].token_and_node[1]), visitor);
            return;
        },
        .ptr_type, .ptr_type_aligned, .ptr_type_sentinel, .ptr_type_bit_range => {
            const ptr_info = tree.fullPtrType(@enumFromInt(node)) orelse return;
            try child_fn(tree, @intFromEnum(ptr_info.ast.child_type), visitor);
            return;
        },
        .array_type, .array_type_sentinel => {
            const arr_type = tree.fullArrayType(@enumFromInt(node)) orelse return;
            const elem_count = @intFromEnum(arr_type.ast.elem_count);
            if (elem_count != 0) {
                try child_fn(tree, elem_count, visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (arr_type.ast.sentinel.unwrap()) |sentinel| {
                try child_fn(tree, @intFromEnum(sentinel), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            const elem_type = @intFromEnum(arr_type.ast.elem_type);
            if (elem_type != 0) {
                try child_fn(tree, elem_type, visitor);
            }
            return;
        },
        .slice, .slice_open, .slice_sentinel => {
            const slice = tree.fullSlice(@enumFromInt(node)) orelse return;
            const sliced = @intFromEnum(slice.ast.sliced);
            if (sliced != 0) {
                try child_fn(tree, sliced, visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            const start = @intFromEnum(slice.ast.start);
            if (start != 0) {
                try child_fn(tree, start, visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (slice.ast.end.unwrap()) |end_node| {
                try child_fn(tree, @intFromEnum(end_node), visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (slice.ast.sentinel.unwrap()) |sentinel_node| {
                try child_fn(tree, @intFromEnum(sentinel_node), visitor);
            }
            return;
        },
        .optional_type,
        .bool_not,
        .negation,
        .bit_not,
        .negation_wrap,
        .address_of,
        .@"try",
        .deref,
        .@"defer",
        .@"comptime",
        .@"nosuspend",
        .@"suspend",
        .@"resume",
        => {
            const child = @intFromEnum(datas[node].node);
            if (child != 0) {
                try child_fn(tree, child, visitor);
            }
            return;
        },
        .unwrap_optional, .grouped_expression, .field_access, .asm_input, .asm_simple => {
            const child = @intFromEnum(datas[node].node_and_token[0]);
            if (child != 0) {
                try child_fn(tree, child, visitor);
            }
            return;
        },
        .bool_and,
        .bool_or,
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
        .bang_equal,
        .equal_equal,
        .less_than,
        .greater_than,
        .less_or_equal,
        .greater_or_equal,
        .merge_error_sets,
        .mul,
        .div,
        .mod,
        .array_mult,
        .mul_wrap,
        .mul_sat,
        .add,
        .sub,
        .array_cat,
        .add_wrap,
        .sub_wrap,
        .add_sat,
        .sub_sat,
        .shl,
        .shl_sat,
        .shr,
        .bit_and,
        .bit_xor,
        .bit_or,
        .@"orelse",
        .@"catch",
        .error_union,
        .array_access,
        .switch_range,
        => {
            const pair = datas[node].node_and_node;
            const lhs = @intFromEnum(pair[0]);
            const rhs = @intFromEnum(pair[1]);
            if (lhs != 0) {
                try child_fn(tree, lhs, visitor);
                if (shouldStop(Visitor, visitor)) return;
            }
            if (rhs != 0) {
                try child_fn(tree, rhs, visitor);
            }
            return;
        },
        else => {},
    }
}

fn shouldStop(comptime Visitor: type, visitor: *Visitor) bool {
    if (@hasField(Visitor, "stop")) {
        return visitor.stop;
    }
    return false;
}

pub fn fillParentMap(tree: *const Ast, root: u32, parent_map: []u32) void {
    const tags = tree.nodes.items(.tag);
    if (root == 0 or root >= tags.len) return;
    fillParentMapInternal(tree, root, 0, parent_map);
}

/// Declaration-rooted links include container members but exclude detached
/// function signature subtrees. Seed order determines shared-node ownership.
pub fn buildDeclarationParentMap(allocator: std.mem.Allocator, tree: *const Ast) std.mem.Allocator.Error![]u32 {
    const tags = tree.nodes.items(.tag);
    const parents = try allocator.alloc(u32, tags.len);
    @memset(parents, 0);
    for (tags, 0..) |tag, node| {
        switch (tag) {
            .fn_decl,
            .test_decl,
            .simple_var_decl,
            .local_var_decl,
            .global_var_decl,
            .aligned_var_decl,
            => fillParentMap(tree, @intCast(node), parents),
            else => {},
        }
    }
    return parents;
}

fn fillParentMapInternal(tree: *const Ast, node: u32, parent: u32, parent_map: []u32) void {
    if (node == 0 or node >= tree.nodes.len) return;
    if (parent != 0 and node < parent_map.len and parent_map[node] == 0) {
        parent_map[node] = parent;
    }

    // Metadata needs container members; runtime visitors must not execute them.
    var container_buffer: [2]Ast.Node.Index = undefined;
    if (tree.fullContainerDecl(&container_buffer, @enumFromInt(node))) |container| {
        if (container.ast.arg.unwrap()) |arg| {
            fillParentMapInternal(tree, @intFromEnum(arg), node, parent_map);
        }
        for (container.ast.members) |member| {
            fillParentMapInternal(tree, @intFromEnum(member), node, parent_map);
        }
        return;
    }

    const Builder = struct {
        parent: u32,
        parent_map: []u32,

        fn child(ast: *const Ast, child_node: u32, self: *@This()) error{}!void {
            fillParentMapInternal(ast, child_node, self.parent, self.parent_map);
        }
    };
    var builder = Builder{ .parent = node, .parent_map = parent_map };
    // The child callback only writes indices and cannot fail.
    walkChildren(Builder, tree, node, &builder, Builder.child) catch unreachable;
}

/// Extract statements from a block node into a buffer.
/// Returns the number of statements, or null if the node is not a block.
pub fn getBlockStatements(
    tree: *const Ast,
    block: u32,
    stmts_buf: *[max_block_statements]u32,
) ?usize {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (block >= tags.len) return null;

    var stmt_count: usize = 0;

    switch (tags[block]) {
        .block, .block_semicolon => {
            const extra = datas[block].extra_range;
            const start: usize = @intFromEnum(extra.start);
            const end: usize = @intFromEnum(extra.end);
            const total_stmts = end - start;
            if (total_stmts > max_block_statements) {
                log.warn("block has {d} statements, exceeding limit of {d}; processing may be incomplete", .{ total_stmts, max_block_statements });
            }
            const len = @min(total_stmts, max_block_statements);
            for (0..len) |i| {
                stmts_buf[i] = tree.extra_data[start + i];
                stmt_count += 1;
            }
        },
        .block_two, .block_two_semicolon => {
            const opt_nodes = datas[block].opt_node_and_opt_node;
            if (opt_nodes[0].unwrap()) |n| {
                stmts_buf[stmt_count] = @intFromEnum(n);
                stmt_count += 1;
            }
            if (opt_nodes[1].unwrap()) |n| {
                stmts_buf[stmt_count] = @intFromEnum(n);
                stmt_count += 1;
            }
        },
        else => return null,
    }

    return stmt_count;
}

/// Check if ancestor_node is an ancestor of descendant_node using a parent map.
/// The parent map should be populated via `fillParentMap`.
pub fn isAncestor(ancestor_node: u32, descendant_node: u32, parent_map: []const u32) bool {
    if (ancestor_node == descendant_node) return true;

    var node = descendant_node;
    var depth: u32 = 0;
    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0) break;
        if (parent == ancestor_node) return true;
        node = parent;
    }
    return false;
}
