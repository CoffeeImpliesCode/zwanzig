const std = @import("std");
const TypeContext = @import("../type_context.zig").TypeContext;
const import_resolver = @import("import_resolver.zig");
const call_resolver = @import("call_resolver.zig");

pub fn isAllocatorExpr(tree: *const std.zig.Ast, type_ctx: ?*TypeContext, expr_node: u32) bool {
    if (isAllocatorType(type_ctx, expr_node)) return true;
    if (isAllocatorName(tree, expr_node)) return true;
    if (isStdHeapAllocatorAccess(tree, expr_node)) return true;
    return false;
}

/// True when `expr_node` is a `std.heap.ArenaAllocator`.
///
/// Proved two ways, never from a name: the expression's own type is spelled
/// `std.heap.ArenaAllocator` behind at most `*`, `?` and `const`; or it is the
/// `std.heap.ArenaAllocator.init(...)` constructor written through a verified
/// `@import("std")` binding, the same proof `isKnownOpenBase` uses for
/// `std.posix` and `std.fs`. A binding is followed to its initializer because
/// what callers ask about is the `arena` in `defer arena.deinit()`, not the
/// call that produced it.
///
/// A local namespace spelled like `std.heap` fails the second proof, and a
/// different allocator that happens to be called an arena fails both.
pub fn isArenaAllocatorExpr(tree: *const std.zig.Ast, type_ctx: ?*TypeContext, expr_node: u32) bool {
    return isArenaExpr(tree, type_ctx, expr_node, arena_walk_frames);
}

/// Frames this walk may consume before it answers conservatively. The limit
/// bounds stack use; it is not evidence the arena is absent, so every exit at
/// the limit reports "not an arena".
const arena_walk_frames: u8 = 8;

fn isAllocatorType(type_ctx: ?*TypeContext, expr_node: u32) bool {
    const ctx = type_ctx orelse return false;
    const info = ctx.getExpressionType(expr_node) orelse return false;
    const type_str = info.type_str orelse return false;
    return isAllocatorTypeName(type_str);
}

fn isAllocatorTypeName(type_str: []const u8) bool {
    return std.mem.eql(u8, stripTypeDecorators(type_str), "std.mem.Allocator");
}

/// Type spelling without its leading indirection, optionality and
/// constness, which are how a declared type is written rather than which type
/// it names.
fn stripTypeDecorators(type_str: []const u8) []const u8 {
    var slice = type_str;
    while (slice.len > 0 and (slice[0] == '*' or slice[0] == '?')) {
        slice = slice[1..];
    }
    if (std.mem.startsWith(u8, slice, "const ")) {
        slice = slice["const ".len..];
    }
    return slice;
}

fn isAllocatorName(tree: *const std.zig.Ast, expr_node: u32) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const token_tags = tree.tokens.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);

    if (expr_node >= tags.len) return false;
    switch (tags[expr_node]) {
        .identifier => {
            const token = main_tokens[expr_node];
            if (token >= token_tags.len or token_tags[token] != .identifier) return false;
            const name = tree.tokenSlice(token);
            return std.mem.eql(u8, name, "allocator") or std.mem.endsWith(u8, name, "allocator");
        },
        .field_access => {
            const field_token = datas[expr_node].node_and_token[1];
            if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return false;
            const name = tree.tokenSlice(field_token);
            return std.mem.eql(u8, name, "allocator") or std.mem.endsWith(u8, name, "allocator");
        },
        else => return false,
    }
}

fn isStdHeapAllocatorAccess(tree: *const std.zig.Ast, expr_node: u32) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const token_tags = tree.tokens.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);

    if (expr_node >= tags.len or tags[expr_node] != .field_access) return false;
    const access = datas[expr_node].node_and_token;
    const field_token = access[1];
    if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return false;
    const field_name = tree.tokenSlice(field_token);
    if (!std.mem.endsWith(u8, field_name, "allocator")) return false;

    const base_node = @intFromEnum(access[0]);
    if (base_node >= tags.len or tags[base_node] != .field_access) return false;
    const base_access = datas[base_node].node_and_token;
    const base_field_token = base_access[1];
    if (base_field_token >= token_tags.len or token_tags[base_field_token] != .identifier) return false;
    if (!std.mem.eql(u8, tree.tokenSlice(base_field_token), "heap")) return false;

    const root_node = @intFromEnum(base_access[0]);
    if (root_node >= tags.len or tags[root_node] != .identifier) return false;
    const root_token = main_tokens[root_node];
    if (root_token >= token_tags.len or token_tags[root_token] != .identifier) return false;
    return std.mem.eql(u8, tree.tokenSlice(root_token), "std");
}

fn isArenaExpr(
    tree: *const std.zig.Ast,
    type_ctx: ?*TypeContext,
    expr_node: u32,
    depth: u8,
) bool {
    if (depth == 0) return false;
    if (hasArenaTypeName(type_ctx, expr_node)) return true;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (expr_node >= tags.len) return false;
    switch (tags[expr_node]) {
        .grouped_expression, .unwrap_optional => return isArenaExpr(tree, type_ctx, @intFromEnum(datas[expr_node].node_and_token[0]), depth - 1),
        .@"try" => return isArenaExpr(tree, type_ctx, @intFromEnum(datas[expr_node].node), depth - 1),
        .identifier => {
            const init = bindingInitializerNode(tree, type_ctx, expr_node) orelse return false;
            return isArenaExpr(tree, type_ctx, init, depth - 1);
        },
        .call, .call_comma, .call_one, .call_one_comma => return isArenaInitializer(tree, type_ctx, expr_node),
        else => return false,
    }
}

fn hasArenaTypeName(type_ctx: ?*TypeContext, expr_node: u32) bool {
    const ctx = type_ctx orelse return false;
    const info = ctx.getExpressionType(expr_node) orelse return false;
    const type_str = info.type_str orelse return false;
    return std.mem.eql(u8, stripTypeDecorators(type_str), "std.heap.ArenaAllocator");
}

fn bindingInitializerNode(
    tree: *const std.zig.Ast,
    type_ctx: ?*TypeContext,
    identifier_node: u32,
) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (identifier_node >= tags.len or tags[identifier_node] != .identifier) return null;
    const resolver = projectResolverFor(tree, type_ctx) orelse return null;
    const declaration = resolver.resolveDeclarationNode(identifier_node) orelse return null;
    const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return null;
    const init = full.ast.init_node.unwrap() orelse return null;
    return @intFromEnum(init);
}

/// `std.heap.ArenaAllocator.init(...)`. Only the constructor counts here; a
/// same-named method anywhere else proves nothing.
fn isArenaInitializer(
    tree: *const std.zig.Ast,
    type_ctx: ?*TypeContext,
    call_node: u32,
) bool {
    if (call_node >= tree.nodes.len) return false;
    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return false;
    const callee: u32 = @intFromEnum(call.ast.fn_expr);
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (callee >= tags.len or tags[callee] != .field_access) return false;
    const access = datas[callee].node_and_token;
    const member = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
    if (!std.mem.eql(u8, member, "init")) return false;
    const namespace = arenaNamespaceNode(tree, @intFromEnum(access[0])) orelse return false;
    if (import_resolver.importPathFromBuiltinCall(tree, namespace)) |path| {
        return std.mem.eql(u8, path, "std");
    }
    const resolver = projectResolverFor(tree, type_ctx) orelse return false;
    return resolver.isVerifiedImportBinding(namespace, "std");
}

/// The `std` node behind a spelled `std.heap.ArenaAllocator`, or null when the
/// expression names something else.
fn arenaNamespaceNode(tree: *const std.zig.Ast, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (node >= tags.len or tags[node] != .field_access) return null;
    const access = datas[node].node_and_token;
    const member = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
    if (!std.mem.eql(u8, member, "ArenaAllocator")) return null;
    const namespace: u32 = @intFromEnum(access[0]);
    if (namespace >= tags.len or tags[namespace] != .field_access) return null;
    const namespace_access = datas[namespace].node_and_token;
    const namespace_member = import_resolver.normalizeIdentifier(tree.tokenSlice(namespace_access[1]));
    if (!std.mem.eql(u8, namespace_member, "heap")) return null;
    return @intFromEnum(namespace_access[0]);
}

/// Resolver whose current file is `tree`, so an import proof taken in that file
/// answers about that file. Without a project file list there is nothing to
/// prove against, and the answer stays "not an arena".
fn projectResolverFor(
    tree: *const std.zig.Ast,
    type_ctx: ?*TypeContext,
) ?call_resolver.ProjectTypeResolver {
    const ctx = type_ctx orelse return null;
    const project = ctx.project_resolver orelse return null;
    if (project.files.len == 0) return null;
    for (project.files, 0..) |file, index| {
        if (file.tree == tree) {
            return call_resolver.ProjectTypeResolver{ .files = project.files, .file_index = index };
        }
    }
    return null;
}
