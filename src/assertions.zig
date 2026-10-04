const std = @import("std");
const ast_walk = @import("ast_walk.zig");
const LexicalIndex = @import("analysis/lexical_index.zig").LexicalIndex;

const AssertionKind = enum {
    boolean,
    equality,
};

pub const AssertionScope = struct {
    std_aliases: std.ArrayList([]const u8),
    testing_aliases: std.ArrayList([]const u8),
    debug_aliases: std.ArrayList([]const u8),

    /// Names bound to the real `std.debug.assert` function. A file that
    /// writes `const assert = std.debug.assert;` calls that function through
    /// an ordinary identifier, so the spelling of the callee no longer names
    /// the namespace it came from. These aliases are recorded together with
    /// the declaration they name, so a later local that shadows the alias,
    /// a rebound variable, or a same-named user function keeps the spelling
    /// without the assertion's effect.
    debug_assert_aliases: std.ArrayList(DebugAssertAlias),
    allow_bare: bool,

    pub const DebugAssertAlias = struct {
        /// The alias's own name.
        name: []const u8,
        /// The var decl that binds the name. A reference matches an alias
        /// only when it resolves to this very declaration, never by spelling.
        declaration_node: u32,
    };

    pub fn init(allocator: std.mem.Allocator) AssertionScope {
        _ = allocator;
        return .{
            .std_aliases = .empty,
            .testing_aliases = .empty,
            .debug_aliases = .empty,
            .debug_assert_aliases = .empty,
            .allow_bare = false,
        };
    }

    pub fn deinit(self: *AssertionScope, allocator: std.mem.Allocator) void {
        self.std_aliases.deinit(allocator);
        self.testing_aliases.deinit(allocator);
        self.debug_aliases.deinit(allocator);
        self.debug_assert_aliases.deinit(allocator);
    }

    fn hasStdAlias(self: *const AssertionScope, name: []const u8) bool {
        for (self.std_aliases.items) |alias| {
            if (std.mem.eql(u8, alias, name)) return true;
        }
        return false;
    }

    fn hasTestingAlias(self: *const AssertionScope, name: []const u8) bool {
        for (self.testing_aliases.items) |alias| {
            if (std.mem.eql(u8, alias, name)) return true;
        }
        return false;
    }

    fn hasDebugAlias(self: *const AssertionScope, name: []const u8) bool {
        for (self.debug_aliases.items) |alias| {
            if (std.mem.eql(u8, alias, name)) return true;
        }
        return false;
    }

    fn addStdAlias(self: *AssertionScope, allocator: std.mem.Allocator, name: []const u8) !void {
        if (self.hasStdAlias(name)) return;
        try self.std_aliases.append(allocator, name);
    }

    fn addTestingAlias(self: *AssertionScope, allocator: std.mem.Allocator, name: []const u8) !void {
        if (self.hasTestingAlias(name)) return;
        try self.testing_aliases.append(allocator, name);
    }

    fn addDebugAlias(self: *AssertionScope, allocator: std.mem.Allocator, name: []const u8) !void {
        if (self.hasDebugAlias(name)) return;
        try self.debug_aliases.append(allocator, name);
    }

    fn debugAssertAliasNames(self: *const AssertionScope, name: []const u8) bool {
        for (self.debug_assert_aliases.items) |alias| {
            if (std.mem.eql(u8, alias.name, name)) return true;
        }
        return false;
    }

    /// Does this reference name one of the recorded `std.debug.assert`
    /// aliases? The declaration is compared by identity, so a local that
    /// shadows the alias resolves to a different node and does not match.
    fn referencesDebugAssertAlias(
        self: *const AssertionScope,
        declaration_node: u32,
        name: []const u8,
    ) bool {
        if (!self.debugAssertAliasNames(name)) return false;
        for (self.debug_assert_aliases.items) |alias| {
            if (alias.declaration_node == declaration_node) return true;
        }
        return false;
    }

    fn addDebugAssertAlias(
        self: *AssertionScope,
        allocator: std.mem.Allocator,
        alias: DebugAssertAlias,
    ) !void {
        for (self.debug_assert_aliases.items) |existing| {
            if (existing.declaration_node == alias.declaration_node) return;
        }
        try self.debug_assert_aliases.append(allocator, alias);
    }
};

pub fn buildAssertionScope(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    fn_root: u32,
    allow_bare: bool,
) !AssertionScope {
    var scope = AssertionScope.init(allocator);
    errdefer scope.deinit(allocator);

    scope.allow_bare = allow_bare;

    try collectAliasesFromRoot(tree, allocator, &scope);
    if (fn_root != 0) {
        if (getFnBody(tree, fn_root)) |body_node| {
            try collectAliasesFromBody(tree, allocator, body_node, &scope);
        }
    }

    return scope;
}

fn isTestAssertionName(name: []const u8) bool {
    return std.mem.eql(u8, name, "expect") or
        std.mem.eql(u8, name, "expectEqual") or
        std.mem.eql(u8, name, "expectEqualStrings") or
        std.mem.eql(u8, name, "expectEqualSlices") or
        std.mem.eql(u8, name, "expectEqualDeep") or
        std.mem.eql(u8, name, "expectApproxEqAbs") or
        std.mem.eql(u8, name, "expectApproxEqRel") or
        std.mem.eql(u8, name, "expectError") or
        std.mem.eql(u8, name, "expectFmt") or
        std.mem.eql(u8, name, "assert");
}

pub fn constraintKindForName(name: []const u8) ?AssertionKind {
    if (std.mem.eql(u8, name, "expect") or std.mem.eql(u8, name, "assert")) {
        return .boolean;
    }
    if (std.mem.eql(u8, name, "expectEqual") or
        std.mem.eql(u8, name, "expectEqualStrings") or
        std.mem.eql(u8, name, "expectEqualSlices") or
        std.mem.eql(u8, name, "expectEqualDeep") or
        std.mem.eql(u8, name, "expectApproxEqAbs") or
        std.mem.eql(u8, name, "expectApproxEqRel"))
    {
        return .equality;
    }
    return null;
}

pub fn resolveAssertionName(
    tree: *const std.zig.Ast,
    fn_expr: std.zig.Ast.Node.Index,
    scope: *const AssertionScope,
) ?[]const u8 {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const fn_node = @intFromEnum(fn_expr);

    if (fn_node >= tags.len) return null;

    if (tags[fn_node] == .field_access) {
        const field_data = datas[fn_node].node_and_token;
        const field_token = field_data[1];
        const field_name = tree.tokenSlice(field_token);
        if (!isTestAssertionName(field_name)) return null;

        const base_node = @intFromEnum(field_data[0]);
        if (isTestingNamespace(tree, base_node, scope)) {
            return field_name;
        }
        return null;
    }

    if (tags[fn_node] == .identifier and scope.allow_bare) {
        const main_token = tree.nodes.items(.main_token)[fn_node];
        const name = tree.tokenSlice(main_token);
        if (isTestAssertionName(name)) return name;
    }

    return null;
}

/// The name of the assertion whose call proves a null check, or null when the
/// callee is not one. A `std.debug.assert` alias is accepted only when the
/// callee resolves to the very declaration the alias registered, so a
/// shadowing local, a rebound variable, and a same-named user function all
/// keep the spelling without the effect.
pub fn resolveDebugAssertionName(
    tree: *const std.zig.Ast,
    fn_expr: std.zig.Ast.Node.Index,
    scope: *const AssertionScope,
    lexical: ?*const LexicalIndex,
) ?[]const u8 {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const fn_node = @intFromEnum(fn_expr);

    if (fn_node >= tags.len) return null;

    if (tags[fn_node] == .identifier) {
        const index = lexical orelse return null;
        const token = tree.nodes.items(.main_token)[fn_node];
        if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return null;
        const binding = index.findBinding(tree.tokenSlice(token), token) orelse return null;
        const declaration = binding.node;
        if (declaration >= tags.len) return null;
        if (!isVarDeclTag(tags[declaration])) return null;

        const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return null;
        const name_token = full.ast.mut_token + 1;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
        const name = tree.tokenSlice(name_token);
        if (!scope.referencesDebugAssertAlias(declaration, name)) return null;
        return name;
    }

    if (tags[fn_node] != .field_access) return null;

    const field_data = datas[fn_node].node_and_token;
    const field_token = field_data[1];
    const field_name = tree.tokenSlice(field_token);
    if (!std.mem.eql(u8, field_name, "assert")) return null;

    const base_node = @intFromEnum(field_data[0]);
    if (isDebugNamespace(tree, base_node, scope)) {
        return field_name;
    }

    return null;
}

fn collectAliasesFromRoot(tree: *const std.zig.Ast, allocator: std.mem.Allocator, scope: *AssertionScope) !void {
    const tags = tree.nodes.items(.tag);

    for (tree.rootDecls()) |decl_idx| {
        const node = @intFromEnum(decl_idx);
        if (node >= tags.len) continue;
        if (!isVarDeclTag(tags[node])) continue;
        try addAliasFromVarDecl(tree, allocator, node, scope);
    }
}

fn collectAliasesFromBody(
    tree: *const std.zig.Ast,
    allocator: std.mem.Allocator,
    body_node: u32,
    scope: *AssertionScope,
) !void {
    var collector = VarDeclCollector{
        .allocator = allocator,
        .scope = scope,
    };
    try ast_walk.walk(VarDeclCollector, tree, body_node, &collector);
}

fn addAliasFromVarDecl(
    tree: *const std.zig.Ast,
    allocator: std.mem.Allocator,
    var_decl_node: u32,
    scope: *AssertionScope,
) !void {
    const tags = tree.nodes.items(.tag);
    const token_tags = tree.tokens.items(.tag);

    if (var_decl_node >= tags.len) return;
    if (!isVarDeclTag(tags[var_decl_node])) return;

    const full = tree.fullVarDecl(@enumFromInt(var_decl_node)) orelse return;
    const name_token = full.ast.mut_token + 1;
    if (name_token >= token_tags.len or token_tags[name_token] != .identifier) return;

    const name = tree.tokenSlice(name_token);
    const init = full.ast.init_node.unwrap() orelse return;
    const init_node = @intFromEnum(init);
    if (resolveAliasKind(tree, init_node, scope)) |kind| {
        switch (kind) {
            .std => try scope.addStdAlias(allocator, name),
            .testing => try scope.addTestingAlias(allocator, name),
            .debug => try scope.addDebugAlias(allocator, name),
        }
        return;
    }
    // `const assert = std.debug.assert;` binds the assertion function, not
    // the namespace that holds it, so it is recorded by the declaration it
    // names rather than as a namespace alias. Only a `const` binding keeps
    // that identity: a `var` may be rebound to another function before the
    // call, so its spelling then proves nothing.
    if (tree.tokenTag(full.ast.mut_token) != .keyword_const) return;
    if (resolvesToDebugAssert(tree, init_node, scope)) {
        try scope.addDebugAssertAlias(allocator, .{
            .name = name,
            .declaration_node = var_decl_node,
        });
    }
}

/// Does this initializer name the real `std.debug.assert` function? Only the
/// direct `std.debug.assert` access and a namespace alias of `std.debug`
/// count; an alias of a user `debug` namespace has no such identity.
fn resolvesToDebugAssert(
    tree: *const std.zig.Ast,
    init_node: u32,
    scope: *const AssertionScope,
) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (init_node >= tags.len) return false;
    if (tags[init_node] != .field_access) return false;

    const field_data = datas[init_node].node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(field_data[1]), "assert")) return false;
    return isDebugNamespace(tree, @intFromEnum(field_data[0]), scope);
}

fn resolveAliasKind(tree: *const std.zig.Ast, expr_node: u32, scope: *const AssertionScope) ?AliasKind {
    if (isStdNamespace(tree, expr_node, scope)) return .std;
    if (isTestingNamespace(tree, expr_node, scope)) return .testing;
    if (isDebugNamespace(tree, expr_node, scope)) return .debug;
    return null;
}

const AliasKind = enum {
    std,
    testing,
    debug,
};

fn isVarDeclTag(tag: std.zig.Ast.Node.Tag) bool {
    return tag == .simple_var_decl or
        tag == .local_var_decl or
        tag == .global_var_decl or
        tag == .aligned_var_decl;
}

fn getFnBody(tree: *const std.zig.Ast, fn_root: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (fn_root >= tags.len) return null;

    if (tags[fn_root] == .test_decl) {
        return @intFromEnum(datas[fn_root].opt_token_and_node[1]);
    }

    if (tags[fn_root] != .fn_decl) return null;
    return @intFromEnum(datas[fn_root].node_and_node[1]);
}

fn isTestingNamespace(tree: *const std.zig.Ast, node: u32, scope: *const AssertionScope) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (node >= tags.len) return false;

    if (tags[node] == .identifier) {
        const token = tree.nodes.items(.main_token)[node];
        const name = tree.tokenSlice(token);
        return scope.hasTestingAlias(name);
    }

    if (tags[node] == .field_access) {
        const data = datas[node].node_and_token;
        const field_token = data[1];
        const field_name = tree.tokenSlice(field_token);
        if (!std.mem.eql(u8, field_name, "testing")) return false;

        const base_node = @intFromEnum(data[0]);
        return isStdNamespace(tree, base_node, scope);
    }

    return false;
}

fn isDebugNamespace(tree: *const std.zig.Ast, node: u32, scope: *const AssertionScope) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (node >= tags.len) return false;

    if (tags[node] == .identifier) {
        const token = tree.nodes.items(.main_token)[node];
        const name = tree.tokenSlice(token);
        return scope.hasDebugAlias(name);
    }

    if (tags[node] == .field_access) {
        const data = datas[node].node_and_token;
        const field_token = data[1];
        const field_name = tree.tokenSlice(field_token);
        if (!std.mem.eql(u8, field_name, "debug")) return false;

        const base_node = @intFromEnum(data[0]);
        return isStdNamespace(tree, base_node, scope);
    }

    return false;
}

fn isStdNamespace(tree: *const std.zig.Ast, node: u32, scope: *const AssertionScope) bool {
    const tags = tree.nodes.items(.tag);
    const token_tags = tree.tokens.items(.tag);

    if (node >= tags.len) return false;

    if (tags[node] == .identifier) {
        const token = tree.nodes.items(.main_token)[node];
        const name = tree.tokenSlice(token);
        return std.mem.eql(u8, name, "std") or scope.hasStdAlias(name);
    }

    if (tags[node] == .builtin_call or tags[node] == .builtin_call_comma or
        tags[node] == .builtin_call_two or tags[node] == .builtin_call_two_comma)
    {
        const builtin_token = tree.nodes.items(.main_token)[node];
        if (builtin_token >= token_tags.len or token_tags[builtin_token] != .builtin) return false;
        const builtin_name = tree.tokenSlice(builtin_token);
        if (!std.mem.eql(u8, builtin_name, "@import")) return false;
        var buf: [2]std.zig.Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buf, @enumFromInt(node)) orelse return false;
        if (params.len < 1) return false;
        return isStringLiteralValue(tree, @intFromEnum(params[0]), "std");
    }

    return false;
}

fn isStringLiteralValue(tree: *const std.zig.Ast, node: u32, value: []const u8) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;

    switch (tags[node]) {
        .string_literal, .multiline_string_literal => {},
        else => return false,
    }

    const token = tree.nodes.items(.main_token)[node];
    const slice = tree.tokenSlice(token);
    if (slice.len < 2 or slice[0] != '"' or slice[slice.len - 1] != '"') return false;
    return std.mem.eql(u8, slice[1 .. slice.len - 1], value);
}

const VarDeclCollector = struct {
    allocator: std.mem.Allocator,
    scope: *AssertionScope,
    stop: bool = false,

    pub fn visit(self: *VarDeclCollector, tree: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
        if (isVarDeclTag(tag)) {
            try addAliasFromVarDecl(tree, self.allocator, node, self.scope);
        }
    }
};
