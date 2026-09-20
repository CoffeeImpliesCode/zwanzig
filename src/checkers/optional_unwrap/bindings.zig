const std = @import("std");
const lexical_index = @import("../../analysis/lexical_index.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");

/// Borrows source-owned syntax facts; guard queries allocate no additional index.
pub const QueryContext = struct {
    tree: *const std.zig.Ast,
    lexical: *const lexical_index.LexicalIndex,

    pub fn firstToken(self: *const QueryContext, node: u32) u32 {
        if (node < self.lexical.ranges.len) {
            const range = self.lexical.ranges[node];
            if (range.first_token <= range.last_token) return range.first_token;
        }
        return self.tree.firstToken(@enumFromInt(node));
    }

    pub fn lastToken(self: *const QueryContext, node: u32) u32 {
        if (node < self.lexical.ranges.len) {
            const range = self.lexical.ranges[node];
            if (range.first_token <= range.last_token) return range.last_token;
        }
        return self.tree.lastToken(@enumFromInt(node));
    }

    pub fn resolveIdentifierBinding(self: *const QueryContext, node: u32) ?u32 {
        const tree = self.tree;
        if (node >= tree.nodes.len or tree.nodeTag(@enumFromInt(node)) != .identifier) return null;
        const reference_token = tree.nodeMainToken(@enumFromInt(node));
        const name = import_resolver.normalizeIdentifier(tree.tokenSlice(reference_token));
        const reference_function = self.lexical.enclosingFunction(reference_token);
        var best: ?BindingCandidate = null;

        for (self.lexical.namedCandidates(name)) |candidate| {
            var scope = candidate.scope;
            var function = candidate.function;
            switch (candidate.kind) {
                .variable => {
                    if (candidate.is_root) {
                        function = null;
                    } else {
                        if (candidate.name_token > reference_token) continue;
                        if (self.lexical.scopes_by_token[candidate.name_token] == 0) continue;
                    }
                },
                .parameter => {
                    if (candidate.name_token > reference_token) continue;
                    // Guard bindings use the enclosing function even for nested
                    // function prototypes, rather than the prototype's range.
                    function = self.lexical.enclosingFunction(scope.first_token);
                    if (function != reference_function) continue;
                    if (function) |function_node| scope = self.lexical.ranges[function_node];
                },
                .function => continue,
            }
            considerCandidate(.{
                .name_token = candidate.name_token,
                .scope = scope,
                .function = function,
            }, reference_token, reference_function, &best);
        }

        const search = PayloadBindingSearch{
            .query = self,
            .name = name,
            .reference_token = reference_token,
            .reference_function = reference_function,
            .best = &best,
        };
        search.walkAncestors(node);
        return if (best) |candidate| candidate.name_token else null;
    }

    // Token scopes reconnect container members and detached prototypes.
    fn payloadParent(self: *const QueryContext, node: u32) ?u32 {
        if (self.lexical.parent(node)) |parent| return parent;
        const first = self.firstToken(node);
        if (first >= self.lexical.scopes_by_token.len) return null;
        const scope = self.lexical.scopes_by_token[first];
        if (scope == 0 or scope == node) return null;
        return if (self.lexical.ranges[scope].contains(self.lastToken(node))) scope else null;
    }
};

const BindingCandidate = struct {
    name_token: u32,
    scope: lexical_index.ScopeRange,
    function: ?u32,
};

fn considerCandidate(
    candidate: BindingCandidate,
    reference_token: u32,
    reference_function: ?u32,
    best: *?BindingCandidate,
) void {
    if (!candidate.scope.contains(reference_token)) return;
    if (candidate.function != null and candidate.function != reference_function) return;
    if (best.*) |previous| {
        if (candidate.scope.span() > previous.scope.span()) return;
        if (candidate.scope.span() == previous.scope.span() and candidate.name_token <= previous.name_token) return;
    }
    best.* = candidate;
}

const PayloadBindingSearch = struct {
    query: *const QueryContext,
    name: []const u8,
    reference_token: u32,
    reference_function: ?u32,
    best: *?BindingCandidate,

    fn walkAncestors(self: PayloadBindingSearch, node: u32) void {
        const tree = self.query.tree;
        var ancestor = node;
        while (self.query.payloadParent(ancestor)) |parent| {
            ancestor = parent;
            if (tree.fullSwitchCase(@enumFromInt(parent))) |full_case| {
                self.optional(full_case.payload_token, @intFromEnum(full_case.ast.target_expr));
                continue;
            }
            switch (tree.nodeTag(@enumFromInt(parent))) {
                .@"if", .if_simple => {
                    const full = tree.fullIf(@enumFromInt(parent)) orelse continue;
                    self.conditional(full);
                },
                .@"while", .while_simple, .while_cont => {
                    const full = tree.fullWhile(@enumFromInt(parent)) orelse continue;
                    self.conditional(full);
                },
                .@"for", .for_simple => {
                    const full = tree.fullFor(@enumFromInt(parent)) orelse continue;
                    self.forPayloads(full.payload_token, @intFromEnum(full.ast.then_expr));
                },
                .@"catch" => {
                    const catch_token = tree.nodeMainToken(@enumFromInt(parent));
                    if (catch_token + 2 >= tree.tokens.len or tree.tokenTag(catch_token + 1) != .pipe) continue;
                    const pair = tree.nodeData(@enumFromInt(parent)).node_and_node;
                    self.optional(catch_token + 2, @intFromEnum(pair[1]));
                },
                .@"errdefer" => {
                    const pair = tree.nodeData(@enumFromInt(parent)).opt_token_and_node;
                    self.optional(pair[0].unwrap(), @intFromEnum(pair[1]));
                },
                else => {},
            }
        }
    }

    fn optional(self: PayloadBindingSearch, payload_token: ?u32, body: u32) void {
        var token = payload_token orelse return;
        const tree = self.query.tree;
        const token_tags = tree.tokens.items(.tag);
        if (token < token_tags.len and token_tags[token] == .asterisk) token += 1;
        if (token >= token_tags.len or token_tags[token] != .identifier) return;
        if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(token)), self.name)) return;
        if (body == 0 or body >= self.query.lexical.ranges.len) return;
        considerCandidate(.{
            .name_token = token,
            .scope = self.query.lexical.ranges[body],
            .function = self.query.lexical.enclosingFunction(token),
        }, self.reference_token, self.reference_function, self.best);
    }

    fn conditional(self: PayloadBindingSearch, full: anytype) void {
        self.optional(full.payload_token, @intFromEnum(full.ast.then_expr));
        if (full.ast.else_expr.unwrap()) |else_node| {
            self.optional(full.error_token, @intFromEnum(else_node));
        }
    }

    fn forPayloads(self: PayloadBindingSearch, payload_token: u32, body: u32) void {
        const token_tags = self.query.tree.tokens.items(.tag);
        if (payload_token >= token_tags.len) return;
        var token = payload_token;
        if (token_tags[token] == .pipe) token += 1;
        if (token == 0 or token >= token_tags.len or token_tags[token - 1] != .pipe) return;
        if (token_tags[token] != .identifier and token_tags[token] != .asterisk) return;
        while (token < token_tags.len) : (token += 1) {
            if (token_tags[token] == .pipe) break;
            if (token_tags[token] == .asterisk) {
                token += 1;
                if (token >= token_tags.len) return;
            }
            if (token_tags[token] == .identifier) self.optional(token, body);
        }
    }
};

test "guard bindings preserve payload scopes and nested function boundaries" {
    const code: [:0]const u8 =
        \\const value: ?u8 = null;
        \\fn root() void { value.global(); }
        \\fn read(value: ?u8, optional: ?*?u8, items: []?u8, result: anyerror!?u8) void {
        \\    value.parameter();
        \\    if (optional) |*@"value"| {
        \\        value.if_payload();
        \\        { const value = optional; value.local(); }
        \\        @"value".if_after();
        \\    } else { value.if_else(); }
        \\    while (result) |value| { value.while_payload(); }
        \\    else |value| { value.while_error(); }
        \\    for (items, 0..) |*value, position| {
        \\        value.for_payload();
        \\        position.for_index();
        \\    }
        \\    result catch |value| value.catch_payload();
        \\    switch (choice) {
        \\        .first => |*value| value.switch_payload(),
        \\        else => value.switch_else(),
        \\    }
        \\    errdefer |value| value.errdefer_payload();
        \\    const Nested = struct { fn inner() void { value.nested(); } };
        \\    value.after();
        \\}
    ;
    const allocator = std.testing.allocator;
    var tree = try std.zig.Ast.parse(allocator, code, .zig);
    defer tree.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var lexical = try lexical_index.LexicalIndex.init(allocator, &tree);
    defer lexical.deinit(allocator);
    const query = QueryContext{ .tree = &tree, .lexical = &lexical };
    const Case = struct { member: []const u8, declaration: []const u8 };
    for ([_]Case{
        .{ .member = "global", .declaration = "value: ?u8 = null" },
        .{ .member = "parameter", .declaration = "value: ?u8, optional" },
        .{ .member = "if_payload", .declaration = "@\"value\"| {" },
        .{ .member = "local", .declaration = "value = optional" },
        .{ .member = "if_after", .declaration = "@\"value\"| {" },
        .{ .member = "if_else", .declaration = "value: ?u8, optional" },
        .{ .member = "while_payload", .declaration = "value| { value.while_payload" },
        .{ .member = "while_error", .declaration = "value| { value.while_error" },
        .{ .member = "for_payload", .declaration = "value, position|" },
        .{ .member = "for_index", .declaration = "position| {" },
        .{ .member = "catch_payload", .declaration = "value| value.catch_payload" },
        .{ .member = "switch_payload", .declaration = "value| value.switch_payload" },
        .{ .member = "switch_else", .declaration = "value: ?u8, optional" },
        .{ .member = "errdefer_payload", .declaration = "value| value.errdefer_payload" },
        .{ .member = "nested", .declaration = "value: ?u8 = null" },
        .{ .member = "after", .declaration = "value: ?u8, optional" },
    }) |case| {
        for (tree.nodes.items(.tag), 0..) |tag, node| {
            if (tag != .field_access) continue;
            const access = tree.nodeData(@enumFromInt(node)).node_and_token;
            if (!std.mem.eql(u8, tree.tokenSlice(access[1]), case.member)) continue;
            const binding = query.resolveIdentifierBinding(@intFromEnum(access[0])) orelse
                return error.TestUnexpectedResult;
            const expected = std.mem.indexOf(u8, code, case.declaration) orelse
                return error.TestUnexpectedResult;
            try std.testing.expectEqual(@as(u32, @intCast(expected)), tree.tokens.items(.start)[binding]);
            break;
        } else return error.TestUnexpectedResult;
    }
}
