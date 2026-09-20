const std = @import("std");
const compat = @import("../compat.zig");
const ast_walk = @import("../ast_walk.zig");
const import_resolver = @import("import_resolver.zig");
const call_resolver = @import("call_resolver.zig");

pub const ScopeRange = struct {
    first_token: u32,
    last_token: u32,

    pub fn span(self: ScopeRange) u32 {
        return self.last_token - self.first_token;
    }

    pub fn contains(self: ScopeRange, token: u32) bool {
        return token >= self.first_token and token <= self.last_token;
    }
};

pub const Candidate = struct {
    name: []const u8,
    scope: ScopeRange,
    node: u32,
    name_token: u32,
    function: ?u32 = null,
    is_root: bool = false,
    kind: enum { variable, parameter, function },
    order: usize = 0,
};

/// Immutable syntax facts. Names borrow the AST source, but no AST address is
/// retained. The source must outlive the index; semantic answers are not cached.
pub const LexicalIndex = struct {
    ranges: []const ScopeRange = &.{},
    parents: []const u32 = &.{},
    root_declarations: []const bool = &.{},
    scopes_by_token: []const u32 = &.{},
    functions_by_token: []const u32 = &.{},
    candidates: []const Candidate = &.{},
    names: std.StringHashMapUnmanaged(CandidateRange) = .empty,

    const CandidateRange = struct { start: usize, end: usize };

    pub fn init(allocator: std.mem.Allocator, tree: *const std.zig.Ast) !LexicalIndex {
        // Parser recovery can leave nodes that cannot be walked safely.
        if (tree.errors.len != 0) return .{};
        const ranges = try allocator.alloc(ScopeRange, tree.nodes.len);
        errdefer allocator.free(ranges);
        @memset(ranges, .{ .first_token = 1, .last_token = 0 });
        if (ranges.len != 0) ranges[0] = .{
            .first_token = 0,
            .last_token = if (tree.tokens.len == 0) 0 else @intCast(tree.tokens.len - 1),
        };
        for (1..tree.nodes.len) |node| {
            const first = tree.firstToken(@enumFromInt(node));
            const last = tree.lastToken(@enumFromInt(node));
            if (first <= last and last < tree.tokens.len) {
                ranges[node] = .{ .first_token = first, .last_token = last };
            }
        }

        const parents = try allocator.alloc(u32, tree.nodes.len);
        errdefer allocator.free(parents);
        @memset(parents, 0);
        for (1..tree.nodes.len) |node| {
            var builder = ParentBuilder{ .parent = @intCast(node), .ranges = ranges, .parents = parents };
            ast_walk.walkChildren(ParentBuilder, tree, @intCast(node), &builder, ParentBuilder.child) catch unreachable;
        }

        const root_declarations = try allocator.alloc(bool, tree.nodes.len);
        errdefer allocator.free(root_declarations);
        @memset(root_declarations, false);
        for (tree.rootDecls()) |node| root_declarations[@intFromEnum(node)] = true;

        const scopes = try tokenOwners(allocator, tree, ranges, .scope);
        errdefer allocator.free(scopes);
        const functions = try tokenOwners(allocator, tree, ranges, .function);
        errdefer allocator.free(functions);

        var index: LexicalIndex = .{
            .ranges = ranges,
            .parents = parents,
            .root_declarations = root_declarations,
            .scopes_by_token = scopes,
            .functions_by_token = functions,
            .candidates = &.{},
            .names = .empty,
        };
        errdefer index.names.deinit(allocator);
        var candidates: std.ArrayList(Candidate) = .empty;
        defer candidates.deinit(allocator);
        const tags = tree.nodes.items(.tag);
        for (tags, 0..) |tag, node| {
            if (!import_resolver.isVarDeclTag(tag)) continue;
            const full = tree.fullVarDecl(@enumFromInt(node)) orelse continue;
            const name_token = full.ast.mut_token + 1;
            if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
            try candidates.append(allocator, .{
                .name = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)),
                .scope = if (root_declarations[node]) ranges[0] else index.lexicalScope(name_token),
                .node = @intCast(node),
                .name_token = name_token,
                .function = index.enclosingFunction(name_token),
                .is_root = root_declarations[node],
                .kind = .variable,
                .order = candidates.items.len,
            });
        }
        for (tags, 0..) |tag, node| {
            const proto_node: u32 = switch (tag) {
                .fn_decl => @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]),
                .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi => @intCast(node),
                else => continue,
            };
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const proto = tree.fullFnProto(&buffer, @enumFromInt(proto_node)) orelse continue;
            const scope = ranges[node];
            if (scope.first_token > scope.last_token) continue;
            if (tag == .fn_decl) {
                if (proto.name_token) |name_token| {
                    if (name_token < tree.tokens.len and tree.tokenTag(name_token) == .identifier) {
                        try candidates.append(allocator, .{
                            .name = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)),
                            .scope = index.lexicalScope(tree.nodeMainToken(@enumFromInt(proto_node))),
                            .node = proto_node,
                            .name_token = name_token,
                            .kind = .function,
                            .order = candidates.items.len,
                        });
                    }
                }
            }
            for (proto.ast.params) |param| {
                const parameter_node = @intFromEnum(param);
                const name_token: u32 = if (tree.fullVarDecl(param)) |full|
                    full.ast.mut_token + 1
                else
                    @intCast(import_resolver.paramNameTokenBeforeType(tree, parameter_node) orelse continue);
                if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
                if (tree.fullVarDecl(param)) |full| {
                    if (full.ast.type_node == .none) continue;
                }
                try candidates.append(allocator, .{
                    .name = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)),
                    .scope = scope,
                    .node = parameter_node,
                    .name_token = name_token,
                    .function = if (tag == .fn_decl) @intCast(node) else null,
                    .kind = .parameter,
                    .order = candidates.items.len,
                });
            }
        }
        std.mem.sort(Candidate, candidates.items, {}, candidateLessThan);
        var start: usize = 0;
        while (start < candidates.items.len) {
            const name = candidates.items[start].name;
            var end = start + 1;
            while (end < candidates.items.len and std.mem.eql(u8, name, candidates.items[end].name)) : (end += 1) {}
            try index.names.put(allocator, name, .{ .start = start, .end = end });
            start = end;
        }
        index.candidates = try candidates.toOwnedSlice(allocator);
        return index;
    }

    pub fn deinit(self: *LexicalIndex, allocator: std.mem.Allocator) void {
        self.names.deinit(allocator);
        allocator.free(self.candidates);
        allocator.free(self.functions_by_token);
        allocator.free(self.scopes_by_token);
        allocator.free(self.root_declarations);
        allocator.free(self.parents);
        allocator.free(self.ranges);
    }

    pub fn parent(self: *const LexicalIndex, node: u32) ?u32 {
        if (node >= self.parents.len or self.parents[node] == 0) return null;
        return self.parents[node];
    }

    pub fn enclosingFunction(self: *const LexicalIndex, token: u32) ?u32 {
        if (token >= self.functions_by_token.len or self.functions_by_token[token] == 0) return null;
        return self.functions_by_token[token];
    }

    pub fn lexicalScope(self: *const LexicalIndex, token: u32) ScopeRange {
        if (self.ranges.len == 0) return .{ .first_token = 0, .last_token = 0 };
        return self.ranges[if (token < self.scopes_by_token.len) self.scopes_by_token[token] else 0];
    }

    pub fn isRootDeclaration(self: *const LexicalIndex, node: usize) bool {
        return node < self.root_declarations.len and self.root_declarations[node];
    }

    pub fn namedCandidates(self: *const LexicalIndex, name: []const u8) []const Candidate {
        const range = self.names.get(name) orelse return &.{};
        return self.candidates[range.start..range.end];
    }

    pub fn findBinding(self: *const LexicalIndex, name: []const u8, token: u32) ?*const Candidate {
        const function = self.enclosingFunction(token);
        var best: ?*const Candidate = null;
        for (self.namedCandidates(name)) |*candidate| {
            if (candidate.kind == .function) continue;
            if (!candidate.is_root and candidate.name_token > token) continue;
            if (candidate.function != null and candidate.function != function) continue;
            if (!candidate.is_root and !candidate.scope.contains(token)) continue;
            if (best) |previous| {
                if (candidate.scope.span() > previous.scope.span()) continue;
                if (candidate.scope.span() == previous.scope.span() and candidate.name_token <= previous.name_token) continue;
            }
            best = candidate;
        }
        return best;
    }

    pub fn findFunction(self: *const LexicalIndex, name: []const u8, token: u32) ?u32 {
        var best: ?u32 = null;
        var best_span: u32 = std.math.maxInt(u32);
        for (self.namedCandidates(name)) |candidate| {
            if (candidate.kind != .function or !candidate.scope.contains(token)) continue;
            if (candidate.scope.span() >= best_span) continue;
            best = candidate.node;
            best_span = candidate.scope.span();
        }
        return best;
    }
};

fn candidateLessThan(_: void, a: Candidate, b: Candidate) bool {
    return switch (std.mem.order(u8, a.name, b.name)) {
        .lt => true,
        .gt => false,
        .eq => a.order < b.order,
    };
}

const ParentBuilder = struct {
    parent: u32,
    ranges: []const ScopeRange,
    parents: []u32,

    fn child(_: *const std.zig.Ast, node: u32, self: *ParentBuilder) error{}!void {
        if (node == 0 or node >= self.parents.len or node == self.parent or self.parents[node] != 0) return;
        const range = self.ranges[node];
        const parent_range = self.ranges[self.parent];
        if (parent_range.contains(range.first_token) and parent_range.contains(range.last_token)) {
            self.parents[node] = self.parent;
        }
    }
};

fn tokenOwners(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    ranges: []const ScopeRange,
    kind: enum { scope, function },
) ![]u32 {
    var nodes: std.ArrayList(u32) = .empty;
    defer nodes.deinit(allocator);
    for (tree.nodes.items(.tag), 0..) |tag, node| {
        const selected = switch (kind) {
            .function => tag == .fn_decl,
            .scope => switch (tag) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => true,
                else => call_resolver.isContainerTag(tag),
            },
        };
        if (selected and ranges[node].first_token <= ranges[node].last_token) try nodes.append(allocator, @intCast(node));
    }
    const Order = struct {
        fn start(context: []const ScopeRange, a: u32, b: u32) bool {
            return context[a].first_token < context[b].first_token;
        }

        fn smallest(context: []const ScopeRange, a: u32, b: u32) std.math.Order {
            const comparison = std.math.order(context[a].span(), context[b].span());
            return if (comparison == .eq) std.math.order(a, b) else comparison;
        }
    };
    std.mem.sort(u32, nodes.items, ranges, Order.start);
    const Queue: type = std.PriorityQueue(u32, []const ScopeRange, Order.smallest);
    var active = if (compat.frontend == .zig_0_16)
        Queue.initContext(ranges)
    else
        Queue.init(allocator, ranges);
    defer if (compat.frontend == .zig_0_16) active.deinit(allocator) else active.deinit();
    const owners = try allocator.alloc(u32, tree.tokens.len);
    errdefer allocator.free(owners);
    var next: usize = 0;
    for (owners, 0..) |*owner, token| {
        while (next < nodes.items.len and ranges[nodes.items[next]].first_token <= token) : (next += 1) {
            if (compat.frontend == .zig_0_16) {
                try active.push(allocator, nodes.items[next]);
            } else {
                try active.add(nodes.items[next]);
            }
        }
        while (active.peek()) |node| {
            if (ranges[node].last_token >= token) break;
            const removed = if (compat.frontend == .zig_0_16)
                active.pop() orelse @panic("lexical owner queue became empty after peek")
            else
                active.remove();
            std.debug.assert(removed == node);
        }
        owner.* = active.peek() orelse 0;
    }
    return owners;
}

test "lexical index leaves malformed trees inert" {
    const allocator = std.testing.allocator;
    var tree = try std.zig.Ast.parse(allocator,
        \\pub const Earlier = struct {};
        \\pub fn complete() void {}
        \\fn broken(
    , .zig);
    defer tree.deinit(allocator);
    try std.testing.expect(tree.errors.len != 0);

    var index = try LexicalIndex.init(allocator, &tree);
    defer index.deinit(allocator);
    try std.testing.expectEqual(@as(usize, 0), index.namedCandidates("Earlier").len);
    for (0..tree.nodes.len) |node| {
        try std.testing.expect(index.parent(@intCast(node)) == null);
        try std.testing.expect(!index.isRootDeclaration(node));
    }
    for (0..tree.tokens.len) |token| {
        try std.testing.expect(index.enclosingFunction(@intCast(token)) == null);
        try std.testing.expect(index.findBinding("Earlier", @intCast(token)) == null);
        try std.testing.expect(index.findFunction("complete", @intCast(token)) == null);
        const scope = index.lexicalScope(@intCast(token));
        try std.testing.expect(scope.first_token <= scope.last_token);
        try std.testing.expect(scope.last_token < tree.tokens.len);
    }
}

test "lexical index releases partial syntax and name indexes on allocation failure" {
    const allocator = std.testing.allocator;
    var tree = try std.zig.Ast.parse(allocator,
        \\const Later = struct {};
        \\fn run(value: Later) void {
        \\    { const value: Later = undefined; value.inner(); }
        \\    value.outer();
        \\}
    , .zig);
    defer tree.deinit(allocator);
    const Harness = struct {
        fn run(failing_allocator: std.mem.Allocator, ast: *const std.zig.Ast) !void {
            var index = try LexicalIndex.init(failing_allocator, ast);
            defer index.deinit(failing_allocator);
            for (ast.nodes.items(.tag), 0..) |tag, node| {
                if (tag != .field_access) continue;
                const receiver = ast.nodeData(@enumFromInt(node)).node_and_token[0];
                const token = ast.nodeMainToken(receiver);
                const binding = index.findBinding("value", token) orelse return error.MissingBinding;
                const method = ast.tokenSlice(ast.nodeData(@enumFromInt(node)).node_and_token[1]);
                try std.testing.expectEqual(std.mem.eql(u8, method, "inner"), binding.kind == .variable);
            }
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Harness.run, .{&tree});
}
