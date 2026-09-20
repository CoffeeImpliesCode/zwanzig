const std = @import("std");
const ids = @import("../ids.zig");
const Diagnostic = @import("../diagnostic.zig").Diagnostic;
const Rule = @import("../rule.zig").Rule;
const RuleError = @import("../rule.zig").RuleError;
const Source = @import("../source.zig").Source;
const VarResolver = @import("../engine/var_resolver.zig").VarResolver;

/// Rule that detects unused function parameters.
///
/// Parameters prefixed with '_' are ignored (explicitly unused).
/// Parameters used only in type annotations (e.g., `comptime T: type` used in
/// other parameter types or return type) are considered used.
pub const UnusedParameterRule = struct {
    pub const rule: Rule = .{
        .name = "unused-parameter",
        .default_severity = .warning,
        .checkFn = check,
    };

    fn check(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
    ) RuleError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        const token_tags = tree.tokens.items(.tag);

        for (tags, 0..) |tag, i| {
            if (tag != .fn_decl) continue;

            const node_idx: u32 = @intCast(i);
            const data = datas[node_idx].node_and_node;
            const proto_node = @intFromEnum(data[0]);
            const body_node = @intFromEnum(data[1]);
            if (proto_node == 0 or proto_node >= tags.len) continue;
            if (body_node == 0) continue;

            var resolver = try VarResolver.init(allocator, tree, ids.astId(node_idx));
            defer resolver.deinit();

            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const proto = switch (tags[proto_node]) {
                .fn_proto => tree.fnProto(@enumFromInt(proto_node)),
                .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)),
                .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(proto_node)),
                .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)),
                else => continue,
            };

            var it = proto.iterate(tree);
            while (it.next()) |param| {
                const name_tok = param.name_token orelse continue;
                if (name_tok >= token_tags.len or token_tags[name_tok] != .identifier) continue;

                const name = tree.tokenSlice(name_tok);
                if (shouldSkipName(name)) continue;

                const var_id = ids.varId(name_tok);
                if (isVarIdUsed(&resolver, var_id)) continue;

                const loc = try src.tokenLocation(name_tok);
                const message = try std.fmt.allocPrint(allocator, "Unused parameter '{s}'", .{name});
                defer allocator.free(message);

                const diag = try Diagnostic.initAtLocation(
                    allocator,
                    src.getFilePath(),
                    rule.name,
                    .warning,
                    message,
                    loc.line,
                    loc.column,
                );
                try diagnostics.append(allocator, diag);
            }
        }
    }

    fn shouldSkipName(name: []const u8) bool {
        if (name.len == 0) return true;
        if (name[0] == '_') return true;
        return false;
    }

    fn isVarIdUsed(resolver: *const VarResolver, var_id: ids.VarId) bool {
        var it = resolver.mappings.iterator();
        while (it.next()) |entry| {
            if (entry.value_ptr.* == var_id) return true;
        }
        return false;
    }
};

fn expectUnusedParameterDiagnostics(code: [:0]const u8, expected_name: []const u8) !void {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "skript-regression.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try UnusedParameterRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, expected_name) != null);
}

test "skript regression: tuple destructuring reads its source parameter" {
    const code: [:0]const u8 =
        \\fn unpack(payload: u32) u32 {
        \\    const low, const high = .{ payload & 0xff, payload >> 8 };
        \\    return low + high;
        \\}
        \\fn unsafeControl(actually_unused: u32) void {
        \\    _ = 0;
        \\}
    ;

    try expectUnusedParameterDiagnostics(code, "actually_unused");
}

test "skript regression: generic signatures use comptime parameters" {
    const code: [:0]const u8 =
        \\fn signatureOnly(comptime T: type, comptime op: fn (T) T) type {
        \\    _ = op;
        \\    return u8;
        \\}
        \\fn tupleType(comptime F: type) type {
        \\    return struct { F, F };
        \\}
        \\fn unsafeControl(comptime actually_unused: type) type {
        \\    return u8;
        \\}
    ;

    try expectUnusedParameterDiagnostics(code, "actually_unused");
}

test "shadowed parameter name still diagnoses the parameter" {
    const code: [:0]const u8 =
        \\fn shadowed(x: u32) u32 {
        \\    const x: u32 = 5;
        \\    return x;
        \\}
    ;

    try expectUnusedParameterDiagnostics(code, "x");
}

test "shadowed comptime parameter still diagnoses the parameter" {
    const code: [:0]const u8 =
        \\fn shadowedComptime(comptime T: type) type {
        \\    const T = u8;
        \\    return T;
        \\}
    ;

    try expectUnusedParameterDiagnostics(code, "T");
}
