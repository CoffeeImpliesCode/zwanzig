const std = @import("std");
const cfg_mod = @import("cfg.zig");
const Cfg = cfg_mod.Cfg;
const CfgEdge = cfg_mod.CfgEdge;
const EdgeKind = cfg_mod.EdgeKind;
const IrNode = cfg_mod.IrNode;
const IrTag = cfg_mod.IrTag;
const ids = @import("ids.zig");
const diagnostic_mod = @import("diagnostic.zig");
const SourceRange = diagnostic_mod.SourceRange;
const Location = diagnostic_mod.Location;
const zir_bridge = @import("zir_bridge.zig");
const TypeInfo = zir_bridge.TypeInfo;

/// Magic bytes to identify cached artifact format.
const magic: [4]u8 = .{ 'Z', 'W', 'C', 'A' };

/// Current format version for cached artifacts.
/// Increment when the serialization format changes.
const format_version: u32 = 1;

/// Cached intermediate artifacts for a source file.
/// Contains CFGs for all functions and any other precomputed analysis data.
pub const CachedArtifacts = struct {
    allocator: std.mem.Allocator,
    /// CFGs for each function in the file, keyed by function AST node index.
    cfgs: std.AutoHashMap(u32, *Cfg),
    /// Whether ZIR/type info was available during caching.
    had_type_info: bool,

    pub fn init(allocator: std.mem.Allocator) CachedArtifacts {
        return .{
            .allocator = allocator,
            .cfgs = std.AutoHashMap(u32, *Cfg).init(allocator),
            .had_type_info = false,
        };
    }

    pub fn deinit(self: *CachedArtifacts) void {
        var iter = self.cfgs.valueIterator();
        while (iter.next()) |cfg_ptr| {
            destroyCfg(self.allocator, cfg_ptr.*);
        }
        self.cfgs.deinit();
    }

    /// Take ownership on success; leave the caller's CFG unchanged on failure.
    /// The CFG must be allocated with self.allocator and not already owned by this cache.
    /// Its borrowed function name is copied, and any previous CFG for the key is freed.
    pub fn addCfg(self: *CachedArtifacts, fn_ast_node: u32, cfg: *Cfg) !void {
        const owned_name = if (cfg.fn_name) |name| try self.allocator.dupe(u8, name) else null;
        errdefer if (owned_name) |name| self.allocator.free(name);

        const entry = try self.cfgs.getOrPut(fn_ast_node);
        if (entry.found_existing) {
            std.debug.assert(entry.value_ptr.* != cfg);
            destroyCfg(self.allocator, entry.value_ptr.*);
        }
        cfg.fn_name = owned_name;
        entry.value_ptr.* = cfg;
    }

    /// Get a CFG for a function by its AST node index.
    pub fn getCfg(self: *const CachedArtifacts, fn_ast_node: u32) ?*const Cfg {
        return self.cfgs.get(fn_ast_node);
    }

    /// Serialize artifacts to bytes.
    pub fn serialize(self: *const CachedArtifacts, allocator: std.mem.Allocator) ![]u8 {
        var buffer: std.ArrayList(u8) = .empty;
        errdefer buffer.deinit(allocator);

        try buffer.appendSlice(allocator, &magic);

        var version_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &version_bytes, format_version, .little);
        try buffer.appendSlice(allocator, &version_bytes);

        try buffer.append(allocator, if (self.had_type_info) 1 else 0);

        var cfg_count_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &cfg_count_bytes, @intCast(self.cfgs.count()), .little);
        try buffer.appendSlice(allocator, &cfg_count_bytes);

        var iter = self.cfgs.iterator();
        while (iter.next()) |entry| {
            const fn_node = entry.key_ptr.*;
            const cfg = entry.value_ptr.*;

            var fn_node_bytes: [4]u8 = undefined;
            std.mem.writeInt(u32, &fn_node_bytes, fn_node, .little);
            try buffer.appendSlice(allocator, &fn_node_bytes);

            try serializeCfg(cfg, allocator, &buffer);
        }

        return buffer.toOwnedSlice(allocator);
    }

    /// Deserialize artifacts from bytes.
    pub fn deserialize(allocator: std.mem.Allocator, data: []const u8) !CachedArtifacts {
        if (data.len < 9) {
            return error.InvalidFormat;
        }

        if (!std.mem.eql(u8, data[0..4], &magic)) {
            return error.InvalidFormat;
        }

        const version = std.mem.readInt(u32, data[4..8], .little);
        if (version != format_version) {
            return error.VersionMismatch;
        }

        var offset: usize = 8;
        const had_type_info = try deserializeBool(data, &offset);
        if (!hasBytes(data, offset, 4)) {
            return error.InvalidFormat;
        }

        const cfg_count = std.mem.readInt(u32, data[offset..][0..4], .little);
        offset += 4;

        var artifacts = CachedArtifacts.init(allocator);
        errdefer artifacts.deinit();

        artifacts.had_type_info = had_type_info;

        for (0..cfg_count) |_| {
            if (!hasBytes(data, offset, 4)) {
                return error.InvalidFormat;
            }

            const fn_node = std.mem.readInt(u32, data[offset..][0..4], .little);
            offset += 4;
            if (artifacts.cfgs.contains(fn_node)) return error.InvalidFormat;

            const cfg_result = try deserializeCfg(allocator, data, offset);
            errdefer destroyCfg(allocator, cfg_result.cfg);
            offset = cfg_result.new_offset;

            try artifacts.cfgs.putNoClobber(fn_node, cfg_result.cfg);
        }

        if (offset != data.len) return error.InvalidFormat;
        return artifacts;
    }

    /// Check if artifacts are valid/complete.
    pub fn isValid(self: *const CachedArtifacts) bool {
        return self.cfgs.count() > 0;
    }
};

fn destroyCfg(allocator: std.mem.Allocator, cfg: *Cfg) void {
    if (cfg.fn_name) |name| allocator.free(name);
    cfg.deinit();
    allocator.destroy(cfg);
}

fn hasBytes(data: []const u8, offset: usize, length: usize) bool {
    return offset <= data.len and length <= data.len - offset;
}

fn deserializeBool(data: []const u8, offset: *usize) !bool {
    if (!hasBytes(data, offset.*, 1)) return error.InvalidFormat;
    const value = data[offset.*];
    offset.* += 1;
    return switch (value) {
        0 => false,
        1 => true,
        else => error.InvalidFormat,
    };
}

fn deserializeEnum(comptime T: type, value: u8) !T {
    inline for (std.meta.fields(T)) |field| {
        if (value == field.value) return @enumFromInt(value);
    }
    return error.InvalidFormat;
}

fn serializeCfg(cfg: *const Cfg, allocator: std.mem.Allocator, buffer: *std.ArrayList(u8)) !void {
    var node_count_bytes: [4]u8 = undefined;
    std.mem.writeInt(u32, &node_count_bytes, @intCast(cfg.nodes.items.len), .little);
    try buffer.appendSlice(allocator, &node_count_bytes);

    for (cfg.nodes.items) |node| {
        try serializeIrNode(&node.ir_node, allocator, buffer);
    }

    var edge_count_bytes: [4]u8 = undefined;
    std.mem.writeInt(u32, &edge_count_bytes, @intCast(cfg.edges.items.len), .little);
    try buffer.appendSlice(allocator, &edge_count_bytes);

    for (cfg.edges.items) |edge| {
        try serializeEdge(&edge, allocator, buffer);
    }

    var entry_bytes: [4]u8 = undefined;
    std.mem.writeInt(u32, &entry_bytes, ids.cfgIndex(cfg.entry), .little);
    try buffer.appendSlice(allocator, &entry_bytes);

    var exit_bytes: [4]u8 = undefined;
    std.mem.writeInt(u32, &exit_bytes, ids.cfgIndex(cfg.exit), .little);
    try buffer.appendSlice(allocator, &exit_bytes);

    const has_fn_name: u8 = if (cfg.fn_name != null) 1 else 0;
    try buffer.append(allocator, has_fn_name);
    if (cfg.fn_name) |name| {
        var name_len_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &name_len_bytes, @intCast(name.len), .little);
        try buffer.appendSlice(allocator, &name_len_bytes);
        try buffer.appendSlice(allocator, name);
    }

    const has_fn_ast_node: u8 = if (cfg.fn_ast_node != null) 1 else 0;
    try buffer.append(allocator, has_fn_ast_node);
    if (cfg.fn_ast_node) |node_id| {
        var node_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &node_bytes, ids.astIndex(node_id), .little);
        try buffer.appendSlice(allocator, &node_bytes);
    }
}

fn serializeIrNode(node: *const IrNode, allocator: std.mem.Allocator, buffer: *std.ArrayList(u8)) !void {
    try buffer.append(allocator, @intFromEnum(node.tag));

    const has_ast_node: u8 = if (node.ast_node != null) 1 else 0;
    try buffer.append(allocator, has_ast_node);
    if (node.ast_node) |ast| {
        var ast_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &ast_bytes, ast, .little);
        try buffer.appendSlice(allocator, &ast_bytes);
    }

    const has_range: u8 = if (node.source_range != null) 1 else 0;
    try buffer.append(allocator, has_range);
    if (node.source_range) |range| {
        try serializeSourceRange(&range, allocator, buffer);
    }

    const has_operand: u8 = if (node.operand_node != null) 1 else 0;
    try buffer.append(allocator, has_operand);
    if (node.operand_node) |op| {
        var op_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &op_bytes, op, .little);
        try buffer.appendSlice(allocator, &op_bytes);
    }

    const has_operand2: u8 = if (node.operand2_node != null) 1 else 0;
    try buffer.append(allocator, has_operand2);
    if (node.operand2_node) |op| {
        var op_bytes: [4]u8 = undefined;
        std.mem.writeInt(u32, &op_bytes, op, .little);
        try buffer.appendSlice(allocator, &op_bytes);
    }

    const has_type: u8 = if (node.type_info != null) 1 else 0;
    try buffer.append(allocator, has_type);
    if (node.type_info) |ti| {
        try serializeTypeInfo(&ti, allocator, buffer);
    }
}

fn serializeSourceRange(range: *const SourceRange, allocator: std.mem.Allocator, buffer: *std.ArrayList(u8)) !void {
    var bytes: [16]u8 = undefined;
    std.mem.writeInt(u32, bytes[0..4], @intCast(range.start.line), .little);
    std.mem.writeInt(u32, bytes[4..8], @intCast(range.start.column), .little);
    std.mem.writeInt(u32, bytes[8..12], @intCast(range.end.line), .little);
    std.mem.writeInt(u32, bytes[12..16], @intCast(range.end.column), .little);
    try buffer.appendSlice(allocator, &bytes);
}

fn serializeEdge(edge: *const CfgEdge, allocator: std.mem.Allocator, buffer: *std.ArrayList(u8)) !void {
    var bytes: [9]u8 = undefined;
    std.mem.writeInt(u32, bytes[0..4], ids.cfgIndex(edge.from), .little);
    std.mem.writeInt(u32, bytes[4..8], ids.cfgIndex(edge.to), .little);
    bytes[8] = @intFromEnum(edge.kind);
    try buffer.appendSlice(allocator, &bytes);
}

fn serializeTypeInfo(ti: *const TypeInfo, allocator: std.mem.Allocator, buffer: *std.ArrayList(u8)) !void {
    try buffer.append(allocator, @intFromEnum(ti.kind));

    var size_bytes: [2]u8 = undefined;
    std.mem.writeInt(u16, &size_bytes, ti.size_bits, .little);
    try buffer.appendSlice(allocator, &size_bytes);

    const flags: u8 = (if (ti.is_signed) @as(u8, 1) else 0) | (if (ti.is_comptime) @as(u8, 2) else 0);
    try buffer.append(allocator, flags);
}

const DeserializeCfgResult = struct {
    cfg: *Cfg,
    new_offset: usize,
};

fn deserializeCfg(allocator: std.mem.Allocator, data: []const u8, start_offset: usize) !DeserializeCfgResult {
    var offset = start_offset;

    if (!hasBytes(data, offset, 4)) {
        return error.InvalidFormat;
    }
    const node_count = std.mem.readInt(u32, data[offset..][0..4], .little);
    offset += 4;

    const cfg = try allocator.create(Cfg);
    cfg.* = Cfg.init(allocator);
    errdefer destroyCfg(allocator, cfg);

    for (0..node_count) |i| {
        const node_result = try deserializeIrNode(data, offset);
        offset = node_result.new_offset;

        const idx = try cfg.addNode(node_result.node);
        std.debug.assert(ids.cfgIndex(idx) == @as(u32, @intCast(i)));
    }

    if (!hasBytes(data, offset, 4)) {
        return error.InvalidFormat;
    }
    const edge_count = std.mem.readInt(u32, data[offset..][0..4], .little);
    offset += 4;

    for (0..edge_count) |_| {
        const edge_result = try deserializeEdge(data, offset);
        offset = edge_result.new_offset;
        const edge = edge_result.edge;
        if (ids.cfgIndex(edge.from) >= node_count or ids.cfgIndex(edge.to) >= node_count) {
            return error.InvalidFormat;
        }
        try cfg.addEdgeWithKind(edge.from, edge.to, edge.kind);
    }

    if (!hasBytes(data, offset, 8)) {
        return error.InvalidFormat;
    }
    cfg.entry = ids.cfgId(std.mem.readInt(u32, data[offset..][0..4], .little));
    offset += 4;
    cfg.exit = ids.cfgId(std.mem.readInt(u32, data[offset..][0..4], .little));
    offset += 4;
    if (ids.cfgIndex(cfg.entry) >= node_count or ids.cfgIndex(cfg.exit) >= node_count) {
        return error.InvalidFormat;
    }

    if (try deserializeBool(data, &offset)) {
        if (!hasBytes(data, offset, 4)) {
            return error.InvalidFormat;
        }
        const name_len: usize = std.mem.readInt(u32, data[offset..][0..4], .little);
        offset += 4;

        if (!hasBytes(data, offset, name_len)) {
            return error.InvalidFormat;
        }
        cfg.fn_name = try allocator.dupe(u8, data[offset..][0..name_len]);
        offset += name_len;
    }

    if (try deserializeBool(data, &offset)) {
        if (!hasBytes(data, offset, 4)) {
            return error.InvalidFormat;
        }
        cfg.fn_ast_node = ids.astId(std.mem.readInt(u32, data[offset..][0..4], .little));
        offset += 4;
    }

    return .{
        .cfg = cfg,
        .new_offset = offset,
    };
}

const DeserializeIrNodeResult = struct {
    node: IrNode,
    new_offset: usize,
};

fn deserializeIrNode(data: []const u8, start_offset: usize) !DeserializeIrNodeResult {
    var offset = start_offset;

    if (!hasBytes(data, offset, 1)) {
        return error.InvalidFormat;
    }

    const tag = try deserializeEnum(IrTag, data[offset]);
    offset += 1;

    var node = IrNode.init(tag);

    if (try deserializeBool(data, &offset)) {
        if (!hasBytes(data, offset, 4)) {
            return error.InvalidFormat;
        }
        node.ast_node = std.mem.readInt(u32, data[offset..][0..4], .little);
        offset += 4;
    }

    if (try deserializeBool(data, &offset)) {
        const range_result = try deserializeSourceRange(data, offset);
        node.source_range = range_result.range;
        offset = range_result.new_offset;
    }

    if (try deserializeBool(data, &offset)) {
        if (!hasBytes(data, offset, 4)) {
            return error.InvalidFormat;
        }
        node.operand_node = std.mem.readInt(u32, data[offset..][0..4], .little);
        offset += 4;
    }

    if (try deserializeBool(data, &offset)) {
        if (!hasBytes(data, offset, 4)) {
            return error.InvalidFormat;
        }
        node.operand2_node = std.mem.readInt(u32, data[offset..][0..4], .little);
        offset += 4;
    }

    if (try deserializeBool(data, &offset)) {
        const ti_result = try deserializeTypeInfo(data, offset);
        node.type_info = ti_result.type_info;
        offset = ti_result.new_offset;
    }

    return .{
        .node = node,
        .new_offset = offset,
    };
}

const DeserializeSourceRangeResult = struct {
    range: SourceRange,
    new_offset: usize,
};

fn deserializeSourceRange(data: []const u8, start_offset: usize) !DeserializeSourceRangeResult {
    if (!hasBytes(data, start_offset, 16)) {
        return error.InvalidFormat;
    }

    const start_line = std.mem.readInt(u32, data[start_offset..][0..4], .little);
    const start_col = std.mem.readInt(u32, data[start_offset + 4 ..][0..4], .little);
    const end_line = std.mem.readInt(u32, data[start_offset + 8 ..][0..4], .little);
    const end_col = std.mem.readInt(u32, data[start_offset + 12 ..][0..4], .little);

    return .{
        .range = SourceRange.init(
            Location.init(start_line, start_col),
            Location.init(end_line, end_col),
        ),
        .new_offset = start_offset + 16,
    };
}

const DeserializeEdgeResult = struct {
    edge: CfgEdge,
    new_offset: usize,
};

fn deserializeEdge(data: []const u8, start_offset: usize) !DeserializeEdgeResult {
    if (!hasBytes(data, start_offset, 9)) {
        return error.InvalidFormat;
    }

    const from = ids.cfgId(std.mem.readInt(u32, data[start_offset..][0..4], .little));
    const to = ids.cfgId(std.mem.readInt(u32, data[start_offset + 4 ..][0..4], .little));
    const kind = try deserializeEnum(EdgeKind, data[start_offset + 8]);

    return .{
        .edge = CfgEdge.initWithKind(from, to, kind),
        .new_offset = start_offset + 9,
    };
}

const DeserializeTypeInfoResult = struct {
    type_info: TypeInfo,
    new_offset: usize,
};

fn deserializeTypeInfo(data: []const u8, start_offset: usize) !DeserializeTypeInfoResult {
    if (!hasBytes(data, start_offset, 4)) {
        return error.InvalidFormat;
    }

    const kind = try deserializeEnum(TypeInfo.TypeKind, data[start_offset]);
    const size_bits = std.mem.readInt(u16, data[start_offset + 1 ..][0..2], .little);
    const flags = data[start_offset + 3];
    if (flags & ~@as(u8, 3) != 0) return error.InvalidFormat;

    return .{
        .type_info = .{
            .kind = kind,
            .size_bits = size_bits,
            .is_signed = (flags & 1) != 0,
            .is_comptime = (flags & 2) != 0,
            .type_str = null,
        },
        .new_offset = start_offset + 4,
    };
}

test "CachedArtifacts: serialize and deserialize empty" {
    const allocator = std.testing.allocator;

    var artifacts = CachedArtifacts.init(allocator);
    defer artifacts.deinit();

    const serialized = try artifacts.serialize(allocator);
    defer allocator.free(serialized);

    var deserialized = try CachedArtifacts.deserialize(allocator, serialized);
    defer deserialized.deinit();

    try std.testing.expectEqual(false, deserialized.had_type_info);
    try std.testing.expectEqual(@as(usize, 0), deserialized.cfgs.count());
}

test "CachedArtifacts: serialize and deserialize with CFG" {
    const allocator = std.testing.allocator;

    const serialized = try serializeArtifactTestCfg(allocator);
    defer allocator.free(serialized);

    var deserialized = try CachedArtifacts.deserialize(allocator, serialized);
    defer deserialized.deinit();

    try std.testing.expectEqual(true, deserialized.had_type_info);
    try std.testing.expectEqual(@as(usize, 2), deserialized.cfgs.count());
    const unnamed_cfg = deserialized.getCfg(84) orelse return error.TestExpectedCfg;
    try std.testing.expect(unnamed_cfg.fn_name == null);
    try std.testing.expect(unnamed_cfg.fn_ast_node == null);

    const restored_cfg = deserialized.getCfg(42) orelse return error.TestExpectedCfg;
    try std.testing.expectEqualStrings("cached_function", restored_cfg.fn_name.?);
    try std.testing.expectEqual(ids.astId(42), restored_cfg.fn_ast_node.?);
    try std.testing.expectEqual(ids.cfgId(0), restored_cfg.entry);
    try std.testing.expectEqual(ids.cfgId(2), restored_cfg.exit);
    try std.testing.expectEqual(@as(usize, 3), restored_cfg.nodeCount());
    try std.testing.expectEqual(@as(usize, 2), restored_cfg.edgeCount());

    const restored_node = restored_cfg.getNode(ids.cfgId(1)) orelse return error.TestUnexpectedResult;
    const node = restored_node.ir_node;
    try std.testing.expectEqual(IrTag.var_decl, node.tag);
    try std.testing.expectEqual(@as(u32, 43), node.ast_node.?);
    try std.testing.expectEqual(@as(u32, 44), node.operand_node.?);
    try std.testing.expectEqual(@as(u32, 45), node.operand2_node.?);
    try std.testing.expectEqual(@as(usize, 2), node.source_range.?.start.line);
    try std.testing.expectEqual(@as(usize, 3), node.source_range.?.start.column);
    try std.testing.expectEqual(@as(usize, 4), node.source_range.?.end.line);
    try std.testing.expectEqual(@as(usize, 5), node.source_range.?.end.column);
    try std.testing.expectEqual(TypeInfo.TypeKind.int, node.type_info.?.kind);
    try std.testing.expectEqual(@as(u16, 32), node.type_info.?.size_bits);
    try std.testing.expect(node.type_info.?.is_signed);
    try std.testing.expect(node.type_info.?.is_comptime);
    try std.testing.expectEqual(EdgeKind.branch_true, restored_cfg.edges.items[0].kind);
    try std.testing.expectEqual(ids.cfgId(0), restored_cfg.edges.items[0].from);
    try std.testing.expectEqual(ids.cfgId(1), restored_cfg.edges.items[0].to);
}

test "CachedArtifacts: invalid format handling" {
    const allocator = std.testing.allocator;

    const result1 = CachedArtifacts.deserialize(allocator, "short");
    try std.testing.expectError(error.InvalidFormat, result1);

    const result2 = CachedArtifacts.deserialize(allocator, "BAD_magic_");
    try std.testing.expectError(error.InvalidFormat, result2);

    var bad_version = [_]u8{ 'Z', 'W', 'C', 'A', 99, 0, 0, 0, 0 };
    const result3 = CachedArtifacts.deserialize(allocator, &bad_version);
    try std.testing.expectError(error.VersionMismatch, result3);
}

test "CachedArtifacts: addCfg retains caller ownership on allocation failure" {
    const Harness = struct {
        fn run(allocator: std.mem.Allocator) !void {
            var artifacts = CachedArtifacts.init(allocator);
            defer artifacts.deinit();

            const cfg = try createArtifactTestCfg(allocator, "original_name");
            const original_name = cfg.fn_name orelse {
                cfg.deinit();
                allocator.destroy(cfg);
                return error.TestUnexpectedResult;
            };
            artifacts.addCfg(42, cfg) catch |err| {
                defer allocator.destroy(cfg);
                defer cfg.deinit();
                try std.testing.expect(cfg.fn_name.?.ptr == original_name.ptr);
                try std.testing.expectEqualStrings("original_name", cfg.fn_name.?);
                try std.testing.expectEqual(@as(usize, 3), cfg.nodeCount());
                try std.testing.expect(artifacts.getCfg(42) == null);
                return err;
            };

            try std.testing.expect(artifacts.getCfg(42).? == cfg);
            try std.testing.expect(cfg.fn_name.?.ptr != original_name.ptr);
            try std.testing.expectEqualStrings("original_name", cfg.fn_name.?);
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Harness.run, .{});
}

test "CachedArtifacts: replacement releases the old CFG only after success" {
    const Harness = struct {
        fn run(allocator: std.mem.Allocator) !void {
            var artifacts = CachedArtifacts.init(allocator);
            defer artifacts.deinit();

            const original = try createArtifactTestCfg(allocator, "original");
            artifacts.addCfg(42, original) catch |err| {
                original.deinit();
                allocator.destroy(original);
                return err;
            };

            const replacement = try createArtifactTestCfg(allocator, "replacement");
            const replacement_name = replacement.fn_name orelse {
                replacement.deinit();
                allocator.destroy(replacement);
                return error.TestUnexpectedResult;
            };
            replacement.nodes.items[1].ir_node.operand_node = 99;
            artifacts.addCfg(42, replacement) catch |err| {
                defer allocator.destroy(replacement);
                defer replacement.deinit();
                try std.testing.expect(artifacts.getCfg(42).? == original);
                try std.testing.expectEqualStrings("original", original.fn_name.?);
                try std.testing.expect(replacement.fn_name.?.ptr == replacement_name.ptr);
                return err;
            };

            const cached = artifacts.getCfg(42) orelse return error.TestUnexpectedResult;
            try std.testing.expectEqual(@as(usize, 1), artifacts.cfgs.count());
            try std.testing.expectEqualStrings("replacement", cached.fn_name.?);
            try std.testing.expectEqual(@as(u32, 99), cached.nodes.items[1].ir_node.operand_node.?);
        }
    };
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Harness.run, .{});
}

test "CachedArtifacts: deserialize releases partial CFGs on allocation failure" {
    const allocator = std.testing.allocator;
    const serialized = try serializeArtifactTestCfg(allocator);
    defer allocator.free(serialized);

    const Harness = struct {
        fn run(failing_allocator: std.mem.Allocator, data: []const u8) !void {
            var artifacts = try CachedArtifacts.deserialize(failing_allocator, data);
            defer artifacts.deinit();
            const cfg = artifacts.getCfg(42) orelse return error.TestExpectedCfg;
            try std.testing.expectEqualStrings("cached_function", cfg.fn_name.?);
            try std.testing.expectEqual(@as(usize, 3), cfg.nodeCount());
            const other = artifacts.getCfg(84) orelse return error.TestExpectedCfg;
            try std.testing.expect(other.fn_name == null);
            try std.testing.expectEqual(@as(usize, 2), other.edgeCount());
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Harness.run, .{serialized});
}

test "CachedArtifacts: deserialize rejects duplicate function keys without leaks" {
    const allocator = std.testing.allocator;
    const serialized = try serializeArtifactTestCfg(allocator);
    defer allocator.free(serialized);

    var duplicated: std.ArrayList(u8) = .empty;
    defer duplicated.deinit(allocator);
    try duplicated.appendSlice(allocator, serialized);
    try duplicated.appendSlice(allocator, serialized[13..]);
    std.mem.writeInt(u32, duplicated.items[9..13], 4, .little);

    try std.testing.checkAllAllocationFailures(
        allocator,
        expectInvalidArtifactData,
        .{@as([]const u8, duplicated.items)},
    );
}

test "CachedArtifacts: deserialize releases every truncated prefix" {
    const allocator = std.testing.allocator;
    const serialized = try serializeArtifactTestCfg(allocator);
    defer allocator.free(serialized);

    for (0..serialized.len) |length| {
        try expectInvalidArtifactData(allocator, serialized[0..length]);
    }
    try std.testing.checkAllAllocationFailures(
        allocator,
        expectInvalidArtifactData,
        .{serialized[0 .. serialized.len - 1]},
    );
}

test "CachedArtifacts: deserialize rejects trailing bytes and invalid header flags" {
    const allocator = std.testing.allocator;
    const serialized = try serializeArtifactTestCfg(allocator);
    defer allocator.free(serialized);

    const extended = try allocator.alloc(u8, serialized.len + 1);
    defer allocator.free(extended);
    @memcpy(extended[0..serialized.len], serialized);
    extended[serialized.len] = 0;
    try expectInvalidArtifactData(allocator, extended);

    serialized[8] = 2;
    try expectInvalidArtifactData(allocator, serialized);
}

test "CachedArtifacts: deserialize rejects invalid enum and flag bytes" {
    const invalid_node = [_]u8{ 255, 0, 0, 0, 0, 0 };
    try std.testing.expectError(error.InvalidFormat, deserializeIrNode(&invalid_node, 0));
    const invalid_presence = [_]u8{ @intFromEnum(IrTag.expr), 2, 0, 0, 0, 0 };
    try std.testing.expectError(error.InvalidFormat, deserializeIrNode(&invalid_presence, 0));
    const invalid_edge = [_]u8{ 0, 0, 0, 0, 0, 0, 0, 0, 255 };
    try std.testing.expectError(error.InvalidFormat, deserializeEdge(&invalid_edge, 0));
    const invalid_type = [_]u8{ 255, 0, 0, 0 };
    try std.testing.expectError(error.InvalidFormat, deserializeTypeInfo(&invalid_type, 0));
    const invalid_type_flags = [_]u8{ @intFromEnum(TypeInfo.TypeKind.int), 32, 0, 4 };
    try std.testing.expectError(error.InvalidFormat, deserializeTypeInfo(&invalid_type_flags, 0));
}

test "CachedArtifacts: deserialize rejects CFG indices outside the node array" {
    const allocator = std.testing.allocator;
    var artifacts = CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    const cfg = try createArtifactTestCfg(allocator, "indices");
    artifacts.addCfg(42, cfg) catch |err| {
        cfg.deinit();
        allocator.destroy(cfg);
        return err;
    };

    const indices = [_]*ids.CfgNodeId{
        &cfg.entry,
        &cfg.exit,
        &cfg.edges.items[0].from,
        &cfg.edges.items[0].to,
    };
    for (indices) |index| {
        const original = index.*;
        defer index.* = original;
        index.* = ids.cfgId(@intCast(cfg.nodeCount()));
        const serialized = try artifacts.serialize(allocator);
        defer allocator.free(serialized);
        try expectInvalidArtifactData(allocator, serialized);
    }
}

fn createArtifactTestCfg(allocator: std.mem.Allocator, name: []const u8) !*Cfg {
    const cfg = try allocator.create(Cfg);
    cfg.* = Cfg.init(allocator);
    errdefer {
        cfg.deinit();
        allocator.destroy(cfg);
    }

    cfg.entry = try cfg.addNode(IrNode.init(.fn_entry));
    var declaration = IrNode.initFull(
        .var_decl,
        43,
        SourceRange.init(Location.init(2, 3), Location.init(4, 5)),
    );
    declaration.operand_node = 44;
    declaration.operand2_node = 45;
    declaration.type_info = .{
        .kind = .int,
        .size_bits = 32,
        .is_signed = true,
        .is_comptime = true,
    };
    const body = try cfg.addNode(declaration);
    cfg.exit = try cfg.addNode(IrNode.init(.fn_exit));
    try cfg.addEdgeWithKind(cfg.entry, body, .branch_true);
    try cfg.addEdge(body, cfg.exit);
    cfg.fn_name = name;
    cfg.fn_ast_node = ids.astId(42);
    return cfg;
}

fn serializeArtifactTestCfg(allocator: std.mem.Allocator) ![]u8 {
    var artifacts = CachedArtifacts.init(allocator);
    defer artifacts.deinit();
    artifacts.had_type_info = true;
    const cfg = try createArtifactTestCfg(allocator, "cached_function");
    artifacts.addCfg(42, cfg) catch |err| {
        cfg.deinit();
        allocator.destroy(cfg);
        return err;
    };

    const unnamed = try createArtifactTestCfg(allocator, "");
    unnamed.fn_name = null;
    unnamed.fn_ast_node = null;
    artifacts.addCfg(84, unnamed) catch |err| {
        unnamed.deinit();
        allocator.destroy(unnamed);
        return err;
    };
    return artifacts.serialize(allocator);
}

fn expectInvalidArtifactData(allocator: std.mem.Allocator, data: []const u8) !void {
    var artifacts = CachedArtifacts.deserialize(allocator, data) catch |err| {
        if (err == error.InvalidFormat) return;
        return err;
    };
    defer artifacts.deinit();
    return error.TestExpectedInvalidFormat;
}
