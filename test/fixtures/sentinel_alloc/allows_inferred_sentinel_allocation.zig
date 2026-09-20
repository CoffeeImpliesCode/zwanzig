// EXPECT: none
const std = @import("std");

const File = struct {
    path: [:0]const u8,
};

fn open(allocator: std.mem.Allocator, path: []const u8) !File {
    const duped_path = try allocator.dupeZ(u8, path);
    errdefer allocator.free(duped_path);

    return .{ .path = duped_path };
}
