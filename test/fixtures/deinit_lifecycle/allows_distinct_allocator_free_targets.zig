// EXPECT: none
const std = @import("std");

fn makeTable(allocator: std.mem.Allocator) ![]u8 {
    const table = try allocator.alloc(u8, 64);
    errdefer allocator.free(table);

    const pending = try allocator.alloc(u8, 64);
    defer allocator.free(pending);

    return table;
}
