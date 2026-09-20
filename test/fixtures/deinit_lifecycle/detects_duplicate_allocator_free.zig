// EXPECT: line=6 rule=deinit-lifecycle severity=warning message=both defer and errdefer
const std = @import("std");

fn makeBuffer(allocator: std.mem.Allocator) ![]u8 {
    const buffer = try allocator.alloc(u8, 64);
    errdefer allocator.free(buffer);
    defer allocator.free(buffer);
    return error.Failed;
}
