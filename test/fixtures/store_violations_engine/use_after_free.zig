const std = @import("std");

fn foo(allocator: std.mem.Allocator) !void {
    const ptr = try allocator.alloc(u8, 1);
    allocator.free(ptr);
    ptr[0] = 0;
}

// EXPECT: line=6 rule=store-violations-engine severity=error message=use after free
