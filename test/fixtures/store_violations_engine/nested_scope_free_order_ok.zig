const std = @import("std");

fn foo(allocator: std.mem.Allocator) void {
    const ptr = allocator.alloc(u8, 1) catch unreachable;
    {
        const inner = allocator.alloc(u8, 1) catch unreachable;
        allocator.free(inner);
    }
    allocator.free(ptr);
}

// EXPECT: none
