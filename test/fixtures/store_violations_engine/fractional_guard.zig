const std = @import("std");

fn fractional(allocator: std.mem.Allocator, input: f64) !void {
    const value = input;
    if (value > 0) {
        if (value < 1) {
            const ptr = try allocator.alloc(u8, 1);
            allocator.free(ptr);
            allocator.free(ptr);
        }
    }
}

fn wideUnsigned(allocator: std.mem.Allocator, input: u64) !void {
    const value = input;
    if (value > 0) {
        if (value > 9223372036854775807) {
            const ptr = try allocator.alloc(u8, 1);
            allocator.free(ptr);
            allocator.free(ptr);
        }
    }
}

fn wideSigned(allocator: std.mem.Allocator, input: i128) !void {
    const value = input;
    if (value < 0) {
        if (value < -9223372036854775808) {
            const ptr = try allocator.alloc(u8, 1);
            allocator.free(ptr);
            allocator.free(ptr);
        }
    }
}

// EXPECT: line=9 rule=store-violations-engine severity=error message=double-free
// EXPECT: line=20 rule=store-violations-engine severity=error message=double-free
// EXPECT: line=31 rule=store-violations-engine severity=error message=double-free
