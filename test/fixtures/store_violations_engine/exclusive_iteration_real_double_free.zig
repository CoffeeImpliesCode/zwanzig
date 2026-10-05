const std = @import("std");

/// A single iteration that releases the item it allocated and then releases
/// the same block again. Both frees name one allocation inside one iteration,
/// so the double free is real: stopping the analysis from reporting releases
/// across iterations must not make it blind to this one.
fn releasesTwice(gpa: std.mem.Allocator, items: []const usize) !void {
    for (items) |value| {
        const item = try std.fmt.allocPrint(gpa, "item-{d}", .{value});
        gpa.free(item);
        gpa.free(item);
    }
}

/// An allocation nothing releases. The leak has to keep being reported next
/// to the double free above.
fn losesAllocation(gpa: std.mem.Allocator) !void {
    _ = try gpa.alloc(u8, 8);
}

// EXPECT: line=11 rule=store-violations-engine severity=error message=double-free
// EXPECT: line=18 rule=store-violations-engine severity=error message=resource leak
