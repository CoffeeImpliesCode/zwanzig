const std = @import("std");

const Context = struct { pool: std.mem.Allocator };

/// The block below is charged to whoever owns the allocator this function
/// allocates through. This caller hands it a plain allocator: a plain
/// allocator disposes nothing and is handed back by nothing, so the block is
/// still this function's to free and is reported here.
fn formatInsideContext(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn ordinaryCaller(gpa: std.mem.Allocator) !void {
    const context: Context = .{ .pool = gpa };
    try formatInsideContext(&context);
}

// EXPECT: line=10 rule=store-violations-engine severity=error message=resource leak
