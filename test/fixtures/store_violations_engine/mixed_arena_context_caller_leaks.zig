const std = @import("std");

/// A verified binding for the standard library module: the arena below is
/// recognized through its own initializer, not through the spelling of the
/// namespace that reaches the constructor.
const verified_std = @import("std");

const Context = struct { pool: std.mem.Allocator };

fn formatInsideContext(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// One call site hands over an arena this caller disposes and the other hands
/// over a plain allocator. The first proves nothing by itself: a call site
/// that cannot be read settles nothing either, so the block stays reported.
fn mixedCaller(gpa: std.mem.Allocator) !void {
    var arena = verified_std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const owned: Context = .{ .pool = arena.allocator() };
    const borrowed: Context = .{ .pool = gpa };
    try formatInsideContext(&owned);
    try formatInsideContext(&borrowed);
}

// EXPECT: line=11 rule=store-violations-engine severity=error message=resource leak
