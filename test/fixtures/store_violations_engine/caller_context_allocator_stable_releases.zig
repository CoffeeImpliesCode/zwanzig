// Zig 0.16.0 fixture: `std.process.Init` does not exist in Zig 0.15.2, which
// spells this fixture's directory access through `std.fs`.
const std = @import("std");

const Context = struct { pool: std.mem.Allocator };

/// Both helpers below allocate through a context field and hand back what they
/// build. They read that field and write nothing else, so a caller that keeps
/// the context it declared can leave them to the arena behind it - and can hand
/// the same context to one after the other without the second hand-off reading
/// as a write to it.
pub fn formatInsideContext(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

pub fn duplicateInsideContext(context: *const Context) error{OutOfMemory}!void {
    const value = try context.pool.dupe(u8, "data");
    std.debug.assert(std.mem.eql(u8, value, "data"));
}

fn countLabel(n: usize) usize {
    return n + 1;
}

pub fn main(init: std.process.Init) !void {
    var arena = std.heap.ArenaAllocator.init(init.gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };

    _ = countLabel(3);
    {
        // A binding of its own, declared where the context is but naming a
        // number. The write below lands in it, and the call that reads it
        // takes nothing but itself, so neither reaches the hand-off.
        var counter: usize = 0;
        counter += countLabel(4);
        std.debug.assert(counter == 5);
    }

    try formatInsideContext(&context);
    try duplicateInsideContext(&context);
}

// EXPECT: none
