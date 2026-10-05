// Zig 0.16.0 fixture: `std.process.Init` does not exist in Zig 0.15.2, which
// spells this fixture's directory access through `std.fs`.
const std = @import("std");
const Context = struct { pool: std.mem.Allocator };

pub fn formatInsideContext(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

pub fn nodeInsideContext(context: *const Context) error{OutOfMemory}!void {
    const value = try context.pool.create(usize);
    value.* = 42;
    std.debug.assert(value.* == 42);
}

pub fn duplicateInsideContext(context: *const Context) error{OutOfMemory}!void {
    const value = try context.pool.dupe(u8, "data");
    std.debug.assert(std.mem.eql(u8, value, "data"));
}

pub fn main(init: std.process.Init) !void {
    var arena = std.heap.ArenaAllocator.init(init.gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideContext(&context);
    try nodeInsideContext(&context);
    try duplicateInsideContext(&context);
}

// EXPECT: none
