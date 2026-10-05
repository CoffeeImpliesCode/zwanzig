const std = @import("std");

const Context = struct { pool: std.mem.Allocator };

/// What this frame allocates is charged to whoever owns the allocator its
/// context carries. Every call site below reaches that field again after the
/// context was declared, so what the caller disposes is not what this block
/// comes from, and the block stays reported here.
fn formatInsideContext(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// Written over in place: the field the declaration put there holds a plain
/// allocator by the time the call reads it, and that allocator releases nothing.
fn replacedInPlace(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator() };
    context.pool = gpa;
    try formatInsideContext(&context);
}

/// Reached through a pointer: the same field, written from a binding the
/// declaration never mentions.
fn replacedThroughAPointer(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator() };
    const alias = &context;
    alias.pool = gpa;
    try formatInsideContext(&context);
}

/// Handed to a helper, which writes the field in its own frame.
fn replacePool(gpa: std.mem.Allocator, context: *Context) void {
    context.pool = gpa;
}

fn replacedByAHelper(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator() };
    replacePool(gpa, &context);
    try formatInsideContext(&context);
}

// EXPECT: line=10 rule=store-violations-engine severity=error message=resource leak
