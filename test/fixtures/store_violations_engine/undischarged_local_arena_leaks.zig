const std = @import("std");

/// A verified binding for the standard library module. The constructor below
/// is recognized through this binding's own initializer, with no written type
/// and no project file list to resolve it against.
const verified_std = @import("std");

/// Nothing disposes this arena and nothing hands it back, so what it holds is
/// still this function's to release when it returns. Knowing the arena does
/// not discharge it.
fn undrainedArenaLeaks(gpa: std.mem.Allocator) !void {
    var arena = verified_std.heap.ArenaAllocator.init(gpa);
    const allocator = arena.allocator();
    const buf = try allocator.alloc(u8, 8);
    buf[0] = 'a';
}

/// The binding is written over before the allocation, so the constructor it
/// was declared with says nothing about the value it holds by then. The
/// `deinit` below releases the second arena only; the first one is already
/// unreachable, and the block is reported all the same.
fn reassignedArenaProvesNothing(gpa: std.mem.Allocator) !void {
    var arena = verified_std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    arena = verified_std.heap.ArenaAllocator.init(gpa);
    const allocator = arena.allocator();
    const buf = try allocator.alloc(u8, 8);
    buf[0] = 'b';
}

// EXPECT: line=14 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=27 rule=store-violations-engine severity=error message=resource leak
