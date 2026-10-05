// EXPECT: none
const std = @import("std");

/// A second name for the same module. The arena built through it below is
/// recognized from this binding's own `@import("std")`, not from the spelling
/// of the namespace that reaches the constructor.
const verified_std = @import("std");

/// Disposing the arena releases everything allocated through it. The arena
/// type is written out here, which is the other proof of arena-ness.
fn disposedArenaReleases(gpa: std.mem.Allocator) !void {
    var arena: std.heap.ArenaAllocator = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const allocator = arena.allocator();
    const buf = try allocator.alloc(u8, 8);
    buf[0] = 'a';
}

/// Handing the arena back transfers what it holds, so an arena built without a
/// written type through the verified import is released that way too. The
/// allocator is taken once and used under its own name: what the allocation
/// runs through is the alias, and the arena behind it is still the owner.
fn returnedArenaTransfers(gpa: std.mem.Allocator) !std.heap.ArenaAllocator {
    var arena = verified_std.heap.ArenaAllocator.init(gpa);
    const allocator = arena.allocator();
    const buf = try allocator.alloc(u8, 8);
    buf[0] = 'a';
    return arena;
}
