const std = @import("std");

/// A user type that only looks like the standard arena. Nothing here was
/// imported, so its `init` is not the standard constructor and its `deinit` is
/// not an arena release: the block below stays this function's to free.
const FakeArena = struct {
    backing: std.mem.Allocator,

    fn init(gpa: std.mem.Allocator) FakeArena {
        return .{ .backing = gpa };
    }

    fn allocator(self: *FakeArena) std.mem.Allocator {
        return self.backing;
    }

    fn deinit(self: *FakeArena) void {
        _ = self;
    }
};

/// A namespace of this file's own, spelled like the standard one. Reaching
/// `ArenaAllocator` through it names the type above, not the standard arena:
/// the import identity behind it is not `@import("std")`, so a constructor
/// written that way proves nothing either.
const fake_std = struct {
    const heap = struct {
        const ArenaAllocator = FakeArena;
    };
};

fn fakeArenaInitIsNotAnArena(gpa: std.mem.Allocator) !void {
    var arena = FakeArena.init(gpa);
    defer arena.deinit();
    const allocator = arena.allocator();
    const buf = try allocator.alloc(u8, 8);
    buf[0] = 'a';
}

fn fakeNamespaceIsNotStd(gpa: std.mem.Allocator) !void {
    var arena = fake_std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const allocator = arena.allocator();
    const buf = try allocator.alloc(u8, 8);
    buf[0] = 'b';
}

// EXPECT: line=36 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=44 rule=store-violations-engine severity=error message=resource leak
