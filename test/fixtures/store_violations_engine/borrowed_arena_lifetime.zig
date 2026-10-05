const std = @import("std");
const Allocator = std.mem.Allocator;

const Context = struct {
    arena: Allocator,
};

/// The context field is only named `arena`. What makes it an arena is the
/// `ArenaAllocator.init` the caller below reaches through a verified `std`
/// import; no name decides ownership here. The list and every slot behind it
/// belong to that arena, and this frame hands the list back without releasing
/// a single block of its own.
fn allocateInContext(ctx: *Context, count: usize) ![][]const u8 {
    const list = try ctx.arena.alloc([]const u8, count);
    for (list, 0..) |*slot, i| {
        slot.* = try std.fmt.allocPrint(ctx.arena, "entry-{d}", .{i});
    }
    return list;
}

/// An ordinary allocator nobody releases: this block carries a real free
/// obligation of its own and stays this function's to discharge.
pub fn unsafeLeak(gpa: Allocator) !void {
    const block = try gpa.alloc(u8, 32);
    block[0] = 0;
}

test "all context allocations are owned by the parent arena" {
    var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
    defer arena.deinit();
    var ctx = Context{ .arena = arena.allocator() };
    const items = try allocateInContext(&ctx, 4);
    try std.testing.expectEqual(@as(usize, 4), items.len);
}

// EXPECT: line=24 rule=store-violations-engine severity=error message=resource leak
