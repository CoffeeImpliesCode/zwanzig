// EXPECT: none
const std = @import("std");

const Bag = struct {
    items: std.ArrayList(u8),

    /// `deinit` is a method name, not an arena. Classifying this call as an
    /// arena release would take a release away from whatever really owns the
    /// memory behind `bag`.
    fn deinit(bag: *Bag) void {
        bag.items.deinit();
    }
};

fn userDeinitIsNotAnArenaRelease(gpa: std.mem.Allocator) void {
    var bag = Bag{ .items = .empty };
    defer bag.deinit();
    const buf = gpa.alloc(u8, 4) catch return;
    gpa.free(buf);
}
