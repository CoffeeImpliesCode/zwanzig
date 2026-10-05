// EXPECT: none
//
// A length bound proved by the enclosing condition covers every removal the
// guarded region performs first, so `len > a + 1 and len > b + 1` still proves
// a second pop and `len > 2` still proves a third. A conjunction proves the
// bound of the conjunct that has one.
const std = @import("std");
const Allocator = std.mem.Allocator;

const Row = struct {
    wrapped: bool = false,

    fn deinitRow(self: *Row, gpa: Allocator) void {
        _ = self;
        _ = gpa;
    }
};

fn popOnePerRow(gpa: Allocator, items: *std.ArrayList(Row), keep: usize) void {
    while (items.items.len > keep) {
        var row = items.pop().?;
        row.deinitRow(gpa);
    }
}

fn popGuarded(gpa: Allocator, items: *std.ArrayList(Row), floor: usize) void {
    if (items.items.len > floor + 1) {
        var row = items.pop().?;
        row.deinitRow(gpa);
    }
}

fn popTwice(gpa: Allocator, items: *std.ArrayList(Row), a: usize, b: usize) void {
    if (items.items.len > a + 1 and items.items.len > b + 1) {
        var first = items.pop().?;
        first.deinitRow(gpa);
        var second = items.pop().?;
        second.deinitRow(gpa);
    }
}

fn popThreeTimes(gpa: Allocator, items: *std.ArrayList(Row)) void {
    if (items.items.len > 2) {
        var first = items.pop().?;
        first.deinitRow(gpa);
        var second = items.pop().?;
        second.deinitRow(gpa);
        var third = items.pop().?;
        third.deinitRow(gpa);
    }
}

fn popInBoundedLoop(gpa: Allocator, items: *std.ArrayList(Row), budget: usize) void {
    var used: usize = 0;
    while (used < budget and items.items.len > 0) : (used += 1) {
        var row = items.pop().?;
        row.deinitRow(gpa);
    }
}
