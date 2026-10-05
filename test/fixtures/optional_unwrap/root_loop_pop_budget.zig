// EXPECT: line=22 rule=optional-unwrap
// EXPECT: line=36 rule=optional-unwrap
//
// `while (cond) : (payload)` takes its body as an expression, and a loop is
// an expression, so the body is often a bare `while` or `for` rather than a
// block. A loop performs the removals it holds once per iteration, so no
// proved length bound covers how many elements it spends and the root has to
// be charged the way a loop nested inside a block body already is. A body
// that spends one element and holds no loop, and a loop that only empties a
// list of its own, spend nothing and keep the bound they really leave.
const std = @import("std");

const Row = struct {
    wrapped: bool = false,
};

/// The body is a bare `while` that empties the list, so the removal the
/// continue payload holds has nothing left to take, whatever length the
/// condition proved.
fn popAfterRootDrainLoopBody(items: *std.ArrayList(Row), again: bool) void {
    while (items.items.len > 3) : ({
        const row = items.pop().?;
        _ = row.wrapped;
    }) while (again) {
        if (items.items.len == 0) break;
        _ = items.pop();
        _ = items.pop();
        _ = items.pop();
    };
}

/// The same rule reached through a `for`: it reaches the removals it holds
/// again on every iteration, so the bound goes the same way.
fn popAfterRootDrainSweep(items: *std.ArrayList(Row)) void {
    while (items.items.len > 3) : ({
        const row = items.pop().?;
        _ = row.wrapped;
    }) for (items.items) |_| {
        _ = items.pop();
    };
}

/// The control: the same guard and the same payload over a body that spends a
/// single element and holds no loop. Four elements against a bound of four,
/// one spent by the body and one by the payload, so the forced `.?` never
/// meets an empty list.
fn popAfterSingleRemovalBody(items: *std.ArrayList(Row)) void {
    while (items.items.len > 3) : ({
        const row = items.pop().?;
        _ = row.wrapped;
    }) {
        _ = items.pop();
    }
}

/// The second control: the body is a bare loop as well, but every removal it
/// holds takes from a list of its own, so it spends nothing of this bound.
fn popAfterUnrelatedRootLoop(items: *std.ArrayList(Row), others: *std.ArrayList(Row), again: bool) void {
    while (items.items.len > 3) : ({
        const row = items.pop().?;
        _ = row.wrapped;
    }) while (again) {
        if (others.items.len == 0) break;
        _ = others.pop();
    };
}

/// The executable mirror of `popAfterRootDrainLoopBody`: the same guard, the
/// same bare-loop body and the same payload, with every removal null-checked
/// so the run stays finite and green. Returns how many removals met a list
/// that was already empty.
fn rootLoopDrainMisses(items: *std.ArrayList(Row), again: bool) usize {
    var misses: usize = 0;
    while (items.items.len > 3) : ({
        if (items.pop() == null) misses += 1;
    }) while (again) {
        if (items.items.len == 0) break;
        if (items.pop() == null) misses += 1;
        if (items.pop() == null) misses += 1;
        if (items.pop() == null) misses += 1;
    };
    return misses;
}

test "a bare-loop guard body empties the list before the payload removes from it" {
    var items: std.ArrayList(Row) = .empty;
    defer items.deinit(std.testing.allocator);
    try items.appendSlice(std.testing.allocator, &[_]Row{ .{}, .{}, .{}, .{} });

    // `again` is read off the live list and kept opaque, so the drain below
    // runs at run time instead of being folded away at comptime.
    var again: bool = items.items.len > 0;
    std.mem.doNotOptimizeAway(&again);
    try std.testing.expect(again);

    // One guard entry: the body takes three on its first pass, then takes the
    // last element and meets an empty list twice, so the payload's own
    // removal meets it a third time.
    try std.testing.expectEqual(@as(usize, 3), rootLoopDrainMisses(&items, again));
    try std.testing.expect(items.pop() == null);
}

test "the bodies that stay quiet really do stay inside their bound" {
    var items: std.ArrayList(Row) = .empty;
    defer items.deinit(std.testing.allocator);
    try items.appendSlice(std.testing.allocator, &[_]Row{ .{}, .{}, .{}, .{} });

    var before: usize = items.items.len;
    std.mem.doNotOptimizeAway(&before);

    popAfterSingleRemovalBody(&items);
    try std.testing.expectEqual(before - 2, items.items.len);

    var kept: std.ArrayList(Row) = .empty;
    defer kept.deinit(std.testing.allocator);
    try kept.appendSlice(std.testing.allocator, &[_]Row{ .{}, .{}, .{}, .{} });

    var others: std.ArrayList(Row) = .empty;
    defer others.deinit(std.testing.allocator);
    try others.appendSlice(std.testing.allocator, &[_]Row{ .{}, .{} });

    popAfterUnrelatedRootLoop(&kept, &others, true);
    try std.testing.expectEqual(@as(usize, 3), kept.items.len);
    try std.testing.expectEqual(@as(usize, 0), others.items.len);
}
