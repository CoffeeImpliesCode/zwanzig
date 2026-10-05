// EXPECT: line=23 rule=optional-unwrap
// EXPECT: line=34 rule=optional-unwrap
//
// The proved bound is spent one element per removal the guarded region
// performs before the unwrap, and a loop performs its removals once per
// iteration. A body that drains the list first therefore spends the whole
// bound, however large the enclosing condition proved it, while a loop over
// a list of its own spends nothing and a body that removes one element per
// pass stays inside a bound that proves it.
const std = @import("std");

const Row = struct {
    wrapped: bool = false,
};

/// The inner loop empties the list, so the removal after it has nothing
/// left to take, whatever length the enclosing condition proved.
fn popAfterDrainingLoop(items: *std.ArrayList(Row), floor: usize) void {
    while (items.items.len > floor) {
        while (items.items.len > 0) {
            _ = items.pop();
        }
        const row = items.pop().?;
        _ = row.wrapped;
    }
}

/// The same drain written as a `for`, in a generic body.
fn popAfterDrainingSweep(comptime T: type, items: *std.ArrayList(T), floor: usize) void {
    while (items.items.len > floor) {
        for (items.items) |_| {
            _ = items.pop();
        }
        const last = items.pop().?;
        _ = last;
    }
}

/// A loop over a list of its own takes nothing from this one, so the bound
/// still covers the removal that follows it.
fn popAfterUnrelatedSweep(items: *std.ArrayList(Row), others: *std.ArrayList(Row)) void {
    if (items.items.len > 0) {
        for (others.items) |row| {
            _ = row.wrapped;
        }
        const row = items.pop().?;
        _ = row.wrapped;
    }
}

/// Three removals, and a bound that proves a third element.
fn popThreeUnderBound(items: *std.ArrayList(Row)) void {
    if (items.items.len > 2) {
        const first = items.pop().?;
        const second = items.pop().?;
        const third = items.pop().?;
        _ = first.wrapped;
        _ = second.wrapped;
        _ = third.wrapped;
    }
}

/// One removal per pass, with the condition read again before each of them.
fn popWhileAbove(comptime T: type, items: *std.ArrayList(T), keep: usize) usize {
    var removed: usize = 0;
    while (items.items.len > keep) {
        const last = items.pop().?;
        removed += 1;
        _ = last;
    }
    return removed;
}

test "the removals that stay quiet really do stay inside their bound" {
    var gpa_state = std.heap.DebugAllocator(.{}){};
    defer _ = gpa_state.deinit();
    const gpa = gpa_state.allocator();

    var rows: std.ArrayList(Row) = .empty;
    defer rows.deinit(gpa);
    try rows.appendSlice(gpa, &[_]Row{ .{}, .{}, .{}, .{} });

    var others: std.ArrayList(Row) = .empty;
    defer others.deinit(gpa);
    try others.appendSlice(gpa, &[_]Row{ .{}, .{} });

    popAfterUnrelatedSweep(&rows, &others);
    try std.testing.expectEqual(@as(usize, 3), rows.items.len);

    popThreeUnderBound(&rows);
    try std.testing.expectEqual(@as(usize, 0), rows.items.len);

    var bytes: std.ArrayList(u8) = .empty;
    defer bytes.deinit(gpa);
    try bytes.appendSlice(gpa, &[_]u8{ 1, 2, 3 });
    try std.testing.expectEqual(@as(usize, 2), popWhileAbove(u8, &bytes, 1));
    try std.testing.expectEqual(@as(usize, 1), bytes.items.len);
}
