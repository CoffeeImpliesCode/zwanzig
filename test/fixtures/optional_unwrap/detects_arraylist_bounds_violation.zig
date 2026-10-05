// EXPECT: line=20 rule=optional-unwrap
// EXPECT: line=25 rule=optional-unwrap
// EXPECT: line=31 rule=optional-unwrap
// EXPECT: line=39 rule=optional-unwrap
// EXPECT: line=46 rule=optional-unwrap
// EXPECT: line=68 rule=optional-unwrap
// EXPECT: line=76 rule=optional-unwrap
//
// A bound already spent by earlier removals cannot cover the next one, a
// length proof about another list says nothing, a recorded emptiness is not a
// check, and any statement that can empty the list cancels the proof, as
// does the guard's own condition, re-evaluated before every pass.
const std = @import("std");

const Row = struct {
    wrapped: bool = false,
};

fn popBlind(items: *std.ArrayList(Row)) void {
    _ = items.pop().?;
}

fn popUnrelatedGuard(items: *std.ArrayList(Row), other: *std.ArrayList(Row)) void {
    if (other.items.len > 0) {
        _ = items.pop().?;
    }
}

fn popAfterRecordingEmptiness(items: *std.ArrayList(Row)) bool {
    const was_empty = items.items.len == 0;
    const row = items.pop().?;
    return was_empty or row.wrapped;
}

fn popPastTheBound(items: *std.ArrayList(Row)) void {
    if (items.items.len > 1) {
        _ = items.pop().?;
        _ = items.pop().?;
        _ = items.pop().?;
    }
}

fn popAfterClearing(items: *std.ArrayList(Row)) void {
    while (items.items.len > 1) {
        items.clearRetainingCapacity();
        _ = items.pop().?;
    }
}

/// Spends one element of the list before the guarded body runs, then reports
/// that the loop may keep going.
fn dropOne(items: *std.ArrayList(Row)) bool {
    _ = items.pop();
    return true;
}

/// Empties the list outright once it reaches the length the enclosing
/// condition proves, so that proved length is gone before the body runs.
fn emptyOnTwo(items: *std.ArrayList(Row)) bool {
    if (items.items.len == 2) items.clearRetainingCapacity();
    return true;
}

/// Unsafe: the condition is re-evaluated before the body on every pass, so
/// dropOne spends the element first and the body pops from an empty list.
fn popAfterConditionRemoval(items: *std.ArrayList(Row)) void {
    while (items.items.len > 0 and dropOne(items)) {
        _ = items.pop().?;
    }
}

/// Unsafe: the proved length is gone before the removal is reached, because
/// emptyOnTwo clears the list from the condition itself.
fn popAfterConditionClear(items: *std.ArrayList(Row)) void {
    while (items.items.len > 0 and emptyOnTwo(items)) {
        _ = items.pop().?;
    }
}

test "the condition spends an element before the body runs" {
    var items: std.ArrayList(Row) = .empty;
    defer items.deinit(std.testing.allocator);
    try items.append(std.testing.allocator, .{});

    var bodies: usize = 0;
    var misses: usize = 0;
    while (items.items.len > 0 and dropOne(&items)) {
        bodies += 1;
        if (items.pop() == null) misses += 1;
    }

    try std.testing.expectEqual(@as(usize, 1), bodies);
    try std.testing.expectEqual(@as(usize, 1), misses);
}

test "the condition can empty the list before the body runs" {
    var items: std.ArrayList(Row) = .empty;
    defer items.deinit(std.testing.allocator);
    try items.appendSlice(std.testing.allocator, &[_]Row{ .{}, .{} });

    var misses: usize = 0;
    while (items.items.len > 0 and emptyOnTwo(&items)) {
        if (items.pop() == null) misses += 1;
    }

    try std.testing.expectEqual(@as(usize, 1), misses);
}
