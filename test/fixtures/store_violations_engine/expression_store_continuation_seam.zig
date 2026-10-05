//! `.expr` stores: the seam where a store the CFG builder gave no node of its
//! own loses both its deref ownership transfer and its use-after-free read.
//!
//! `while (cond) : (store)` is lowered as one plain expression node, so every
//! store in this file arrives at the analyzer as a bare `.expr` rather than as
//! the assignment node a store written as a statement of its own gets. Rows e1
//! and e2 are the ownership question: the continuation moves a payload into a
//! block the function returns, and the analyzer has to see the same thing for
//! it that it sees for the same store written as a statement.
//!
//! Rows e3 and e4 are the read question: the store runs against a block that
//! was released before it, once through its destination and once through the
//! value it writes. e1 is the positive row: the ownership transfer really
//! happens, nothing is reported. e2 to e8 are analyzer controls, uncalled.

const std = @import("std");

/// Carries a payload block, so a block made of it can hold a reference.
const Box = struct {
    payload: []u8,
};

/// The payload every driver row hands in, written down so the driver's byte
/// comparison is made against a prefilled buffer and not against a length.
const payload_text = "ownedbytes";

/// e1 - quiet. A `while` continuation that stores an owning aggregate into a
/// block this function returns.
///
/// The store runs once, with `bytes` still allocated and still owned by nobody
/// but this function, and the block it writes into leaves with the return
/// value. The payload rides out inside it, so nothing is reported.
///
/// The loop is finite and its continuation runs exactly once: the body takes
/// `i` from 0 to 1, the continuation then stores, and `1 < 1` ends the loop.
/// Nothing in the body allocates.
fn buildBox(a: std.mem.Allocator, input: []const u8) !*Box {
    const out = try a.create(Box);
    const bytes = try a.dupe(u8, input);
    var i: usize = 0;
    while (i < 1) : (out.* = .{ .payload = bytes }) {
        i += 1;
    }
    return out;
}

/// e2 - reported. The same continuation seam, but the pointee is a `usize`.
///
/// What the store hands over is the pointee's type, not the shape of the value
/// written into it. A `usize` cannot hold a reference, so the store hands the
/// block nothing to own and the bytes stay this function's to release - and it
/// never does. This is the row that pins the over-reach: a pointee that cannot
/// hold a reference must not be credited with one it cannot hold.
fn buildSlot(a: std.mem.Allocator, input: []const u8) !*usize {
    const bytes = try a.dupe(u8, input);
    const slot = try a.create(usize);
    var i: usize = 0;
    while (i < 1) : (slot.* = bytes.len) {
        i += 1;
    }
    return slot;
}

/// e3 - reported. The destination block was released before the continuation
/// store ran, so the store writes through freed memory.
///
/// The region that must be reported is the block `a.create` produced, and the
/// read is the destination's: a store writes through the pointer it names, so
/// the pointer is read. The value it writes is read too, which is what the
/// second report on this line is.
fn e3FreedDestination(a: std.mem.Allocator, input: []const u8) !void {
    const out = try a.create(Box);
    const bytes = try a.dupe(u8, input);
    a.destroy(out);
    a.free(bytes);
    var i: usize = 0;
    while (i < 1) : (out.* = .{ .payload = bytes }) {
        i += 1;
    }
}

/// e4 - reported. The value the store writes names a block released before the
/// continuation ran, so the store reads freed memory.
///
/// Same seam from the other side. The value has to be spelled as something the
/// read descends into, and a bare struct literal is not one of them on its own:
/// the payload is written as a subslice so the read reaches the identifier
/// behind it.
fn e4FreedValue(a: std.mem.Allocator, input: []const u8) !void {
    const out = try a.create(Box);
    const bytes = try a.dupe(u8, input);
    a.free(bytes);
    var i: usize = 0;
    while (i < 1) : (out.* = .{ .payload = bytes[0..2] }) {
        i += 1;
    }
    a.destroy(out);
}

// e1 at runtime. The continuation moves the payload into the block.
// The driver reads it back, releases both blocks, and checks the allocator.
// It reads the payload before it destroys the block that holds it.
test "the continuation store moves the payload into the block it returns" {
    var heap: std.heap.DebugAllocator(.{}) = .init;

    const box = try buildBox(heap.allocator(), payload_text);
    const want: [10:0]u8 = payload_text.*;
    try std.testing.expectEqualStrings(want[0..], box.payload);
    const payload = box.payload;
    heap.allocator().destroy(box);
    heap.allocator().free(payload);
    try std.testing.expectEqual(std.heap.Check.ok, heap.deinit());
}

// EXPECT: line=55 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=77 rule=store-violations-engine severity=error message=use after free
// EXPECT: line=77 rule=store-violations-engine severity=error message=use after free
// EXPECT: line=94 rule=store-violations-engine severity=error message=use after free
// EXPECT: line=146 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=162 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=176 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=195 rule=store-violations-engine severity=error message=resource leak
//
// e1 reports nothing: the store records the ownership edge the payload really
// moves, so the bytes ride out inside the returned block.
//
// e2 reports the bytes the slot's length was read from, at the allocation
// that made them. The same store written as a statement of its own lands in
// the same place, so this row is what keeps a pointee that cannot hold a
// reference from being credited with one.
//
// e3 reports twice on one line, once for the destination the store writes
// through and once for the payload it writes, because both blocks are released
// before the store runs and both are read by it. e4 reports once, for the
// payload alone: its destination is still live at the store.

/// e5 - reported. The continuation store never runs: the loop's own bound
/// starts out false, so no pass is admitted and the step is never reached.
/// The payload therefore never moves into the block this function returns,
/// that block leaves with the empty payload it was given, and the bytes stay
/// live with nothing left to release them. The report belongs to the
/// allocation that made them.
fn e5ContinuationNeverRuns(a: std.mem.Allocator, input: []const u8) !*Box {
    const out = try a.create(Box);
    out.* = .{ .payload = &.{} };
    const bytes = try a.alloc(u8, input.len);
    var i: usize = 1;
    while (i < 1) : (out.* = .{ .payload = bytes }) {
        i += 1;
    }
    return out;
}

/// e6 - reported. The same store that never runs, written as a statement of
/// its own this time instead of as a loop step. A condition that admits no
/// pass is a pass the store is not reached on, so the payload stays where it
/// was allocated and the block that returns is still the empty one. The
/// report belongs to the allocation that made the bytes.
fn e6StoreNeverRuns(a: std.mem.Allocator, input: []const u8) !*Box {
    const out = try a.create(Box);
    out.* = .{ .payload = &.{} };
    const bytes = try a.alloc(u8, input.len);
    if (false) out.* = .{ .payload = bytes };
    return out;
}

/// e7 - reported. The store runs and does move the payload into the block it
/// writes, and that block is released before the return value is built, so
/// the value that leaves is a different block. A release of a block is a
/// release of the block: the payload stored inside it is not released with
/// it, so the bytes are dropped on the floor with it. Nothing is read after
/// the release, so this row is a leak and not a use after free, and the
/// report belongs to the allocation that made the bytes.
fn e7StoredBlockReleasedFreshReturned(a: std.mem.Allocator, input: []const u8) !*Box {
    const stored = try a.create(Box);
    const bytes = try a.alloc(u8, input.len);
    var i: usize = 0;
    while (i < 1) : (stored.* = .{ .payload = bytes }) {
        i += 1;
    }
    a.destroy(stored);
    const fresh = try a.create(Box);
    fresh.* = .{ .payload = &.{} };
    return fresh;
}

/// e8 - reported. The same executed store over a block that is released with
/// nothing returning it. The destroy discharges the container, and only the
/// container: the payload the store put inside it is not released, so the
/// bytes leak and the block does not. The report belongs to the allocation
/// that made the bytes.
fn e8StoredBlockReleasedNothingReturned(a: std.mem.Allocator, input: []const u8) !void {
    const out = try a.create(Box);
    out.* = .{ .payload = &.{} };
    const bytes = try a.alloc(u8, input.len);
    var i: usize = 0;
    while (i < 1) : (out.* = .{ .payload = bytes }) {
        i += 1;
    }
    a.destroy(out);
}

// e5 to e8 are analyzer controls: like e2 they leak on purpose, and the test
// above calls none of them, so running it still exercises e1 alone.
//
// e5 and e6 pin the seam from the side where the store does not run: a pass
// the loop does not admit is not a pass the payload moves on, so the bytes
// stay live and stay reported. A walk that reads the store off the syntax
// and never asks whether the pass exists would credit both rows and silence
// the first two reports below.
//
// e7 and e8 pin it from the side where the store does run: once the payload
// really has moved into a block, the block's own release is what has to be
// looked through. `a.destroy` discharges the container and only the
// container, so the payload inside it leaks in both rows - once with another
// block leaving in the return value, once with nothing returning at all.
