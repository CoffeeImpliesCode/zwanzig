// EXPECT: line=31 rule=optional-unwrap
//
// A `const` local owns no mutable slot for a caller to reach, but the pointer
// its member carries still designates the caller's object. Copying `Flags`
// copies the `cell` pointer, not the `Cell` behind it, so writing through the
// copy's `cell` clears the very optional field the guard read through `box`.
// The second function is the boundary: `Table.inner` points at a `Leaf`, a type
// that has no `cursor` field at all, and `clear` writes only the leaf's own
// `value` bytes, so nothing the cursor guard covers is reachable through it.
const std = @import("std");

const Cell = struct {
    value: ?u8 = null,
};

const Flags = struct {
    cell: *Cell,
};

const Box = struct {
    flags: Flags,
};

// The local `box` is immutable, yet `copy.cell` is the same `*Cell` the guard
// followed, so the guard proves nothing by the time the unwrap runs.
fn readThroughLocalCopy(seed: *Flags) u8 {
    const box: Box = .{ .flags = seed.* };
    if (box.flags.cell.value != null) {
        const copy = box.flags;
        copy.cell.value = null;
        return box.flags.cell.value.?; // copy.cell is the guarded Cell
    }
    return 0;
}

const Leaf = struct {
    value: u32 = 9,

    fn clear(self: *Leaf) void {
        self.value = 0;
    }
};

const Table = struct {
    inner: *Leaf,
};

const State = struct {
    cursor: ?u32 = null,
};

// `Leaf` and `State` are distinct types that share no field, so clearing the
// leaf writes bytes the cursor guard never covers and the guard survives.
fn takeThroughUnrelatedMember(self: *State, table: *Table) u32 {
    std.debug.assert(self.cursor != null);
    table.inner.clear();
    return self.cursor.?;
}

test "a copy of the local box still writes the shared cell" {
    var cell: Cell = .{ .value = 7 };
    const box: Box = .{ .flags = .{ .cell = &cell } };
    const copy = box.flags;
    copy.cell.value = null;
    try std.testing.expect(cell.value == null);
    try std.testing.expect(box.flags.cell.value == null);
    _ = &readThroughLocalCopy;
}

test "an unrelated leaf member call leaves the cursor guard standing" {
    var leaf: Leaf = .{};
    var table: Table = .{ .inner = &leaf };
    var state: State = .{ .cursor = 42 };
    try std.testing.expectEqual(@as(u32, 42), takeThroughUnrelatedMember(&state, &table));
    try std.testing.expectEqual(@as(u32, 0), leaf.value);
}
