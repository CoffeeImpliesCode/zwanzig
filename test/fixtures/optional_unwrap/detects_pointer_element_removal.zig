// EXPECT: line=41 rule=optional-unwrap
// EXPECT: line=55 rule=optional-unwrap
//
// A removal copies the element out of the list, but an element that is itself
// a pointer still designates what it points at. When the list was given the
// guarded object's own address, the removed pointer is that very object, so
// clearing through it or writing through it clears the guarded field. A list of
// values copies its elements out instead, so the removed slot owns its own
// bytes and the separate guard survives.
const std = @import("std");

const Allocator = std.mem.Allocator;

const Cell = struct {
    value: ?u8 = null,

    pub fn clear(self: *Cell) void {
        self.value = null;
    }
};

const Row = struct {
    cell: *Cell,
    wrapped: bool = false,

    pub fn clear(self: *Row) void {
        self.wrapped = false;
    }
};

/// The list received `cell` and holds nothing else, so the removed pointer is
/// that same `Cell`.
fn popThenClearCell(gpa: Allocator, cell: *Cell) !u8 {
    var list: std.ArrayList(*Cell) = .empty;
    defer list.deinit(gpa);
    try list.append(gpa, cell);
    std.debug.assert(cell.value != null);
    if (list.items.len > 0) {
        const next = list.pop().?;
        next.clear();
        return cell.value.?;
    }
    return 0;
}

/// The same removal, written through the removed pointer.
fn popThenWriteCell(gpa: Allocator, cell: *Cell) !u8 {
    var list: std.ArrayList(*Cell) = .empty;
    defer list.deinit(gpa);
    try list.append(gpa, cell);
    std.debug.assert(cell.value != null);
    if (list.items.len > 0) {
        const next = list.pop().?;
        next.value = null;
        return cell.value.?;
    }
    return 0;
}

/// The row was copied out of the list, so clearing that copy reaches neither
/// the list nor the cell the guard read.
fn popRowKeepsGuard(gpa: Allocator, rows: *std.ArrayList(Row), cell: *Cell) !u8 {
    try rows.append(gpa, .{ .cell = cell });
    std.debug.assert(cell.value != null);
    if (rows.items.len > 0) {
        var row = rows.pop().?;
        row.clear();
        row.wrapped = false;
    }
    return cell.value.?;
}

/// A removed byte is a copy the new slot owns, so rewriting it reaches nothing
/// outside that slot.
fn popByteKeepsGuard(gpa: Allocator, bytes: *std.ArrayList(u8), cell: *Cell) !u8 {
    try bytes.append(gpa, 3);
    std.debug.assert(cell.value != null);
    if (bytes.items.len > 0) {
        var next = bytes.pop().?;
        next = next -% 1;
    }
    return cell.value.?;
}
