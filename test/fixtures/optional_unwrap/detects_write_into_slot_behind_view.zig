// EXPECT: line=21 rule=optional-unwrap
// EXPECT: line=29 rule=optional-unwrap
// EXPECT: line=38 rule=optional-unwrap
// EXPECT: line=47 rule=optional-unwrap
//
// A view taken from a local slot designates the very bytes that slot owns, so
// writing the slot reaches storage the guarded expression reads even though
// the two are spelled with different names. By-value copies are the other
// side of the line: they own new storage and never carry the slot's bytes.
const std = @import("std");

const Cell = struct {
    value: ?u32,
};

pub fn writesSlotBehindSliceView() u32 {
    var cells: [2]Cell = .{ .{ .value = 1 }, .{ .value = 2 } };
    const view: []Cell = cells[0..];
    std.debug.assert(view[0].value != null);
    cells[0].value = null;
    return view[0].value.?;
}

pub fn writesSlotBehindPointerView() u32 {
    var cells: [2]Cell = .{ .{ .value = 1 }, .{ .value = 2 } };
    const first: *Cell = &cells[0];
    std.debug.assert(first.value != null);
    cells[0].value = null;
    return first.value.?;
}

pub fn writesSlotBehindCopiedView() u32 {
    var cells: [2]Cell = .{ .{ .value = 1 }, .{ .value = 2 } };
    const view: []Cell = cells[0..];
    const copy: []Cell = view;
    std.debug.assert(copy[0].value != null);
    cells[0].value = null;
    return copy[0].value.?;
}

pub fn writesSlotBehindReboundAlias() u32 {
    var cells: [2]Cell = .{ .{ .value = 1 }, .{ .value = 2 } };
    var first: *Cell = &cells[1];
    std.debug.assert(first.value != null);
    first = &cells[0];
    cells[0].value = null;
    return first.value.?;
}