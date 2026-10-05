// EXPECT: line=82 rule=optional-unwrap
// EXPECT: line=89 rule=optional-unwrap
//
// A copy of a value owns its own bytes, so writing one is not writing through
// an alias to the receiver and the null guard still stands at the unwrap. The
// member's own declared type decides that, and a name this file gives to a
// type carries whatever the name was given: `const Owned = OwnedCell;` names
// the container and `const Shared = *OwnedCell;` names the pointer. The two
// spellings of a value member therefore behave alike, and the two spellings
// of a pointer member still reach the field the guard read.
const std = @import("std");

const OwnedCell = struct {
    value: ?u8 = null,
};

/// A value carrier, spelled through a name of this file.
const Owned = OwnedCell;

/// A pointer carrier, spelled through a name of this file.
const Shared = *OwnedCell;

const OwnedFlags = struct {
    cell: Owned,
};

const Holder = struct {
    owned: OwnedFlags,
};

const DirectHolder = struct {
    cell: OwnedCell,
};

const AliasedHolder = struct {
    cell: Owned,
};

const SharedHolder = struct {
    cell: Shared,
};

/// Two hops, both of them naming the container. The copy owns its own
/// `OwnedCell` bytes, so writing it leaves the guarded field set.
pub fn assertedWriteCopy(self: *Holder) u8 {
    std.debug.assert(self.owned.cell.value != null);
    var copy = self.owned;
    copy.cell.value = null;
    std.debug.assert(copy.cell.value == null);
    return self.owned.cell.value.?;
}

/// The same copy with the member's type spelled out instead of named, so
/// nothing here depends on how a name is resolved.
pub fn writeThroughDirectCell(self: *DirectHolder) u8 {
    std.debug.assert(self.cell.value != null);
    var copy = self.cell;
    copy.value = null;
    std.debug.assert(copy.value == null);
    return self.cell.value.?;
}

/// One hop instead of two: the copied member's own declared type is the name.
/// Only that spelling differs from the pair above, and the verdict has to
/// match it.
pub fn writeThroughAliasedCell(self: *AliasedHolder) u8 {
    std.debug.assert(self.cell.value != null);
    var copy = self.cell;
    copy.value = null;
    std.debug.assert(copy.value == null);
    return self.cell.value.?;
}

/// The pointer twin. The name here stands for a pointer, so the copy carries
/// the pointer the guard read and `view.value = null` writes the very `?u8`
/// `self.cell.value` names.
pub fn writeThroughSharedCell(self: *SharedHolder) u8 {
    std.debug.assert(self.cell.value != null);
    var view = self.cell;
    view.value = null;
    std.debug.assert(view.value == null);
    return self.cell.value.?;
}

/// No copy at all: the guarded storage itself is rewritten after the assert.
pub fn writesDirectlyToOriginal(self: *Holder) u8 {
    std.debug.assert(self.owned.cell.value != null);
    self.owned.cell.value = null;
    return self.owned.cell.value.?;
}

test "a value copy leaves the guarded field set, however its member type is spelled" {
    var holder: Holder = .{ .owned = .{ .cell = .{ .value = 7 } } };
    var copy = holder.owned;
    copy.cell.value = null;
    try std.testing.expect(copy.cell.value == null);
    try std.testing.expectEqual(@as(?u8, 7), holder.owned.cell.value);

    var direct: DirectHolder = .{ .cell = .{ .value = 5 } };
    var direct_copy = direct.cell;
    direct_copy.value = null;
    try std.testing.expect(direct_copy.value == null);
    try std.testing.expectEqual(@as(?u8, 5), direct.cell.value);

    var aliased: AliasedHolder = .{ .cell = .{ .value = 3 } };
    var aliased_copy = aliased.cell;
    aliased_copy.value = null;
    try std.testing.expect(aliased_copy.value == null);
    try std.testing.expectEqual(@as(?u8, 3), aliased.cell.value);

    // The three quiet bodies run for real: none of them can panic here.
    try std.testing.expectEqual(@as(u8, 7), assertedWriteCopy(&holder));
    try std.testing.expectEqual(@as(u8, 5), writeThroughDirectCell(&direct));
    try std.testing.expectEqual(@as(u8, 3), writeThroughAliasedCell(&aliased));
    try std.testing.expectEqual(@as(?u8, 7), holder.owned.cell.value);
    try std.testing.expectEqual(@as(?u8, 5), direct.cell.value);
    try std.testing.expectEqual(@as(?u8, 3), aliased.cell.value);
}

test "the copied pointer writes the storage the guard read, with no unwrap of its own" {
    var cell = OwnedCell{ .value = 9 };
    const holder: SharedHolder = .{ .cell = &cell };
    std.debug.assert(holder.cell.value != null);

    var view = holder.cell;
    view.value = null;

    // Deliberately no `.?` here: the mutation is the observation, so the
    // unsafe consumers are never invoked to witness it.
    try std.testing.expect(view.value == null);
    try std.testing.expect(holder.cell.value == null);
    try std.testing.expect(cell.value == null);
    _ = &writeThroughSharedCell;
    _ = &writesDirectlyToOriginal;
}
