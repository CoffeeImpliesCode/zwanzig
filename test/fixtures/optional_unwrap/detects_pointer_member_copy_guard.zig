// EXPECT: line=36 rule=optional-unwrap
// EXPECT: line=44 rule=optional-unwrap
// EXPECT: line=103 rule=optional-unwrap
// EXPECT: line=112 rule=optional-unwrap
//
// A value copy owns its own bytes, but a member that is a pointer still
// designates what it points at. Writing through the copy, and calling a method
// on that member, both reach the same pointee the guarded field names, so the
// receiver's null guard does not survive them. A member the copy holds by
// value travels with the rest of the struct and reaches nothing.
const std = @import("std");

const Cell = struct {
    value: ?u8 = null,

    pub fn clear(self: *Cell) void {
        self.value = null;
    }
};

const Flags = struct {
    cell: *Cell,
    note: bool = false,
};

const Packet = struct {
    tag: ?u8,
    flags: Flags,

    /// The copy's `cell` member is the pointer the guard read, so clearing it
    /// clears the very field the guard proved non-null.
    pub fn writesThroughMember(self: *Packet) u8 {
        std.debug.assert(self.flags.cell.value != null);
        const copy = self.flags;
        copy.cell.value = null;
        return self.flags.cell.value.?;
    }

    /// A method call on the same member reaches the same pointee.
    pub fn callsThroughMember(self: *Packet) u8 {
        std.debug.assert(self.flags.cell.value != null);
        const copy = self.flags;
        copy.cell.clear();
        return self.flags.cell.value.?;
    }

    /// The copy owns its `note` bytes, so rewriting them reaches nothing the
    /// receiver holds and the guard survives.
    pub fn writesThroughOwnedMember(self: *Packet) u8 {
        std.debug.assert(self.flags.cell.value != null);
        var copy = self.flags;
        copy.note = false;
        return self.flags.cell.value.?;
    }
};

/// The same pointer written through a name. The member's declared type is read
/// through that name, which designates whatever the name was given, so the copy
/// still carries the very pointer the guard read.
const Ptr = *Cell;

const AliasedFlags = struct {
    cell: Ptr,
};

/// A namespace member is read through the container that declares it rather
/// than through a declaration of this file, and designates the same pointer.
const handles = struct {
    pub const Ptr = *Cell;
};

const NamespacedFlags = struct {
    cell: handles.Ptr,
};

/// A container this file gives a name to is a value, so a member written with
/// that name travels with the slot that carries it instead of reaching past it.
const OwnedCell = struct {
    value: ?u8 = null,

    fn clear(self: *OwnedCell) void {
        self.value = null;
    }
};

const Owned = OwnedCell;

const OwnedFlags = struct {
    cell: Owned,
};

const Wire = struct {
    aliased: AliasedFlags,
    namespaced: NamespacedFlags,
    owned: OwnedFlags,

    /// The copy's `cell` is the guard's own pointer, spelled `Ptr` instead of
    /// `*Cell`, so clearing it clears the field the guard proved non-null.
    pub fn clearsThroughAliasedMember(self: *Wire) u8 {
        std.debug.assert(self.aliased.cell.value != null);
        const copy = self.aliased;
        copy.cell.clear();
        return self.aliased.cell.value.?;
    }

    /// The same pointer reached through a namespace member, which the copy
    /// carries just as it carries the pointer itself.
    pub fn clearsThroughNamespacedMember(self: *Wire) u8 {
        std.debug.assert(self.namespaced.cell.value != null);
        const copy = self.namespaced;
        copy.cell.clear();
        return self.namespaced.cell.value.?;
    }

    /// The copy owns the bytes of the container its `cell` member holds, so the
    /// call reaches nothing the guard covers and the guard survives.
    pub fn callsThroughOwnedAliasedMember(self: *Wire) u8 {
        std.debug.assert(self.owned.cell.value != null);
        var copy = self.owned;
        copy.cell.clear();
        return self.owned.cell.value.?;
    }
};

test "a pointer member spelled through an alias still clears the guarded cell" {
    var aliased_cell: Cell = .{ .value = 7 };
    var namespaced_cell: Cell = .{ .value = 8 };

    const aliased = AliasedFlags{ .cell = &aliased_cell };
    const aliased_copy = aliased;
    aliased_copy.cell.clear();
    try std.testing.expect(aliased_cell.value == null);

    const namespaced = NamespacedFlags{ .cell = &namespaced_cell };
    const namespaced_copy = namespaced;
    namespaced_copy.cell.clear();
    try std.testing.expect(namespaced_cell.value == null);

    const carried = OwnedFlags{ .cell = .{ .value = 3 } };
    var owned_copy = carried;
    owned_copy.cell.clear();
    try std.testing.expectEqual(@as(?u8, 3), carried.cell.value);

    _ = &Packet.writesThroughMember;
    _ = &Packet.callsThroughMember;
    _ = &Packet.writesThroughOwnedMember;
    _ = &Wire.clearsThroughAliasedMember;
    _ = &Wire.clearsThroughNamespacedMember;
    _ = &Wire.callsThroughOwnedAliasedMember;
}
