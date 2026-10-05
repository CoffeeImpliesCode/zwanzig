// EXPECT: line=27 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=34 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
//
// Operand order decides what an unwrap reaches. Zig evaluates the elements
// of a tuple, and the arguments of a call, left to right: a mutation written
// ahead of the `.?` in the same statement runs before the field is read,
// while one written behind it runs on a value the read already produced.
// A null guard that covers the read covers neither of those operands.

const Owner = struct {
    field: ?u32 = null,

    /// Clears the field and answers a value for the operand beside it.
    fn clear(self: *Owner) u32 {
        self.field = null;
        return 0;
    }

    fn total(first: u32, second: u32) u32 {
        return first + second;
    }

    /// The element ahead of the unwrap clears the field first, so the `.?`
    /// reads back the null that element puts there.
    fn tupleBefore(self: *Owner) [2]u32 {
        if (self.field == null) return .{ 0, 0 };
        return .{ self.clear(), self.field.? };
    }

    /// The argument ahead of the unwrap clears the field first, so the `.?`
    /// reads back the null that argument puts there.
    fn argumentBefore(self: *Owner) u32 {
        if (self.field == null) return 0;
        return total(self.clear(), self.field.?);
    }

    /// The unwrap is the first element, so the clear beside it runs on a
    /// value the read already produced.
    fn tupleAfter(self: *Owner) [2]u32 {
        if (self.field == null) return .{ 0, 0 };
        return .{ self.field.?, self.clear() };
    }

    /// The unwrap is the first argument, so the clear beside it runs on a
    /// value the read already produced.
    fn argumentAfter(self: *Owner) u32 {
        if (self.field == null) return 0;
        return total(self.field.?, self.clear());
    }

    /// A deferred clear runs when the scope exits, which is after the read.
    fn deferredClear(self: *Owner) u32 {
        if (self.field == null) return 0;
        defer self.clear();
        return self.field.?;
    }
};

/// Each caller below hands the owner over as it comes: none of them proves
/// the field non-null, so what a method does with it is read on its own.
pub fn tupleBeforeEntry(owner: *Owner) [2]u32 {
    return owner.tupleBefore();
}

pub fn argumentBeforeEntry(owner: *Owner) u32 {
    return owner.argumentBefore();
}

pub fn tupleAfterEntry(owner: *Owner) [2]u32 {
    return owner.tupleAfter();
}

pub fn argumentAfterEntry(owner: *Owner) u32 {
    return owner.argumentAfter();
}

pub fn deferredEntry(owner: *Owner) u32 {
    return owner.deferredClear();
}
