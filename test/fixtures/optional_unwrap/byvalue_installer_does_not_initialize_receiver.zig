// EXPECT: line=35 rule=optional-unwrap severity=warning
// EXPECT: line=42 rule=optional-unwrap severity=warning
//
// A by-value receiver is a copy handed to the callee, so what the callee writes
// lands on that copy and never installs the caller's optional field. Only a real
// pointer hands the callee the caller's storage.
const std = @import("std");

const Band = struct {
    width: u16 = 80,
};

const Holder = struct {
    field: ?Band = null,

    fn installByValue(self: Holder, value: Band) void {
        var mine = self;
        mine.installByPointer(value);
    }

    fn installByCopy(self: Holder, value: Band) void {
        var copy = self;
        copy.field = value;
    }

    fn installByPointer(self: *Holder, value: Band) void {
        self.field = value;
    }
};

// The by-value installer writes a copy, so the field is still null here.
fn readAfterByValueInstall() u16 {
    var holder: Holder = .{};
    holder.installByValue(Band{});
    return holder.field.?.width;
}

// The copy the method makes of itself is the same story one level down.
fn readAfterByCopyInstall() u16 {
    var holder: Holder = .{};
    holder.installByCopy(Band{});
    return holder.field.?.width;
}

// The pointer receiver is the caller's own storage, so this one holds.
fn readAfterPointerInstall() u16 {
    var holder: Holder = .{};
    holder.installByPointer(Band{});
    return holder.field.?.width;
}

test "a by-value installer writes a copy, a pointer installer writes the field" {
    try std.testing.expectEqual(@as(u16, 80), readAfterPointerInstall());
    _ = &readAfterByValueInstall;
    _ = &readAfterByCopyInstall;
}
