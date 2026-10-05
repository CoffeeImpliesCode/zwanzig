// EXPECT: line=20 rule=optional-unwrap severity=warning
// EXPECT: line=45 rule=optional-unwrap severity=warning
//
// A pointer to an optional stores that optional, a type alias that ends in `?`
// is still optional, and a write spelled through a second name for the object
// clears the field it aliases. None of them carries a construction fact.
const std = @import("std");

const Band = struct {
    width: u16 = 80,
};

const MaybeBand = ?Band;
const AliasedBand = MaybeBand;

const Session = struct {
    field: ?Band = null,

    fn readSessionWidth(self: *Session) u16 {
        return self.field.?.width;
    }

    fn clear(self: *Session) void {
        self.field = null;
    }

    fn clearThroughAlias(self: *Session) void {
        var me = self;
        me.field = null;
    }
};

const Holder = struct {
    field: ?Band = null,

    fn installFromPointer(self: *Holder, src: *?Band) void {
        self.field = src.*;
    }

    fn installFromAlias(self: *Holder, value: AliasedBand) void {
        self.field = value;
    }

    fn readHolderWidth(self: *Holder) u16 {
        return self.field.?.width;
    }
};

const ConstructedHolder = struct {
    field: ?Band = null,

    fn readConstructedWidth(self: *ConstructedHolder) u16 {
        return self.field.?.width;
    }
};

fn readAfterDirectClear() u16 {
    var session: Session = .{ .field = Band{} };
    session.clear();
    return session.readSessionWidth();
}

fn readAfterAliasedClear() u16 {
    var session: Session = .{ .field = Band{} };
    session.clearThroughAlias();
    return session.readSessionWidth();
}

fn readAfterPointerInstall() u16 {
    var holder: Holder = .{};
    var maybe: ?Band = null;
    holder.installFromPointer(&maybe);
    return holder.readHolderWidth();
}

fn readAfterAliasInstall() u16 {
    var holder: Holder = .{};
    const maybe: ?Band = null;
    holder.installFromAlias(maybe);
    return holder.readHolderWidth();
}

test "pointer and alias installs: only the constructed holder is read" {
    var holder: ConstructedHolder = .{ .field = Band{} };
    try std.testing.expectEqual(@as(u16, 80), holder.readConstructedWidth());
}
