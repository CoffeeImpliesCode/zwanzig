// EXPECT: line=22 rule=optional-unwrap severity=warning
//
// An array parameter can carry a pointer to the receiver, so a callee that
// takes one may rewrite the field its own unwrap depends on. The alias is
// followed as far as the receiver's own declaration, and the guard the one
// caller establishes does not survive that. A plain value parameter carries
// nothing and leaves its helper's proof alone.
const std = @import("std");

const Band = struct {
    width: u16 = 80,
};

const Slots = [1]*App;

const App = struct {
    plain: ?Band = null,
    tall: ?Band = null,

    fn readThroughSlots(self: *App, slots: Slots) u16 {
        slots[0].plain = null;
        return self.plain.?.width;
    }

    fn readTall(self: *App, width: u16) u16 {
        return self.tall.?.width + width;
    }
};

fn reset(self: *App) u16 {
    if (self.plain != null) {
        const slots: Slots = .{self};
        return self.readThroughSlots(slots);
    }
    return 0;
}

fn keep(self: *App) u16 {
    if (self.tall != null) {
        return self.readTall(2);
    }
    return 0;
}

test "an array parameter reaches the receiver the callee unwraps" {
    var app: App = .{ .plain = Band{}, .tall = Band{} };
    try std.testing.expectEqual(@as(u16, 82), keep(&app));
    _ = &reset;
}
