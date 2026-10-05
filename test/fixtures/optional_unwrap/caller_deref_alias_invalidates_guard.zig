// EXPECT: line=18 rule=optional-unwrap severity=warning
//
// A caller that clears the field through a pointer alias writes it as
// `me.*.field`, a place this scan cannot spell, and the write still reaches
// the receiver's own storage: the helper it calls afterwards keeps its warning.
// The same shape with the field only checked still proves its own helper.
const std = @import("std");

const Band = struct {
    width: u16 = 80,
};

const App = struct {
    plain: ?Band = null,
    tall: ?Band = null,

    fn readPlain(self: *App) u16 {
        return self.plain.?.width;
    }

    fn readTall(self: *App) u16 {
        return self.tall.?.width;
    }
};

// The alias holds the receiver's own pointer, so writing through its pointee
// clears the caller's field before the call.
fn reset(self: *App) u16 {
    const me = self;
    me.*.plain = null;
    return self.readPlain();
}

// The same shape with the field checked instead of cleared.
fn keep(self: *App) u16 {
    if (self.tall != null) {
        return self.readTall();
    }
    return 0;
}

test "a deref alias clears the receiver before the guarded call" {
    var app: App = .{ .plain = Band{}, .tall = Band{} };
    try std.testing.expectEqual(@as(u16, 80), keep(&app));
    _ = &reset;
}
