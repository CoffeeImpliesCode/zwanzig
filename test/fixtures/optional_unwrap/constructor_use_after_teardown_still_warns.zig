// EXPECT: line=36 rule=optional-unwrap severity=warning
// EXPECT: line=50 rule=optional-unwrap severity=warning
// EXPECT: line=56 rule=optional-unwrap severity=warning
//
// Construction facts survive only until something replaces or clears the field
// again. A read after a teardown, a read after a recovered constructor error
// and a read of an undefined owner each keep the warning.
const std = @import("std");

const Region = struct {
    height: u16 = 24,

    fn render(self: *const Region) u16 {
        return self.height;
    }
};

const Session = struct {
    region: ?Region = null,

    fn deinit(self: *Session) void {
        self.region = null;
    }
};

// A struct literal installs the field, so the first read is safe.
fn readConstructedSession() u16 {
    var session = Session{ .region = Region{} };
    return session.region.?.render();
}

// The teardown clears the field again before the read.
fn readAfterTeardown() u16 {
    var session = Session{ .region = Region{} };
    session.deinit();
    return session.region.?.render();
}

// A replacement installation after the teardown restores the fact.
fn readAfterReplacement() u16 {
    var session = Session{ .region = Region{} };
    session.deinit();
    session.region = Region{};
    return session.region.?.render();
}

// A recovered constructor error leaves the fallback value in place.
fn readAfterRecoveredFailure() u16 {
    var session = makeSession() catch Session{};
    return session.region.?.render();
}

// An undefined owner carries no construction fact at all.
fn readUndefinedSession() u16 {
    var session: Session = undefined;
    return session.region.?.render();
}

fn makeSession() error{No}!Session {
    return .{ .region = Region{} };
}

test "construction controls: only the constructed session is read" {
    try std.testing.expectEqual(@as(u16, 24), readConstructedSession());
    try std.testing.expectEqual(@as(u16, 24), readAfterReplacement());
}
