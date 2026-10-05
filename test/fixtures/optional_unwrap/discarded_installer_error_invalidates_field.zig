// EXPECT: line=26 rule=optional-unwrap
//
// The rollback an `errdefer` describes runs before the caller's next statement
// whenever that caller carries on after a failure. A second startup that fails
// therefore hands back a cleared field, so an earlier successful installation
// is no longer a proof — while the caller that lets the failure end its own
// flow still only ever observes the success path.
const std = @import("std");

const Session = struct {
    slot: ?u32 = null,

    fn abort(self: *Session) void {
        self.slot = null;
    }

    // A genuinely fallible startup: it installs, and it can still fail after
    // having installed, which is exactly what the rollback is for.
    fn start(self: *Session, fail: bool) !void {
        errdefer self.abort();
        self.slot = 1;
        if (fail) return error.Failed;
    }

    fn read(self: *Session) u32 {
        return self.slot.?; // the second failure was swallowed
    }

    fn readPropagated(self: *Session) u32 {
        return self.slot.?;
    }

    fn runSwallowing(self: *Session, fail: bool) !u32 {
        try self.start(false);
        self.start(fail) catch {};
        return self.read();
    }

    fn runPropagating(self: *Session, fail: bool) !u32 {
        try self.start(false);
        try self.start(fail);
        return self.readPropagated();
    }
};

test "the propagated failure never reaches a read" {
    var session: Session = .{};
    _ = try session.runPropagating(false);
    try std.testing.expectEqual(@as(?u32, 1), session.slot);
    try std.testing.expectError(error.Failed, session.runPropagating(true));
    _ = &Session.runSwallowing;
}
