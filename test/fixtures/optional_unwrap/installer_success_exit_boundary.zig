// EXPECT: line=30 rule=optional-unwrap
// EXPECT: line=34 rule=optional-unwrap
//
// An installation a caller may rely on has to survive every way the callee can
// leave, not only the one that falls off its end. A `return` under a condition
// the field itself has nothing to do with is a successful exit, and it hands
// the caller back the field exactly as the caller passed it.
const std = @import("std");

const Session = struct {
    slot: ?u32 = null,

    // Whether this method installs at all is decided by a condition about
    // something else, so its early exit is a successful one and leaves the
    // field untouched.
    fn initWhen(self: *Session, install: bool) !void {
        if (!install) return;
        self.slot = 1;
    }

    // The same shape written as a braced block.
    fn initUnless(self: *Session, install: bool) !void {
        if (!install) {
            return;
        }
        self.slot = 2;
    }

    fn readWhen(self: *Session) u32 {
        return self.slot.?; // initWhen
    }

    fn readUnless(self: *Session) u32 {
        return self.slot.?; // initUnless
    }

    fn runWhen(self: *Session, install: bool) !u32 {
        try self.initWhen(install);
        return self.readWhen();
    }

    fn runUnless(self: *Session, install: bool) !u32 {
        try self.initUnless(install);
        return self.readUnless();
    }
};

test "the installing paths of both methods really store their value" {
    var session: Session = .{};
    _ = try session.runWhen(true);
    try std.testing.expectEqual(@as(?u32, 1), session.slot);
    _ = try session.runUnless(true);
    try std.testing.expectEqual(@as(?u32, 2), session.slot);
}
