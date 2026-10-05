// EXPECT: none
//
// An early successful exit only defeats an installation when the field is not
// installed at that exit. An exit guarded by the field itself leaves a field
// that is already there, and an exit that carries an error leaves on the path
// the caller has already taken before it reaches anything after the call.
const std = @import("std");

const Session = struct {
    slot: ?u32 = null,

    // The early exit happens exactly while the field is already installed.
    fn initUnlessReady(self: *Session) !void {
        if (self.slot != null) return;
        self.slot = 1;
    }

    // The exit carries an error, which the caller cannot continue past.
    fn initOrFail(self: *Session, fail: bool) !void {
        if (fail) return error.Failed;
        self.slot = 2;
    }

    fn read(self: *Session) u32 {
        return self.slot.?;
    }

    fn runGuarded(self: *Session) !u32 {
        try self.initUnlessReady();
        return self.read();
    }

    fn runChecked(self: *Session, fail: bool) !u32 {
        try self.initOrFail(fail);
        return self.read();
    }
};

test "both methods really store their value" {
    var session: Session = .{};
    try std.testing.expectEqual(@as(u32, 1), try session.runGuarded());
    try std.testing.expectEqual(@as(u32, 2), try session.runChecked(false));
    try std.testing.expectError(error.Failed, session.runChecked(true));
}
