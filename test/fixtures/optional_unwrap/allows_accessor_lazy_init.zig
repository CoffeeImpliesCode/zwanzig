// EXPECT: none
//
// An accessor's own body is the proof: `handleAfterEnsure` reads the field
// after a call whose declaration leaves it filled on every successful exit, a
// `const` written with an optional type and a value that cannot be null is
// enough on its own, and a branch whose alternative returns fills the field on
// whichever path reaches the code after it.
const std = @import("std");

const Fd = struct {
    n: i32 = 0,
};

const Terminal = struct {
    handle: ?Fd = null,
    calls: usize = 0,

    fn handleOrDefault(self: *Terminal) Fd {
        self.calls += 1;
        if (self.handle == null) self.handle = Fd{ .n = -1 };
        return self.handle.?;
    }

    fn initialHandle(self: *const Terminal) Fd {
        _ = self;
        const built: ?Fd = .{ .n = 0 };
        return built.?;
    }

    fn fillThenRead(self: *Terminal) Fd {
        if (self.handle == null) self.handle = Fd{ .n = 7 };
        return self.handle.?;
    }

    fn ensureHandle(self: *Terminal) void {
        if (self.handle == null) self.handle = Fd{ .n = 9 };
    }

    fn handleAfterEnsure(self: *Terminal) Fd {
        self.ensureHandle();
        return self.handle.?;
    }

    fn fillInOneBranch(self: *Terminal, attach: bool) Fd {
        if (attach) {
            self.handle = Fd{ .n = 3 };
        } else {
            return Fd{ .n = 0 };
        }
        return self.handle.?;
    }
};

test "accessor lazy init: every accessor that fills returns the filled handle" {
    var t1: Terminal = .{};
    try std.testing.expectEqual(@as(i32, -1), t1.handleOrDefault().n);
    const t2: Terminal = .{};
    try std.testing.expectEqual(@as(i32, 0), t2.initialHandle().n);
    var t3: Terminal = .{};
    try std.testing.expectEqual(@as(i32, 7), t3.fillThenRead().n);
    var t4: Terminal = .{};
    try std.testing.expectEqual(@as(i32, 9), t4.handleAfterEnsure().n);
    var t5: Terminal = .{};
    try std.testing.expectEqual(@as(i32, 3), t5.fillInOneBranch(true).n);
}
