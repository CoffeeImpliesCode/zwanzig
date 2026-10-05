// EXPECT: line=19 rule=optional-unwrap
// EXPECT: line=23 rule=optional-unwrap
// EXPECT: line=33 rule=optional-unwrap
//
// An accessor that fills the field on one branch only proves nothing, a body
// that never fills proves nothing, and a postcondition that is undone again
// before the read proves nothing either.
const Fd = struct {
    n: i32 = 0,
};

const Terminal = struct {
    handle: ?Fd = null,
    calls: usize = 0,

    fn maybeHandle(self: *Terminal, attach: bool) Fd {
        self.calls += 1;
        if (attach) self.handle = Fd{ .n = 3 };
        return self.handle.?;
    }

    fn unwrapWithoutFill(self: *Terminal) Fd {
        return self.handle.?;
    }

    fn ensureHandle(self: *Terminal) void {
        if (self.handle == null) self.handle = Fd{ .n = 9 };
    }

    fn handleAfterEnsureAndClear(self: *Terminal) Fd {
        self.ensureHandle();
        self.handle = null;
        return self.handle.?;
    }
};
