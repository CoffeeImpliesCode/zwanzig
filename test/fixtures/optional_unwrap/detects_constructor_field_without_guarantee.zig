// EXPECT: line=26 rule=optional-unwrap
// EXPECT: line=48 rule=optional-unwrap
// EXPECT: line=68 rule=optional-unwrap
// EXPECT: line=94 rule=optional-unwrap
// EXPECT: line=117 rule=optional-unwrap
// EXPECT: line=143 rule=optional-unwrap
//
// Nothing about the constructor's name proves anything: each container below
// unwraps a field that its own construction and control flow leave nullable.
const std = @import("std");

/// The constructor never asserts, so `fill` may still be null where `pad`
/// holds.
fn Unguarded(comptime T: type, comptime pad: bool) type {
    return struct {
        const Self = @This();
        fill: ?T,
        rest: usize = 0,

        pub fn init(fill: ?T) Self {
            return .{ .fill = fill };
        }

        pub fn next(self: *Self) ?T {
            if (self.rest == 0 or !pad) return null;
            return self.fill.?;
        }
    };
}

/// `pad` is a runtime flag here, so neither the constructor's guard nor the
/// use's early exit decides anything before the program runs.
fn RuntimeFlag(comptime T: type) type {
    return struct {
        const Self = @This();
        fill: ?T,
        rest: usize = 1,
        pad: bool,
        pub fn init(fill: ?T, pad: bool) Self {
            if (pad) {
                std.debug.assert(fill != null);
            }
            return .{ .fill = fill, .pad = true };
        }

        pub fn next(self: *Self) ?T {
            if (self.rest == 0 or !self.pad) return null;
            return self.fill.?;
        }
    };
}

/// The use is not dominated by anything that decides `pad`.
fn UnguardedUse(comptime T: type, comptime pad: bool) type {
    return struct {
        const Self = @This();
        fill: ?T,
        rest: usize = 1,

        pub fn init(fill: ?T) Self {
            if (pad) {
                std.debug.assert(fill != null);
            }
            return .{ .fill = fill };
        }

        pub fn next(self: *Self) ?T {
            return self.fill.?;
        }
    };
}

/// A second construction stores null, so the field's own guarantee is gone
/// however well the first constructor behaves.
fn SecondConstructor(comptime T: type, comptime pad: bool) type {
    return struct {
        const Self = @This();
        fill: ?T,
        rest: usize = 0,

        pub fn init(fill: ?T) Self {
            if (pad) {
                std.debug.assert(fill != null);
            }
            return .{ .fill = fill };
        }

        pub fn blank() Self {
            return .{ .fill = null };
        }

        pub fn next(self: *Self) ?T {
            if (self.rest == 0 or !pad) return null;
            return self.fill.?;
        }
    };
}

/// The field is cleared between the point the constructor guarantees and the
/// use.
fn MutatedAfterInit(comptime T: type, comptime pad: bool) type {
    return struct {
        const Self = @This();
        fill: ?T,
        rest: usize = 0,

        pub fn init(fill: ?T) Self {
            if (pad) {
                std.debug.assert(fill != null);
            }
            return .{ .fill = fill };
        }

        pub fn next(self: *Self) ?T {
            if (self.rest == 0 or !pad) return null;
            self.fill = null;
            return self.fill.?;
        }
    };
}

/// A user function named `assert` is not the stdlib assertion, so its call
/// proves nothing about the value.
fn FakeAssert(comptime T: type, comptime pad: bool) type {
    return struct {
        const Self = @This();
        fill: ?T,
        rest: usize = 0,

        fn assert(condition: bool) void {
            if (!condition) unreachable;
        }

        pub fn init(fill: ?T) Self {
            if (pad) {
                assert(fill != null);
            }
            return .{ .fill = fill };
        }

        pub fn next(self: *Self) ?T {
            if (self.rest == 0 or !pad) return null;
            return self.fill.?;
        }
    };
}

test "each container still reports its own forced unwrap" {
    _ = Unguarded(u8, true).init(null);
    _ = RuntimeFlag(u8).init(null, false);
    _ = UnguardedUse(u8, false).init(null);
    _ = SecondConstructor(u8, true).blank();
    _ = MutatedAfterInit(u8, false).init(null);
    _ = FakeAssert(u8, false).init(null);
}