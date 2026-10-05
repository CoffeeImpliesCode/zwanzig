// EXPECT: line=27 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=52 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=73 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=97 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
//
// Every iterator below has the padded shape, and every one of them unwraps a
// fill that nothing in this file establishes. Only a private factory whose
// own assertion is the last word about the field proves one.
const std = @import("std");

/// A public factory: code outside this file builds this iterator, so what
/// this constructor asserts is not the last word about the field.
pub fn ExportedIterator(comptime pad: bool) type {
    return struct {
        const Self = @This();
        remaining: usize,
        fill: ?u8,

        fn init(remaining: usize, fill: ?u8) Self {
            if (pad) std.debug.assert(fill != null);
            return .{ .remaining = remaining, .fill = fill };
        }

        fn next(self: *Self) ?u8 {
            if (self.remaining == 0 or !pad) return null;
            self.remaining -= 1;
            return self.fill.?;
        }
    };
}

/// A second constructor of the same type stores a null fill, so the guarded
/// one is not every value this type is built from.
fn BlankIterator(comptime pad: bool) type {
    return struct {
        const Self = @This();
        remaining: usize,
        fill: ?u8,

        fn init(remaining: usize, fill: ?u8) Self {
            if (pad) std.debug.assert(fill != null);
            return .{ .remaining = remaining, .fill = fill };
        }

        fn blank() Self {
            return .{ .remaining = 0, .fill = null };
        }

        fn next(self: *Self) ?u8 {
            if (self.remaining == 0 or !pad) return null;
            self.remaining -= 1;
            return self.fill.?;
        }
    };
}

/// A user function where the assertion belongs: it proves nothing about what
/// the constructor stored.
fn FakeAssertIterator(comptime pad: bool) type {
    return struct {
        const Self = @This();
        remaining: usize,
        fill: ?u8,

        fn init(remaining: usize, fill: ?u8) Self {
            if (pad) assertFill(fill != null);
            return .{ .remaining = remaining, .fill = fill };
        }

        fn next(self: *Self) ?u8 {
            if (self.remaining == 0 or !pad) return null;
            self.remaining -= 1;
            return self.fill.?;
        }
    };
}

fn assertFill(condition: bool) void {
    _ = condition;
}

/// The guarded construction, then a write that clears what it stored.
fn ClearedIterator(comptime pad: bool) type {
    return struct {
        const Self = @This();
        remaining: usize,
        fill: ?u8,

        fn init(remaining: usize, fill: ?u8) Self {
            if (pad) std.debug.assert(fill != null);
            return .{ .remaining = remaining, .fill = fill };
        }

        fn next(self: *Self) ?u8 {
            if (self.remaining == 0 or !pad) return null;
            self.remaining -= 1;
            return self.fill.?;
        }
    };
}

pub fn main() void {
    var exported = ExportedIterator(true).init(2, 7);
    _ = exported.next();

    var blanked = BlankIterator(true).blank();
    _ = blanked.next();

    var faked = FakeAssertIterator(true).init(2, 7);
    _ = faked.next();

    var cleared = ClearedIterator(true).init(2, 7);
    cleared.fill = null;
    _ = cleared.next();
}
