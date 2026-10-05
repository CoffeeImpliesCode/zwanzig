// EXPECT: line=31 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
//
// The one report here is `unsafeRead`: nothing in this file establishes that
// a plain optional parameter is non-null. The private factory's own assertion
// proves `fill` for `Iterator(true)`, and `next` returns before its unwrap
// whenever `pad` is false, so the iterator needs nothing else. The unrelated
// public function receives no iterator, and the address taken of it only
// keeps the declaration referenced, so neither reaches the field.
const std = @import("std");

fn Iterator(comptime pad: bool) type {
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

pub fn unsafeRead(value: ?u8) u8 {
    return value.?;
}

test "padding requires a fill and non-padding never unwraps it" {
    var padded = Iterator(true).init(2, 7);
    try std.testing.expectEqual(@as(?u8, 7), padded.next());
    try std.testing.expectEqual(@as(?u8, 7), padded.next());
    try std.testing.expectEqual(@as(?u8, null), padded.next());
    var unpadded = Iterator(false).init(2, null);
    try std.testing.expectEqual(@as(?u8, null), unpadded.next());
    _ = &unsafeRead;
}
