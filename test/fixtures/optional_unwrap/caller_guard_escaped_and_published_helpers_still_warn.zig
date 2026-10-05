// EXPECT: line=16 rule=optional-unwrap severity=warning
// EXPECT: line=37 rule=optional-unwrap severity=warning
//
// A method taken as a value, and a method reachable from outside this file,
// both have callers this analysis cannot read. Neither inherits a guard.
const std = @import("std");

const Band = struct {
    width: u16 = 80,
};

const EscapedHelper = struct {
    field: ?Band = null,

    fn readEscapedWidth(self: *EscapedHelper) u16 {
        return self.field.?.width;
    }

    fn run(self: *EscapedHelper) u16 {
        if (self.field != null) {
            const alias: *const fn (*EscapedHelper) u16 = EscapedHelper.readEscapedWidth;
            _ = alias;
            return self.readEscapedWidth();
        }
        return 0;
    }
};

pub const PublishedBand = struct {
    width: u16 = 80,
};

pub const PublishedHelper = struct {
    field: ?PublishedBand = null,

    pub fn readPublishedWidth(self: *PublishedHelper) u16 {
        return self.field.?.width;
    }

    fn run(self: *PublishedHelper) u16 {
        if (self.field != null) {
            return self.readPublishedWidth();
        }
        return 0;
    }
};

test "escapes: the taken and published helpers still warn" {
    var escaped: EscapedHelper = .{ .field = Band{} };
    var published: PublishedHelper = .{ .field = PublishedBand{} };
    try std.testing.expectEqual(@as(u16, 80), escaped.run());
    try std.testing.expectEqual(@as(u16, 80), published.run());
}
