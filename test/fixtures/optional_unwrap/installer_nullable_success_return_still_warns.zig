// EXPECT: line=12 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
const std = @import("std");

const Owner = struct {
    slot: ?u8 = null,
    fn start(self: *Owner, skip: bool) error{Failed}!?u8 {
        if (skip) return self.slot;
        self.slot = 1;
        return self.slot;
    }
    fn read(self: *Owner) u8 {
        return self.slot.?;
    }
    pub fn run(self: *Owner, skip: bool) !u8 {
        _ = try self.start(skip);
        return self.read();
    }
};

test "only the installing success path is called" {
    var owner: Owner = .{};
    try std.testing.expectEqual(@as(u8, 1), try owner.run(false));
}
