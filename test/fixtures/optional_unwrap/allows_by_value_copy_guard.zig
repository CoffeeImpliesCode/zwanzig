// EXPECT: none
//
// A by-value receiver copies each field it writes. Those copies own their own
// bytes, so writing one is not writing through an alias to the receiver and
// the null guard on `tag` still holds at the unwrap.
const std = @import("std");

const Flags = struct { first: bool = false, second: bool = false };

const Packet = struct {
    tag: ?u8,
    flags: Flags,

    pub fn matches(self: Packet, tag: u8, flags: Flags) bool {
        if (self.tag == null) return false;
        var normalized = self.flags;
        normalized.first = false;
        normalized.second = false;
        var expected = flags;
        expected.first = false;
        expected.second = false;
        return tag == self.tag.? and std.meta.eql(normalized, expected);
    }
};

test "writes to independent value copies preserve the packet's null guard" {
    const packet: Packet = .{ .tag = 7, .flags = .{ .first = true } };
    try std.testing.expect(packet.matches(7, .{}));
    try std.testing.expect(!packet.matches(8, .{}));
    const empty: Packet = .{ .tag = null, .flags = .{} };
    try std.testing.expect(!empty.matches(7, .{}));
}
