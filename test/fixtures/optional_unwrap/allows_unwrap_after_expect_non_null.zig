// EXPECT: none
const std = @import("std");

pub fn main() !void {
    const maybe: ?u8 = 1;
    try std.testing.expect(maybe != null);
    const v = maybe.?;
    _ = v;
}
