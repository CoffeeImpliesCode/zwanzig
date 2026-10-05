// EXPECT: none
const std = @import("std");

pub fn main() !void {
    const maybe: ?u8 = 1;
    const t = std.testing;
    try t.expect(maybe != null);
    const v = maybe.?;
    _ = v;
}
