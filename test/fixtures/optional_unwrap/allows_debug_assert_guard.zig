// EXPECT: none
const std = @import("std");

pub fn main() void {
    const maybe: ?u8 = 1;
    std.debug.assert(maybe != null);
    const value = maybe.?;
    _ = value;
}
