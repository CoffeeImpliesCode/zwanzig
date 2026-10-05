// EXPECT: none
const std = @import("std");
// `usingnamespace` is no longer part of the language. A `const` alias is the
// spelling that keeps `expect` callable under its bare name.
const expect = std.testing.expect;

pub fn main() !void {
    const maybe: ?u8 = 1;
    try expect(maybe != null);
    const v = maybe.?;
    _ = v;
}
