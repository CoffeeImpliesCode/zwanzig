// EXPECT: none
pub fn check() ?u8 {
    const maybe: ?u8 = 1;
    switch (maybe) {
        null => return null,
        else => |value| {
            _ = value;
        },
    }
    return maybe.?;
}
