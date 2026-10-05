// EXPECT: none
pub fn check() ?u8 {
    const maybe: ?u8 = 1;
    if (maybe) |value| {
        _ = value;
    } else {
        return null;
    }
    return maybe.?;
}
