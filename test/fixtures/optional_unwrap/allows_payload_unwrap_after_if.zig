// EXPECT: none
pub fn main() void {
    const maybe: ?u8 = 1;
    if (maybe) |value| {
        _ = value;
        _ = maybe.?;
    }
}
