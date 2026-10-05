// Tests that null check guards the unwrap - no warning expected
// The if (maybe != null) check proves the value is non-null in the then branch
// EXPECT: none
pub fn main() void {
    const maybe: ?u8 = 42;
    if (maybe != null) {
        const value = maybe.?;
        _ = value;
    }
}
