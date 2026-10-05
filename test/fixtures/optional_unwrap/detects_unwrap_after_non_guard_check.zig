// Tests that a null check without control flow doesn't guard a later unwrap
// EXPECT: line=8 rule=optional-unwrap message=forced optional unwrap
pub fn main() void {
    const maybe: ?u8 = null;
    if (maybe != null) {
        // The branch changes nothing, so the check only reports.
    }
    const value = maybe.?;
    _ = value;
}
