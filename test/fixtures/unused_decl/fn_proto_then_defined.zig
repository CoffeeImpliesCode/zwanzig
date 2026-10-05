// EXPECT: none
fn helper() void;

fn helper() void {}

pub fn main() void {
    helper();
}

// zwanzig: not a standalone program: duplicate function member declaration `helper` is the pattern under test, verifying that a prototype followed by a definition is not flagged as unused.
