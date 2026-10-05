// EXPECT: line=2 rule=unused-decl message=value
const value = 1;

pub fn main() void {
    const items = [_]i32{1};
    for (items) |*value| {
        _ = value;
    }
}

// zwanzig: not a standalone program: for loop pointer capture shadowing container constant `value` is the intentional invalidity under test, verifying that shadowed container decls are detected as unused.
