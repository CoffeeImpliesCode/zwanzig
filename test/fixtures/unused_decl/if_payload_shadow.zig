// EXPECT: line=2 rule=unused-decl message=value
const value = 1;

pub fn run(opt: ?i32) void {
    if (opt) |value| {
        _ = value;
    }
}

// zwanzig: not a standalone program: if-unwrap payload capture shadowing container constant `value` is the intentional invalidity under test, verifying that shadowed container decls are detected as unused.
