// Test: if optional unwrap payload shadowed by inner declaration
// EXPECT: line=5 col=15 rule=shadowed-variable message=shadows
fn foo(opt: ?i32) void {
    if (opt) |value| {
        const value = 0;
        _ = value;
    }
}

// zwanzig: not a standalone program: an if optional payload capture shadowed by a local constant of the same name is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
