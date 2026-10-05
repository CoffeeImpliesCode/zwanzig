// Test: if payload shadows outer declaration
// EXPECT: line=5 col=15 rule=shadowed-variable message=shadows
fn foo(opt: ?i32) void {
    const value = 1;
    if (opt) |value| {
        _ = value;
    }
    _ = value;
}

// zwanzig: not a standalone program: an if optional payload capture shadowing the enclosing function-scope constant is the intentional invalidity under test, verifying that the shadowed-variable rule reports the capture rather than the outer declaration.
