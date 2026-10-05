// Test: for payload shadows outer declaration
// EXPECT: line=6 col=18 rule=shadowed-variable message=shadows
fn foo() void {
    const item = 0;
    const items = [_]i32{ 1, 2, 3 };
    for (items) |item| {
        _ = item;
    }
    _ = item;
}

// zwanzig: not a standalone program: a for loop payload capture shadowing the enclosing function-scope constant is the intentional invalidity under test, verifying that the shadowed-variable rule reports the capture rather than the outer declaration.
