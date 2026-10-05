// Test: if-else error payload shadows outer declaration
// EXPECT: line=11 col=13 rule=shadowed-variable message=shadows
fn mayFail() !i32 {
    return 1;
}

fn foo() void {
    const err = error.Other;
    if (mayFail()) |value| {
        _ = value;
    } else |err| {
        _ = err;
    }
    _ = err;
}

// zwanzig: not a standalone program: an if-else error payload capture shadowing the enclosing function-scope constant is the intentional invalidity under test, verifying that the shadowed-variable rule reports the capture rather than the outer declaration.
