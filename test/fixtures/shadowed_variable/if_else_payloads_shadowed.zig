// Test: if-else error and optional payloads shadowed
// EXPECT: line=9 col=15 rule=shadowed-variable message=shadows
fn mayFail() !?i32 {
    return 42;
}

fn foo() void {
    if (mayFail()) |value| {
        const value = 0;
        _ = value;
    } else |_| {}
}

// zwanzig: not a standalone program: an if optional payload capture shadowed by a local constant of the same name is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
