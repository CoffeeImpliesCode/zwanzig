// Test: errdefer payload shadowed by inner declaration
// EXPECT: line=5 col=15 rule=shadowed-variable message=shadows
fn foo() !void {
    errdefer |err| {
        const err = error.Other;
        _ = err;
    }
}

// zwanzig: not a standalone program: an errdefer payload capture shadowed by a local constant of the same name is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
