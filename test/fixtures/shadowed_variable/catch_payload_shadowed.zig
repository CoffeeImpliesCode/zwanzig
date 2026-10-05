// Test: catch error payload shadowed by inner declaration
// EXPECT: line=7 col=15 rule=shadowed-variable message=shadows
fn mayFail() !void {}

fn foo() void {
    mayFail() catch |err| {
        const err = error.Other;
        _ = err;
    };
}

// zwanzig: not a standalone program: a catch error payload capture shadowed by a local constant of the same name is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
