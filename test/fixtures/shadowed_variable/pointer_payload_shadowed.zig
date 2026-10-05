// Test: pointer payload shadowed
// EXPECT: line=6 col=15 rule=shadowed-variable message=shadows
fn foo() void {
    var items = [_]i32{ 1, 2, 3 };
    for (&items) |*item| {
        const item = @as(*i32, undefined);
        _ = item;
    }
}

// zwanzig: not a standalone program: a for loop pointer payload capture shadowed by a local constant of the same name is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
