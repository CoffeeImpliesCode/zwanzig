// Test: while loop payload shadowed by inner declaration
// EXPECT: line=6 col=15 rule=shadowed-variable message=shadows
fn bar(opt: ?i32) void {
    var x = opt;
    while (x) |value| {
        const value = 0;
        x = null;
        _ = value;
    }
}

// zwanzig: not a standalone program: a while optional payload capture shadowed by a local constant of the same name is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
