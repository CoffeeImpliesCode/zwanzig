// Test: function parameter shadowed by local variable
// EXPECT: line=4 col=11 rule=shadowed-variable message=shadows
fn foo(x: i32) void {
    const x = 5;
    _ = x;
}

// zwanzig: not a standalone program: a function parameter shadowed by a local constant of the same name is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
