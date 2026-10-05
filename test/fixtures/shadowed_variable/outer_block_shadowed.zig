// Test: outer block variable shadowed by inner block variable
// EXPECT: line=6 col=15 rule=shadowed-variable message=shadows
fn foo() void {
    const value = 5;
    {
        const value = 10;
        _ = value;
    }
    _ = value;
}

// zwanzig: not a standalone program: a bare block constant shadowing the enclosing function-scope constant is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
