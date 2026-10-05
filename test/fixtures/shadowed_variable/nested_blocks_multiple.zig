// Test: multiple nested block shadows
// EXPECT: line=7 col=15 rule=shadowed-variable message=shadows
// EXPECT: line=9 col=19 rule=shadowed-variable message=shadows
fn foo() void {
    const x = 1;
    {
        const x = 2;
        {
            const x = 3;
            _ = x;
        }
        _ = x;
    }
    _ = x;
}

// zwanzig: not a standalone program: two nested block constants each shadowing the same name from outer scopes are the intentional invalidity under test, verifying that both shadowing declarations are reported.
