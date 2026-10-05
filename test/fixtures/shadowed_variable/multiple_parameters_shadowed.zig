// Test: multiple parameters shadowed
// EXPECT: line=5 col=11 rule=shadowed-variable message=shadows
// EXPECT: line=6 col=11 rule=shadowed-variable message=shadows
fn foo(a: i32, b: i32) void {
    const a = 1;
    const b = 2;
    _ = a;
    _ = b;
}

// zwanzig: not a standalone program: two function parameters shadowed by local constants of the same names are the intentional invalidity under test, verifying that every shadowing declaration is reported.
