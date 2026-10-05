// Test: var shadowing var
// EXPECT: line=6 col=13 rule=shadowed-variable message=shadows
fn foo() void {
    var x: i32 = 1;
    {
        var x: i32 = 2;
        x += 1;
        _ = x;
    }
    x += 1;
    _ = x;
}

// zwanzig: not a standalone program: a variable in an inner block shadowing a variable from the outer scope is the intentional invalidity under test, verifying that the shadowed-variable rule reports variable shadowing as well as constants.
