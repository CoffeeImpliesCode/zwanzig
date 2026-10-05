// Test: deeply nested shadowing through various constructs
// EXPECT: line=8 col=23 rule=shadowed-variable message=shadows
fn foo(items: []const ?i32) void {
    const result: i32 = 0;
    for (items) |maybe| {
        if (maybe) |value| {
            {
                const result = value;
                _ = result;
            }
        }
    }
    _ = result;
}

// zwanzig: not a standalone program: a function-scope constant shadowed by a constant inside a bare block nested under a for capture and an if capture is the intentional invalidity under test, verifying that shadowing is detected across several nesting levels.
