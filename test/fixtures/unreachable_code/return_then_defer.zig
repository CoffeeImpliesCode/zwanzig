// EXPECT: line=4 rule=unreachable-code
fn returnThenDefer() void {
    return;
    defer foo();
}

fn foo() void {}

// zwanzig: not a standalone program: `defer` immediately following `return` is a compile error in Zig, representing the exact unreachable code pattern under test.
