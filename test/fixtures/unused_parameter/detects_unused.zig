// EXPECT: line=2 rule=unused-parameter message=Unused parameter 'unused_param'
fn foo(unused_param: i32, used: i32) void {
    _ = used;
}

// zwanzig: not a standalone program: the unused function parameter `unused_param` is the intentional invalidity under test, verifying that an unused parameter is detected, but Zig rejects it as `unused function parameter` before any analysis can run.
