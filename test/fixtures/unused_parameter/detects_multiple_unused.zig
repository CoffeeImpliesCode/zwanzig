// EXPECT: line=3 rule=unused-parameter message=Unused parameter 'a'
// EXPECT: line=3 rule=unused-parameter message=Unused parameter 'b'
fn foo(a: i32, b: i32, used: i32) void {
    _ = used;
}

// zwanzig: not a standalone program: the unused function parameters `a` and `b` are the intentional invalidity under test, verifying that each unused parameter is reported, but Zig rejects them as `unused function parameter` before any analysis can run.
