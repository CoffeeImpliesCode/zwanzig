// EXPECT: none
fn foo(_ignored: i32) void {}

// zwanzig: not a standalone program: only a bare `_` is a discard in Zig, so the frontend rejects the named-but-unused parameter `_ignored` with `unused function parameter` regardless of the analyzer's opinion; this fixture asserts the unused-parameter rule stays silent for an underscore-prefixed name, and `allows_underscore_placeholder.zig` is the compiling contrast with a bare `_`.
