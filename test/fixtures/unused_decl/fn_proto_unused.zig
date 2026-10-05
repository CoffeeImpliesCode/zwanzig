// EXPECT: line=2 rule=unused-decl message=proto_fn
fn proto_fn() void;

// zwanzig: not a standalone program: a non-extern function without a body is an invalid Zig construct under test, verifying that unused function prototypes are detected.
