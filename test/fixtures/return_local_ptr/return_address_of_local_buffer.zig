// Zig 0.15.2 fixture: returning the address of an expired local is a compile
// error on 0.16.0, so the gate checks this shape on the frontend that has it.
// EXPECT: line=6 rule=return-local-ptr severity=warning
fn bad() *[2]u32 {
    var buf: [2]u32 = undefined;
    return &buf;
}
