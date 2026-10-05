// EXPECT: line=15 rule=unreachable-code-engine
// A user module spelled `std` names no assertion, so a comptime branch that
// calls its `debug.assert` runs ordinary dead code and stays reportable.
const std = struct {
    pub const debug = struct {
        pub fn assert(ok: bool) void {
            if (!ok) @panic("fake assertion");
        }
    };
};

comptime {
    const limit: usize = 80;
    const worst: usize = 77;
    if (worst > limit) {
        std.debug.assert(worst <= limit);
    }
}
