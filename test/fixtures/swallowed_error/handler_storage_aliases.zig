// EXPECT: line=15 rule=swallowed-error
pub const State = struct {
    saved: ?anyerror = null,
    ignored: bool = false,
    pub fn capture(self: *State) void {
        fail() catch |err| {
            const outside = self;
            outside.saved = err;
        };
        fail() catch |err| {
            const slot = &self.saved;
            const alias = slot;
            alias.* = err;
        };
        fail() catch |err| {
            var local: ?anyerror = null;
            const slot = &local;
            slot.* = err;
            self.ignored = local != null;
        };
    }
};
fn fail() !void {
    return error.Bad;
}
