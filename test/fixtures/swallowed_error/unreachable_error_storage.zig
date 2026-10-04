// EXPECT: line=7 rule=swallowed-error

const State = struct { saved: ?anyerror = null, ignored: bool = false };
fn operation() error{Failed}!void { return error.Failed; }

pub fn record(state: *State) void {
    operation() catch |err| {
        if (false) { state.saved = err; }
        state.ignored = true;
    };
}
