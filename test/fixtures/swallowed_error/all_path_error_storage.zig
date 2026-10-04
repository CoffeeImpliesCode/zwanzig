// EXPECT: none

const State = struct { first: ?anyerror = null, second: ?anyerror = null };
fn operation() error{Failed}!void { return error.Failed; }

pub fn unconditional(state: *State) void {
    operation() catch |err| { state.first = err; };
}

pub fn bothBranches(state: *State, first: bool) void {
    operation() catch |err| {
        if (first) { state.first = err; } else { state.second = err; }
    };
}
