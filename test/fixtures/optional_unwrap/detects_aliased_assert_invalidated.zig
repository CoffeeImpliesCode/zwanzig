// EXPECT: line=31 rule=optional-unwrap
// EXPECT: line=37 rule=optional-unwrap
// EXPECT: line=44 rule=optional-unwrap
//
// An alias proves the same fact `std.debug.assert` would, and it stops
// proving it under exactly the same conditions: a later write to the
// guarded storage, a write through an alias, and a call that may mutate
// the storage all drop the fact.
const std = @import("std");
const assert = std.debug.assert;

fn touch(value: *u32) void {
    value.* += 1;
}

const State = struct {
    value: ?u32 = null,
    other: u32 = 0,

    fn init() State {
        return .{};
    }

    pub fn write(self: *State, value: u32) void {
        self.value = value;
    }

    pub fn takeAfterReset(self: *State) u32 {
        assert(self.value != null);
        self.value = null;
        return self.value.?; // reset after the guard
    }

    pub fn takeAfterOptionalWrite(self: *State, other: ?u32) u32 {
        assert(self.value != null);
        self.value = other;
        return self.value.?; // optional write after the guard
    }

    pub fn takeThroughAlias(self: *State) u32 {
        assert(self.value != null);
        const alias = self;
        alias.value = null;
        return self.value.?; // alias write after the guard
    }

    pub fn takeAfterCall(self: *State, other: *State, take: bool) u32 {
        assert(self.value != null);
        maybeReset(other, take);
        return self.value.?; // call may reset the guarded storage
    }

    pub fn takeDisjoint(self: *State) u32 {
        assert(self.value != null);
        touch(&self.other);
        return self.value.?; // disjoint write stays proven
    }
};

fn maybeReset(state: *State, take: bool) void {
    if (take) state.value = null;
}

test "an aliased assert is invalidated like the direct spelling" {
    var state = State.init();
    state.write(1);
    _ = state.takeAfterReset();
    _ = state.takeAfterOptionalWrite(null);
    _ = state.takeThroughAlias();
    _ = state.takeDisjoint();

    var other = State.init();
    other.write(2);
    _ = state.takeAfterCall(&other, true);
}
