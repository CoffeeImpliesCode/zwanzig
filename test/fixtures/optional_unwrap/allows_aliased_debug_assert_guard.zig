// EXPECT: none
//
// `const assert = std.debug.assert;` names the real `std.debug.assert`
// function. The alias is a declaration, so the guard is proven from the
// declaration's own initializer, not from the spelling of the callee.
const std = @import("std");
const assert = std.debug.assert;

fn bump(value: *u32) void {
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

    pub fn takeAliased(self: *State) u32 {
        assert(self.value != null);
        const result = self.value.?;
        self.value = null;
        return result;
    }

    pub fn takeAfterDisjointWrite(self: *State) u32 {
        assert(self.value != null);
        // A disjoint write between the guard and the unwrap keeps the fact.
        bump(&self.other);
        self.other += 1;
        return self.value.?;
    }
};

test "an aliased debug assert guards the unwrap it precedes" {
    var state = State.init();
    state.write(1);
    _ = state.takeAliased();
    state.write(2);
    _ = state.takeAfterDisjointWrite();
}
