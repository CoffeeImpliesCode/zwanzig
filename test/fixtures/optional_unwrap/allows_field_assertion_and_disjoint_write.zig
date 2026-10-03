// EXPECT: none
const std = @import("std");

const State = struct {
    value: ?u32,
    other: u32,
};

fn bump(value: *u32) void {
    value.* += 1;
}

pub fn readChecked(state: *State) !u32 {
    try std.testing.expect(state.value != null);
    bump(&state.other);
    return state.value.?;
}

pub fn readAsserted(state: *State) u32 {
    std.debug.assert(state.value != null);
    return state.value.?;
}
