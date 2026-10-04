// EXPECT: line=26 rule=optional-unwrap
// EXPECT: line=32 rule=optional-unwrap
// EXPECT: line=38 rule=optional-unwrap
// EXPECT: line=45 rule=optional-unwrap
// EXPECT: line=51 rule=optional-unwrap
//
// Only the value a local slot owns is out of reach. A write that leaves the
// slot — an element the header points at, a pointer the slot carries, or a
// slot shared by the whole container — still reaches the guarded storage and
// drops the fact.
const std = @import("std");

const State = struct {
    value: ?u32 = 5,
};

const Holder = struct {
    state: *State,
};

var shared: [4]u32 = undefined;

pub fn writesBackingElement(state: *State, out: []u32) u32 {
    std.debug.assert(state.value != null);
    out[0] = 1;
    return state.value.?;
}

pub fn writesBackingElementField(state: *State, out: []State) u32 {
    std.debug.assert(state.value != null);
    out[0].value = null;
    return state.value.?;
}

pub fn writesThroughPointerParameter(state: *State, other: *State) u32 {
    std.debug.assert(state.value != null);
    other.value = null;
    return state.value.?;
}

pub fn writesThroughStoredPointer(state: *State) u32 {
    var holder: Holder = .{ .state = state };
    std.debug.assert(state.value != null);
    holder.state.value = null;
    return state.value.?;
}

pub fn writesSharedSlot(state: *State) u32 {
    std.debug.assert(state.value != null);
    shared[0] = 1;
    return state.value.?;
}