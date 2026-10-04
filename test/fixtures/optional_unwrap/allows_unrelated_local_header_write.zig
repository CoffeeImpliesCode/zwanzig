// EXPECT: none
// A by-value header lives in the slot that declares it, so rewriting that
// slot — `header.len`, a copy of it, or an element of a local array — reaches
// no storage the guard protects and must not cancel the proven fact.
const std = @import("std");

const State = struct {
    value: ?u32 = 5,
};

pub fn writeParameterHeader(state: *State, out: []u32) u32 {
    var header: []u32 = out;
    std.debug.assert(state.value != null);
    header.len = 0;
    _ = header.len;
    return state.value.?;
}

pub fn writeCopiedHeader(state: *State, out: []u32) u32 {
    std.debug.assert(state.value != null);
    var sink = out;
    sink.len = 0;
    _ = sink.len;
    return state.value.?;
}

pub fn writeHeaderPointer(state: *State, out: []u32) u32 {
    var header: []u32 = out;
    var buffer: [4]u32 = undefined;
    std.debug.assert(state.value != null);
    header.ptr = &buffer;
    _ = header.ptr;
    return state.value.?;
}

pub fn writeLocalArrayElement(state: *State) u32 {
    var buffer: [4]u32 = undefined;
    std.debug.assert(state.value != null);
    buffer[0] = 1;
    return state.value.?;
}

pub fn writeLocalStructField(state: *State) u32 {
    var local: State = .{};
    std.debug.assert(state.value != null);
    local.value = 9;
    return state.value.?;
}

pub fn writeCopiedLocalValue(state: *State) u32 {
    var local: State = .{};
    var copy: State = local;
    std.debug.assert(state.value != null);
    copy.value = 9;
    local.value = 9;
    return state.value.?;
}