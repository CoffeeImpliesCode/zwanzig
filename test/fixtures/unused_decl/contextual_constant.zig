// EXPECT: line=3 rule=unused-decl message=empty
const Unused = struct {
    const empty: @This() = .{};
};

const Assigned = struct {
    const empty: @This() = .{};
};

const Returned = struct {
    const empty: @This() = .{};
};

const Initialized = struct {
    const empty: @This() = .{};
};

pub fn reset(value: *Assigned) void {
    value.* = .empty;
}

pub fn make() error{OutOfMemory}!Returned {
    return .empty;
}

pub fn main() void {
    const value: Initialized = .empty;
    _ = value;
    _ = Unused;
}
