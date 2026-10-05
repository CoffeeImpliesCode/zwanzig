// EXPECT: line=32 rule=optional-unwrap
// EXPECT: line=39 rule=optional-unwrap
// EXPECT: line=47 rule=optional-unwrap
//
// A constructor declared to return an optional proves nothing, and neither
// does an assignment that runs on one branch only or a value cleared again
// before the unwrap reads it.
fn Slot(comptime T: type) type {
    return struct {
        value: T,
        pub fn init(value: T) error{Invalid}!@This() {
            if (value == 0) return error.Invalid;
            return .{ .value = value };
        }
        pub fn maybeInit(value: T) ?@This() {
            if (value == 0) return null;
            return .{ .value = value };
        }
        pub fn deinit(self: *@This()) void {
            self.value = 0;
        }
    };
}

const Owner = struct {
    slot: ?Slot(u8) = null,
};

pub fn optionalResult(value: u8) !Owner {
    var owner: Owner = .{};
    owner.slot = try Slot(u8).maybeInit(value);
    try owner.slot.?.deinit();
    return owner;
}

pub fn conditionalResult(value: u8, take: bool) !Owner {
    var owner: Owner = .{};
    if (take) owner.slot = try Slot(u8).init(value);
    try owner.slot.?.deinit();
    return owner;
}

pub fn clearedBeforeUse(value: u8) !Owner {
    var owner: Owner = .{};
    owner.slot = try Slot(u8).init(value);
    owner.slot = null;
    try owner.slot.?.deinit();
    return owner;
}
