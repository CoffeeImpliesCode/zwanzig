// EXPECT: none
//
// A generic type factory's constructor declares a result that cannot be null,
// so the assignment carries that fact forward. The later `errdefer` keeps it:
// its body runs only on the error exit the successful call has already left.
fn Resource(comptime T: type) type {
    return struct {
        value: T,
        pub fn init(value: T) error{Invalid}!@This() {
            if (value == 0) return error.Invalid;
            return .{ .value = value };
        }
        pub fn deinit(self: *@This()) void {
            self.value = 0;
        }
        pub fn update(self: *@This(), value: T) error{Invalid}!void {
            self.value = value;
        }
    };
}

const Owner = struct {
    resource: ?Resource(u8) = null,
};

pub fn construct(value: u8) !Owner {
    var owner: Owner = .{};
    owner.resource = try Resource(u8).init(value);
    errdefer owner.resource.?.deinit();
    try owner.resource.?.update(value);
    return owner;
}
