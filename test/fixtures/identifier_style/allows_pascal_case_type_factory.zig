// EXPECT: none
pub fn TypeFactory(comptime T: type) type {
    return struct {
        value: T,
    };
}

pub fn main() void {
    const value: TypeFactory(u8) = .{ .value = 1 };
    _ = value;
}
