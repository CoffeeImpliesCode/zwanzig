// EXPECT: line=10 rule=optional-unwrap
const Entry = struct { value: ?u8 };

const Namespace = if (@as(?Entry, .{ .value = 1 })) |entry| struct {
    pub fn guarded() u8 {
        return if (entry.value != null) entry.value.? else 0;
    }

    pub fn unchecked() u8 {
        return entry.value.?;
    }
} else struct {};

pub fn main() void {
    _ = Namespace.guarded();
    _ = Namespace.unchecked();
}
