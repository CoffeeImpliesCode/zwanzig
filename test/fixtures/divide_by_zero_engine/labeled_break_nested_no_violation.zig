// EXPECT: none

const Value = enum { a, b };

pub fn nested_label(lhs: i64, rhs: i64, value: Value) i64 {
    return switch (value) {
        .a => outer: {
            {
                if (rhs == 0) break :outer 0;
            }
            break :outer @divTrunc(lhs, rhs);
        },
        .b => 0,
    };
}
