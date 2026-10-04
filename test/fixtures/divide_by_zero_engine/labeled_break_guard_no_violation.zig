// EXPECT: none

const Value = enum { a, b };

pub fn guarded(lhs: i64, rhs: i64, value: Value) i64 {
    return switch (value) {
        .a => blk: {
            if (rhs == 0) break :blk 0;
            break :blk @divTrunc(lhs, rhs);
        },
        .b => 0,
    };
}
