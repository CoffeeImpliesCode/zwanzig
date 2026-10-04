// EXPECT: line=11 rule=divide-by-zero-engine severity=warning message=possible

const Value = enum { a, b };

pub fn wrong_label(lhs: i64, rhs: i64, value: Value) i64 {
    return switch (value) {
        .a => outer: {
            inner: {
                if (rhs == 0) break :inner;
            }
            break :outer @divTrunc(lhs, rhs);
        },
        .b => 0,
    };
}
