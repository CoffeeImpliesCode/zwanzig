// EXPECT: none

const Value = enum { a, b };

// `@"guarded"` is the same identifier as `guarded`, so a plain `break :guarded`
// still names this block and the division below it stays guarded.
pub fn quoted_label_decl(lhs: i64, rhs: i64, value: Value) i64 {
    return switch (value) {
        .a => @"guarded": {
            if (rhs == 0) break :guarded 0;
            break :guarded @divTrunc(lhs, rhs);
        },
        .b => 0,
    };
}
