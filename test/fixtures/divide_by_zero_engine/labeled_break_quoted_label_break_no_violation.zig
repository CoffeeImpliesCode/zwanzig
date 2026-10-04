// EXPECT: none

const Value = enum { a, b };

// The mirror image: a plainly declared label named by an escaped `break`. The
// remainder below it would divide by zero if the transfer did not resolve.
pub fn quoted_label_break(lhs: i64, rhs: i64, value: Value) i64 {
    return switch (value) {
        .a => guarded: {
            if (rhs == 0) break :@"guarded" 0;
            break :@"guarded" @mod(lhs, rhs);
        },
        .b => 0,
    };
}
