// EXPECT: line=8 rule=identifier-style
// EXPECT: line=10 rule=identifier-style
// #78 control: a labeled block that yields a number yields a value, so an
// UpperCamelCase alias of one still needs snake_case. The lowercase alias of the
// same block shape is the control that the value rule accepts.
const fallback_max: usize = 32;

const MaxLayers: usize = 32;

const BoundedMax: usize = blk: {
    if (fallback_max > 0) break :blk fallback_max;
    break :blk 64;
};

const clamped_max: usize = blk: {
    if (fallback_max > 0) break :blk fallback_max;
    break :blk 64;
};

test "value blocks keep the value rule" {
    const std = @import("std");
    try std.testing.expectEqual(@as(usize, 32), MaxLayers);
    try std.testing.expectEqual(@as(usize, 32), BoundedMax);
    try std.testing.expectEqual(@as(usize, 32), clamped_max);
}
