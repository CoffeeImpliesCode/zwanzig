// EXPECT: line=15 rule=identifier-style
// EXPECT: line=17 rule=identifier-style
// #77 control: not every field access is a type. A plain value and a struct
// field read stay values in a file that also proves type-valued reflection
// fields, so both keep the snake_case naming rule.
const std = @import("std");

pub const Point = struct {
    x: f32,
    y: f32,
};

const origin: Point = .{ .x = 0, .y = 0 };

const MaxSegments: usize = 4096;

const OriginX: f32 = origin.x;

const Element = @typeInfo([]Point).pointer.child;

test "value constants keep their diagnoses" {
    try std.testing.expectEqual(@as(usize, 4096), MaxSegments);
    try std.testing.expectEqual(@as(f32, 0), OriginX);
    try std.testing.expect(Element == Point);
}
