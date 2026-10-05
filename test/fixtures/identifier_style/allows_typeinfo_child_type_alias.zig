// EXPECT: none
// #77: the `.child` of a `@typeInfo` pointer, optional or array payload is the
// pointed-to type, so an UpperCamelCase alias of one is a type alias at file
// scope and inside a function body. `@typeInfo` itself evaluates to a
// `std.builtin.Type` union value, so only the type-carrying fields decide.
const std = @import("std");

pub const QuadSegment = extern struct {
    start: [2]f32,
    control: [2]f32,
    end: [2]f32,
};

pub const SegmentList = struct {
    items: []QuadSegment = &.{},

    pub fn count(self: *const SegmentList) usize {
        return self.items.len;
    }
};

pub const SegmentElement = @typeInfo([]QuadSegment).pointer.child;

pub const SetElement = @typeInfo([4]QuadSegment).array.child;

pub const SegmentTag = enum(u8) {
    sample,
};

pub const TagType = @typeInfo(SegmentTag).@"enum".tag_type;

pub const ReturnType = @typeInfo(fn () void).@"fn".return_type.?;

pub fn checkLayout(list: *const SegmentList) void {
    const Arc = @typeInfo(@TypeOf(list.items)).pointer.child;
    std.debug.assert(@sizeOf(Arc) == @sizeOf(QuadSegment));

    const MaybeSegment = @typeInfo(@TypeOf(@as(?QuadSegment, null))).optional.child;
    std.debug.assert(@sizeOf(MaybeSegment) == @sizeOf(QuadSegment));
}

test "reflection type fields name the element type" {
    const list: SegmentList = .{};
    checkLayout(&list);
    try std.testing.expectEqual(@as(usize, 0), list.count());
    try std.testing.expect(SegmentElement == QuadSegment);
    try std.testing.expect(SetElement == QuadSegment);
    try std.testing.expect(TagType == u8);
    try std.testing.expect(ReturnType == void);
}
