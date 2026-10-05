// EXPECT: line=23 rule=identifier-style
// #78: the type a PascalCase factory returns is a type value wherever it is
// bound, so a lowercase binding at the consumer still names a type and is
// reported. `allows_labeled_block_error_set_alias` is the same factory bound to
// a PascalCase name and stays clean.
const std = @import("std");

pub const PlainModel = struct {
    pub fn paint(self: *const PlainModel, out: []u8) !void {
        _ = self;
        _ = out;
    }
};

pub fn PaintErrorOf(comptime Model: type) type {
    return blk: {
        if (!@hasDecl(Model, "PaintError")) break :blk error{PaintUnsupported};
        break :blk Model.PaintError;
    };
}

test "a lowercase binding of an inferred error set is still a type" {
    const inferred = PaintErrorOf(PlainModel);
    try std.testing.expect(inferred == error{PaintUnsupported});
}
