// EXPECT: none
// #78: a labeled block produces the value of every `break :label` expression
// that can leave it. Every break here yields a closed error set, so the alias
// names a type and keeps its PascalCase name, including the break that yields
// a namespace member alias and the break nested inside another block. An
// error-union alias and an alias of an error set a factory infers name a type
// the same way, so they keep their PascalCase names as well.
const std = @import("std");

pub const InkModel = struct {
    pub const PaintError = error{ NoPalette, UnsupportedEncoding };

    pub fn paint(self: *const InkModel, out: []u8) PaintResult {
        _ = self;
        _ = out;
    }
};

pub const PlainModel = struct {
    pub fn paint(self: *const PlainModel, out: []u8) PlainPaintError!void {
        _ = self;
        _ = out;
    }
};

pub const PaintError = blk: {
    if (!@hasDecl(InkModel, "PaintError")) break :blk error{PaintUnsupported};
    const Declared = InkModel.PaintError;
    if (Declared == anyerror) @compileError("the declared set must be closed");
    break :blk Declared;
};

pub fn PaintErrorOf(comptime Model: type) type {
    return blk: {
        if (!@hasDecl(Model, "PaintError")) break :blk error{PaintUnsupported};
        break :blk Model.PaintError;
    };
}

pub const PlainPaintError = PaintErrorOf(PlainModel);

pub const PaintResult = InkModel.PaintError!void;

pub const NestedError = outer: {
    break :outer inner: {
        break :inner error{InnerMissing};
    };
};

test "closed error sets round-trip" {
    try std.testing.expect(PaintError == error{ NoPalette, UnsupportedEncoding });
}
