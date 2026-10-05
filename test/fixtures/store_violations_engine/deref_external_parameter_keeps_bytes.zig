const std = @import("std");

const Out = struct {
    text: []u8,
};

/// The store writes into the block the `out` parameter names, which is a
/// block in the caller's frame. The duplicated bytes ride out of this function
/// with it and the caller releases them once, so nothing is left unreleased
/// behind and the store is not a leak.
fn fillFromCallerBlock(a: std.mem.Allocator, out: *Out) !void {
    const text = try a.dupe(u8, "kept bytes");
    out.* = .{ .text = text };
}

/// The same store into a block this function built. Nothing releases the bytes
/// and nothing carries them out, so the store is not a release and they are
/// still reported here.
fn fillFromLocalBlock(a: std.mem.Allocator, input: []const u8) !void {
    var local: Out = undefined;
    const text = try a.dupe(u8, input);
    (@as(*Out, &local)).* = .{ .text = text };
}

/// The out-parameter whose pointee cannot hold a reference. `length.* =
/// bytes.len` writes a length, so the store hands the block nothing to own and
/// the bytes stay this function's to release - which it never does, whichever
/// frame the block itself belongs to. The caller owning the block is not the
/// same fact as the block being able to hold the bytes.
fn storeLengthFromCallerBlock(a: std.mem.Allocator, input: []const u8, length: *usize) !void {
    const bytes = try a.dupe(u8, input);
    length.* = bytes.len;
}

test "the caller's block keeps the bytes the store wrote into it" {
    const a = std.testing.allocator;
    var out: Out = undefined;
    try fillFromCallerBlock(a, &out);
    defer a.free(out.text);
    try std.testing.expectEqualStrings("kept bytes", out.text);
}

// EXPECT: line=21 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=31 rule=store-violations-engine severity=error message=resource leak
