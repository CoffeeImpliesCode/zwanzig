// EXPECT: none
//
// The producer fills `position` exactly for the tags the whitelist accepts,
// and the guard asks about the very same error value, so the payload unwrap
// cannot be reached with a null position. A tag whitelist says nothing about
// an arbitrary payload; here the partition and the whitelist are read off the
// same declared error set and compared tag by tag.
const std = @import("std");

const ParseError = error{ BadEscape, UnexpectedEnd, OutOfMemory };
const Info = struct { position: ?usize };

fn diagnostic(err: ParseError) Info {
    return .{ .position = switch (err) {
        error.BadEscape, error.UnexpectedEnd => 6,
        error.OutOfMemory => null,
    } };
}

fn isPositioned(err: ParseError) bool {
    return switch (err) {
        error.BadEscape, error.UnexpectedEnd => true,
        error.OutOfMemory => false,
    };
}

pub fn position(err: ParseError) ?usize {
    const info = diagnostic(err);
    if (!isPositioned(err)) return null;
    return info.position.?;
}

pub fn insideBranch(err: ParseError) ?usize {
    const info = diagnostic(err);
    if (isPositioned(err)) return info.position.?;
    return null;
}

test "the producer's error partition matches its nullable payload" {
    try std.testing.expectEqual(@as(?usize, 6), position(error.BadEscape));
    try std.testing.expectEqual(@as(?usize, 6), position(error.UnexpectedEnd));
    try std.testing.expectEqual(@as(?usize, null), position(error.OutOfMemory));
    try std.testing.expectEqual(@as(?usize, 6), insideBranch(error.BadEscape));
    try std.testing.expectEqual(@as(?usize, null), insideBranch(error.OutOfMemory));
}
