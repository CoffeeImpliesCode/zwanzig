const std = @import("std");

const Payload = struct {
    src: []const u8,
};

/// Builds its result out of the argument it was handed, so the caller's
/// block rides out inside the returned value.
fn parseInto(src: []const u8) error{EmptySource}!Payload {
    if (src.len == 0) return error.EmptySource;
    return .{ .src = src };
}

/// The store hands the duplicated bytes to the pointee, and a store is a
/// retain rather than a release: nothing returns the pointee and nothing
/// disposes it, so both the bytes it took and the block it was written into
/// stay reported here.
fn droppedPointeeStillLeaks(allocator: std.mem.Allocator, input: []const u8) !usize {
    const owned = try allocator.dupe(u8, input);
    const p = try allocator.create(Payload);
    p.* = try parseInto(owned);
    return p.src.len;
}

// EXPECT: line=19 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=20 rule=store-violations-engine severity=error message=resource leak
