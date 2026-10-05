const std = @import("std");

/// A `usize` pointee cannot hold a reference, so the store below writes a
/// number into it and hands it nothing. Returning the pointer carries that
/// integer to the caller and leaves the duplicated bytes exactly where they
/// were, unreleased and reported.
fn pointerToLen(allocator: std.mem.Allocator, input: []const u8) !*usize {
    const bytes = try allocator.dupe(u8, input);
    const p: *usize = try allocator.create(usize);
    p.* = bytes.len;
    return p;
}

// EXPECT: line=8 rule=store-violations-engine severity=error message=resource leak
