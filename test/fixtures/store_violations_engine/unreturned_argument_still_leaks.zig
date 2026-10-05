const std = @import("std");

const View = struct {
    src: []const u8,
    len: usize,
};

/// Hands back the slice it was given and never the spare one. The spare goes
/// in and nothing in the result points at it, so a caller storing the result
/// takes ownership of `src` alone.
fn makeView(n: usize, src: []const u8, spare: []const u8) View {
    _ = spare;
    return .{ .src = src, .len = n };
}

fn unreturnedArgumentStillLeaks(allocator: std.mem.Allocator, input: []const u8) !*View {
    const src = try allocator.dupe(u8, input);
    const spare = try allocator.dupe(u8, input);
    const p = try allocator.create(View);
    p.* = makeView(input.len, src, spare);
    return p;
}

// EXPECT: line=18 rule=store-violations-engine severity=error message=resource leak
