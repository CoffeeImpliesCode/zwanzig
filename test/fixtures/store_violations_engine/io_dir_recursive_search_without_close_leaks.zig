const std = @import("std");

/// Control for the recursive search above: with the deferred close removed
/// the acquired directory is reported again, so the safe case is quiet
/// because the release is proven and not because the open went unnoticed.
fn searchWithoutClose(io: std.Io, root: []const u8, name: []const u8) ?[]const u8 {
    var dir = std.Io.Dir.openDir(.cwd(), io, root, .{ .iterate = true }) catch return null;
    var it = dir.iterate();
    while (it.next(io) catch return null) |entry| {
        if (std.mem.startsWith(u8, entry.name, name)) return root;
    }
    return null;
}

// EXPECT: line=7 rule=store-violations-engine severity=error message=resource leak
