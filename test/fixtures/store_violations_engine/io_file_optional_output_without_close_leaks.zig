const std = @import("std");

const payload = "P6\n1 1\n255\n\x00\x00\x00";

/// Control for issue #62: the file branch without its deferred close is
/// reported, while the borrowed stdout branch stays silent - the fix does not
/// come from making the borrowed handle closeable.
fn emitFileWithoutClose(out_path: ?[]const u8, io: std.Io) !void {
    if (out_path) |path| {
        var file = try std.Io.Dir.cwd().createFile(io, path, .{});
        try file.writeStreamingAll(io, payload);
    } else {
        try std.Io.File.stdout().writeStreamingAll(io, payload);
    }
}

// EXPECT: line=10 rule=store-violations-engine severity=error message=resource leak
