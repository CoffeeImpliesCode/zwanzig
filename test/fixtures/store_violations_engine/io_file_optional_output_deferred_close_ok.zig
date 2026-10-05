// EXPECT: none
const std = @import("std");

const payload = "P6\n1 1\n255\n\x00\x00\x00";

/// Issue #62: the owned output file is released after a successful write and
/// after a write error propagates out of the function. The else branch
/// borrows `stdout()`, which acquires nothing here and must not be required to
/// close anything; the file branch closes only the file it created.
fn emitFile(out_path: ?[]const u8, io: std.Io) !void {
    if (out_path) |path| {
        var file = try std.Io.Dir.cwd().createFile(io, path, .{});
        defer file.close(io);
        try file.writeStreamingAll(io, payload);
    } else {
        try std.Io.File.stdout().writeStreamingAll(io, payload);
    }
}

/// The borrowed handle on its own: asking `stdout()` for a writer opens
/// nothing to release, so there is no close to prove and nothing to report.
fn emitToStdout(io: std.Io, bytes: []const u8) !void {
    try std.Io.File.stdout().writeStreamingAll(io, bytes);
}
