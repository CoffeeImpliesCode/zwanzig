const std = @import("std");

const WriteError = std.mem.Allocator.Error || std.Io.File.Writer.Error || std.Io.File.OpenError;

const document = "<svg xmlns=\"http://www.w3.org/2000/svg\"/>";

/// Control for issue #63: dropping only the buffer free reports the
/// allocation at its own binding. The file handle keeps its close, so this is
/// one allocation leak and never a handle leak.
fn writeFileWithoutBufferFree(
    gpa: std.mem.Allocator,
    io: std.Io,
    dir: std.Io.Dir,
    path: []const u8,
) WriteError!void {
    const svg = try gpa.dupe(u8, document);
    var file = try std.Io.Dir.createFile(dir, io, path, .{});
    defer file.close(io);
    try file.writeStreamingAll(io, svg);
}

// EXPECT: line=16 rule=store-violations-engine severity=error message=resource leak
