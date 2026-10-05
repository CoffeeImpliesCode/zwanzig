const std = @import("std");

const WriteError = std.mem.Allocator.Error || std.Io.File.Writer.Error || std.Io.File.OpenError;

const document = "<svg xmlns=\"http://www.w3.org/2000/svg\"/>";

/// Control for issue #63: dropping only the file close reports the handle at
/// its own binding. The buffer keeps its free, so this is one handle leak and
/// never an allocation leak.
fn writeFileWithoutHandleClose(
    gpa: std.mem.Allocator,
    io: std.Io,
    dir: std.Io.Dir,
    path: []const u8,
) WriteError!void {
    const svg = try gpa.dupe(u8, document);
    defer gpa.free(svg);
    var file = try std.Io.Dir.createFile(dir, io, path, .{});
    try file.writeStreamingAll(io, svg);
}

// EXPECT: line=18 rule=store-violations-engine severity=error message=resource leak
