// EXPECT: none
// Zig 0.16.0 fixture: the `Io` spellings below do not exist in Zig 0.15.2.
const std = @import("std");

const WriteError = std.mem.Allocator.Error || std.Io.File.Writer.Error || std.Io.File.OpenError;

const document = "<svg xmlns=\"http://www.w3.org/2000/svg\"/>";

/// Issue #63: the caller-supplied directory stays borrowed and is never
/// closed here. The rendered buffer is an allocation and the created file is
/// a handle; each is released on a normal return, on a propagated write error,
/// and the buffer is still freed when the file creation fails after it.
fn writeFile(
    gpa: std.mem.Allocator,
    io: std.Io,
    dir: std.Io.Dir,
    path: []const u8,
) WriteError!void {
    const svg = try gpa.dupe(u8, document);
    defer gpa.free(svg);
    var file = try std.Io.Dir.createFile(dir, io, path, .{});
    defer file.close(io);
    try file.writeStreamingAll(io, svg);
}
