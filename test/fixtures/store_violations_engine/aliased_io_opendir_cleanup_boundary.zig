const std = @import("std");
const Io = std.Io;

fn scanDir(dir: Io.Dir, io: Io, name: []const u8) !void {
    var sub = try dir.openDir(io, name, .{ .iterate = true });
    defer sub.close(io);
}

fn unsafeLeak(dir: Io.Dir, io: Io, name: []const u8) !void {
    _ = try dir.openDir(io, name, .{ .iterate = true });
}

// EXPECT: line=10 rule=store-violations-engine severity=error message=resource leak
