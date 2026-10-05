// EXPECT: none
// Zig 0.16.0 fixture: the `Io` spellings below do not exist in Zig 0.15.2.
const std = @import("std");

/// Issue #84: a creation error is not an opened resource - the catch arm
/// returns before any handle exists - while a successful creation registers
/// its deferred close before the fallible write, so a write error still runs
/// that close.
pub fn writeRecord(io: std.Io, dir: std.Io.Dir, name: []const u8, bytes: []const u8) !void {
    var file = dir.createFile(io, name, .{
        .truncate = false,
        .exclusive = true,
    }) catch |err| switch (err) {
        error.PathAlreadyExists => return error.RecordExists,
        else => return err,
    };
    defer file.close(io);
    try file.writeStreamingAll(io, bytes);
}

/// The already-taken exclusive create is refused, not reported: the mapping
/// arm owns nothing to release.
pub fn refuseExisting(io: std.Io, dir: std.Io.Dir, name: []const u8) !void {
    writeRecord(io, dir, name, "record\n") catch |err| switch (err) {
        error.RecordExists => return,
        else => return err,
    };
}
