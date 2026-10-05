// EXPECT: none
// Zig 0.16.0 fixture: the `Io` spellings below do not exist in Zig 0.15.2.
const lib = @import("std");

/// The std namespace under another name is still the std namespace, so `cwd`
/// here is the borrowed current directory: it acquires nothing, needs no
/// close, and is never the acquisition a leak is reported against. What this
/// function opens through the same alias is owned, and is released.
fn borrowedDirectoryThroughRenamedImport(io: lib.Io, name: []const u8) !void {
    const cwd = lib.Io.Dir.cwd();
    var dir = try cwd.openDir(io, name, .{ .iterate = true });
    defer dir.close(io);
    _ = &dir;
}

/// The borrowed factory reached through the type instead of through a
/// binding, and the borrowed standard streams, likewise acquire nothing.
fn borrowedStreamsThroughRenamedImport(io: lib.Io, payload: []const u8) !void {
    try lib.Io.File.stdout().writeStreamingAll(io, payload);
    try lib.Io.File.stderr().writeStreamingAll(io, payload);
    try lib.Io.Dir.cwd().createDirPath(io, "zwanzig-fixture-alias-dir");
}
