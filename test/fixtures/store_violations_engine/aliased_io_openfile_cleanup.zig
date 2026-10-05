// EXPECT: none
const std = @import("std");

/// Issue #62's second reducer: the standard library's `Io` reached through an
/// alias, and the directory supplied as a parameter instead of opened here.
/// `Io.Dir` is proven from what `Io` was given to it, so the handle the
/// deferred close releases is the real one - not a type that happens to be
/// spelled the same way.
const Io = std.Io;

/// The success arm holds a file and registers its close before returning. The
/// failing arm produces no handle, so there is nothing there to release.
fn viaTry(dir: Io.Dir, io: Io, path: []const u8) !void {
    var file = try dir.openFile(io, path, .{});
    defer file.close(io);
}

/// The same lifetime written with an explicit catch: the binding only ever
/// holds the successful open.
fn viaCatch(dir: Io.Dir, io: Io, path: []const u8) !void {
    const file = dir.openFile(io, path, .{}) catch |err| return err;
    defer file.close(io);
}

/// Mapping one failure to another still leaves the failed open empty, and the
/// deferred close runs for the open that did happen.
fn viaMappedError(dir: Io.Dir, io: Io, path: []const u8) !void {
    const file = dir.openFile(io, path, .{}) catch |err| switch (err) {
        error.FileNotFound => return error.MissingFixture,
        else => return err,
    };
    defer file.close(io);
}

/// The borrowed factory reached through the alias borrows like the one reached
/// by its real name: it acquires nothing, needs no close, and is never the
/// acquisition a leak is reported against.
fn borrowedThroughAlias(io: Io, payload: []const u8) !void {
    try Io.File.stdout().writeStreamingAll(io, payload);
    const cwd = Io.Dir.cwd();
    var dir = try cwd.openDir(io, "zwanzig-fixture-alias-dir", .{ .iterate = true });
    defer dir.close(io);
    _ = &dir;
}
