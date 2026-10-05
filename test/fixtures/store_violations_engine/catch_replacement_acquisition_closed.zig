// EXPECT: none
const std = @import("std");

const Io = std.Io;

/// The primary failed, so the handler opened the replacement the binding then
/// holds. Both arms produced a real handle here, and the one deferred close
/// settles whichever one this path ran.
fn replacementOpens(dir: Io.Dir, io: Io, primary: []const u8, fallback: []const u8) void {
    const file = dir.openFile(io, primary, .{}) catch try dir.openFile(io, fallback, .{});
    defer file.close(io);
}

/// The same replacement, opened under a labelled block and carried out of it.
/// The block is only the wrapper the `break :label` hands the handle through;
/// the open it made is still the binding's to release.
fn replacementOpensInBlock(dir: Io.Dir, io: Io, primary: []const u8, fallback: []const u8) !void {
    const file = dir.openFile(io, primary, .{}) catch openReplacement: {
        const replacement = dir.openFile(io, fallback, .{}) catch |err| return err;
        break :openReplacement replacement;
    };
    defer file.close(io);
}

/// A handler that hands back a handle the caller already owns binds an alias
/// rather than a second open, so the single close below releases the handle
/// this frame holds whichever name reached the binding.
fn replacementForwards(dir: Io.Dir, io: Io, owned: Io.File, primary: []const u8) void {
    const file = dir.openFile(io, primary, .{}) catch owned;
    defer file.close(io);
}

/// A failure arm that returns before the binding exists opened nothing: the
/// successful open is the only acquisition on this path and the deferred close
/// is the only release. This is the shape `examples/good_example.zig` is
/// written in.
fn failureArmOpensNothing(dir: Io.Dir, io: Io, primary: []const u8) !void {
    const file = dir.openFile(io, primary, .{}) catch |err| return err;
    defer file.close(io);
}
