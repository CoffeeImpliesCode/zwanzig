const std = @import("std");

const Io = std.Io;

/// The inferred optional in the Zig 0.16 spelling: nothing writes the
/// payload's type, so the guard that captures it is the only thing that could
/// have named the file it holds. What the capture holds is the value the guard
/// unwrapped - the open that happened - and nothing at all on the arm where
/// the open failed, so the deferred close settles the whole optional.
fn inferredDeferredPayload(io: Io, dir: Io.Dir, path: []const u8) void {
    const maybe = dir.openFile(io, path, .{}) catch null;
    defer if (maybe) |file| file.close(io);
}

/// The same inferred optional released without `defer`. The guard runs on the
/// only path that holds a handle, so it releases it there and owes nothing on
/// the other.
fn inferredBodyPayload(io: Io, dir: Io.Dir, path: []const u8) void {
    const maybe = dir.openFile(io, path, .{}) catch null;
    if (maybe) |file| {
        file.close(io);
    }
}

/// A loop guard captures that same optional payload. The capture is proven from
/// the condition it was written next to, never from the name `close` and never
/// from the name the payload happens to be given.
fn inferredLoopPayload(io: Io, dir: Io.Dir, path: []const u8) void {
    const maybe = dir.openFile(io, path, .{}) catch null;
    while (maybe) |file| {
        file.close(io);
        break;
    }
}

/// The control: the first row with its release taken away. The open is real on
/// the arm that took it, so the handle is reported against the binding that
/// holds it - which is what says the three rows above released something.
fn inferredUnreleasedPayload(io: Io, dir: Io.Dir, path: []const u8) void {
    const maybe = dir.openFile(io, path, .{}) catch null;
    _ = &maybe;
}

// EXPECT: line=40 rule=store-violations-engine severity=error message=resource leak

/// The counterexample the rows above do not cover: the optional is
/// overwritten before the guard reads it, so the handle the successful open
/// produced is stranded and the binding the guard releases is nothing. A
/// guard that cannot be taken settles nothing the frame already holds, so
/// the handle stays reported against the acquisition that took it.
fn overwrittenOptional(io: Io, dir: Io.Dir, path: []const u8) void {
    var maybe = dir.openFile(io, path, .{}) catch null;
    maybe = null;
    if (maybe) |file| {
        file.close(io);
    }
}

// EXPECT: line=52 rule=store-violations-engine severity=error message=resource leak
