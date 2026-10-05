const std = @import("std");
const Io = std.Io;

/// Control for issue #62's second reducer: the same alias and the same
/// supplied directory, with the release removed. The discarded open is the
/// one resource the function acquires, and it is reported where it happens.
fn unsafeLeak(dir: Io.Dir, io: Io, path: []const u8) !void {
    _ = try dir.openFile(io, path, .{});
}

/// A method named `close` that takes the runtime is not a release by itself.
/// `Fake` is the caller's own type, so proving the alias proves nothing about
/// this call, and the handle it ignored is still held.
const Fake = struct {
    fn close(fake: Fake, io: Io) void {
        _ = fake;
        _ = io;
    }
};

fn fakeCloseKeepsTheLeak(dir: Io.Dir, io: Io, path: []const u8) !void {
    var file = try dir.openFile(io, path, .{});
    var fake = Fake{};
    fake.close(io);
    try file.writeStreamingAll(io, "held\n");
}

// EXPECT: line=8 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=22 rule=store-violations-engine severity=error message=resource leak
