const std = @import("std");

const Session = struct {
    io: std.Io,
    closed: bool,

    /// Takes an `io` and is named `close`, but it owns no handle: the file
    /// opened below stays held.
    fn close(self: *Session, io: std.Io) void {
        self.io = io;
        self.closed = true;
    }
};

const Sink = struct {
    /// An io-free `close` on a type that owns nothing.
    fn close(verbose: bool) void {
        _ = verbose;
    }
};

/// Neither unrelated `close` releases the file, so the handle is reported.
/// Recognizing `close(io)` is a statement about the receiver's proven
/// `std.Io` type, never about the method's name or its argument list.
fn unrelatedCloseDoesNotRelease(io: std.Io, path: []const u8) !void {
    var session = Session{ .io = io, .closed = false };
    defer session.close(io);
    defer Sink.close(false);
    var file = try std.Io.Dir.cwd().openFile(io, path, .{});
    try file.writeStreamingAll(io, "record\n");
}

// EXPECT: line=29 rule=store-violations-engine severity=error message=resource leak
