const std = @import("std");

/// Control for issue #84: the same exclusive create with its deferred close
/// removed is reported at the file binding, while the creation-error mapping
/// keeps the failure arm free of any handle.
pub fn lostMappedFile(io: std.Io, dir: std.Io.Dir, name: []const u8) !void {
    var file = dir.createFile(io, name, .{
        .truncate = false,
        .exclusive = true,
    }) catch |err| switch (err) {
        error.PathAlreadyExists => return error.RecordExists,
        else => return err,
    };
    try file.writeStreamingAll(io, "record\n");
}

// EXPECT: line=7 rule=store-violations-engine severity=error message=resource leak
