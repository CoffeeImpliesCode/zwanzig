// EXPECT: none
const std = @import("std");

/// Issue #85: `catch null` turns the binding into an optional. The failure
/// arm holds no handle at all - the open never happened there - and the
/// success arm holds the one the deferred close releases, so neither arm
/// owes what the other settled. This is the file shape of the allocator's
/// optional-payload defer (`fp_defer_payload_optional_free.zig`).
fn readMaybe(path: []const u8) void {
    const maybe = std.fs.cwd().openFile(path, .{}) catch null;
    defer if (maybe) |file| file.close();

    if (maybe) |file| {
        _ = file;
    }
}

/// The guard is the only release on this one, and it still settles the
/// successful open: nothing here is reported, and the failure arm - which
/// reached the `defer` without ever opening anything - owes nothing.
fn readMaybeWithoutASecondUse(path: []const u8) void {
    const maybe = std.fs.cwd().openFile(path, .{}) catch null;
    defer if (maybe) |file| file.close();
}
