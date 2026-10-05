// EXPECT: none

// Zig 0.16.0 fixture: `std.Io.Dir` and `std.process.Init` do not exist in Zig
// 0.15.2, which spells this open through `std.fs`; the two trees share no
// spelling the resource model still reads as an acquisition, so the fixture
// names its frontend instead of branching on one. A comptime `if` around the
// open would hide the acquisition from the checker, which resolves `try`,
// `catch`, `unwrap` and grouping but not `if`.
const std = @import("std");

/// Issue #85: a file acquired through a `catch` and released with `defer`
/// leaks nothing. The failure arm returns before the binding exists - the
/// open failed there, so no handle was ever produced to release - and the
/// success arm holds the one the deferred close releases. This is the shape
/// `examples/good_example.zig` is written in, in its Zig 0.16.0 spelling: the
/// directory comes from the borrowed `Io.Dir.cwd` factory and the I/O instance
/// arrives with the process, so neither is acquired here.
pub fn main(init: std.process.Init) !void {
    const file = std.Io.Dir.cwd().openFile(init.io, "test.txt", .{}) catch |err| {
        std.debug.print("Failed to open file: {}\n", .{err});
        return err;
    };
    defer file.close(init.io);
}
