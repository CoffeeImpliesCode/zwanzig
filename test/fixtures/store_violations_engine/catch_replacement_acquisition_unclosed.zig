const std = @import("std");

const Io = std.Io;

/// The handler opened the replacement on the arm where the primary failed and
/// nothing releases it. That arm really did acquire a handle, so treating every
/// caught failure as an empty binding would drop the fallback's obligation
/// along with the primary's call.
fn replacementTryLeaks(dir: Io.Dir, io: Io, primary: []const u8, fallback: []const u8) void {
    const file = dir.openFile(io, primary, .{}) catch try dir.openFile(io, fallback, .{});
    _ = file;
}

/// The failure arm returns before the binding exists, so the successful open is
/// the only acquisition on this path and nothing releases it.
fn primaryLeaks(dir: Io.Dir, io: Io, primary: []const u8) !void {
    const file = dir.openFile(io, primary, .{}) catch |err| return err;
    _ = file;
}

/// The replacement is opened inside the handler's block and handed out of it.
/// The binding aliases that handle instead of opening a second one, so the
/// region the handler acquired is the one nothing releases, and the primary's
/// own open on the other arm is a second, separate leak.
fn replacementBlockLeaks(dir: Io.Dir, io: Io, primary: []const u8, fallback: []const u8) void {
    const file = dir.openFile(io, primary, .{}) catch openReplacement: {
        const replacement = dir.openFile(io, fallback, .{}) catch return;
        break :openReplacement replacement;
    };
    _ = file;
}

/// A handler that forwards a handle this frame opened binds an alias, so both
/// spellings name one region on the failure arm and neither is released.
fn replacementForwardsLeak(dir: Io.Dir, io: Io, primary: []const u8, fallback: []const u8) void {
    const replacement = dir.openFile(io, fallback, .{}) catch return;
    const file = dir.openFile(io, primary, .{}) catch replacement;
    _ = file;
}

// EXPECT: line=10 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=17 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=26 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=27 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=36 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=37 rule=store-violations-engine severity=error message=resource leak
