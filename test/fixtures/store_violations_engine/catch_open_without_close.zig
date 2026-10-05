const std = @import("std");

/// Issue #85, the other side of the pair: the failure arm still returns
/// before the binding exists, so the successful open is the only acquisition
/// this function takes - and nothing releases it. The `catch` is not what
/// makes the leak, and a close written for the success arm cannot be
/// conjured out of one.
fn leaksTheSuccessfulOpen(path: []const u8) !void {
    const file = std.fs.cwd().openFile(path, .{}) catch |err| return err;
    _ = file;
}

/// Mapping the error to a value of its own owns no handle either: the mapped
/// error is not an open. The obligation stays the single successful open.
fn fallbackIsNotAnOpen(path: []const u8) !void {
    const file = std.fs.cwd().openFile(path, .{}) catch return error.CannotOpen;
    _ = file;
}

/// A failure arm that opens the replacement really does acquire on that
/// path, so dropping the primary's acquisition there must not quietly drop
/// the fallback's either: the handler's handle is held and unreleased.
fn fallbackAcquiresAndLeaks(path: []const u8, other: []const u8) void {
    const file = std.fs.cwd().openFile(path, .{}) catch std.fs.cwd().openFile(other, .{}) catch return;
    _ = file;
}

/// The same failure arm with its close in place settles both handles: the
/// fallback's on the failure arm, the primary's on the success arm.
fn fallbackAcquiresAndCloses(path: []const u8, other: []const u8) void {
    const file = std.fs.cwd().openFile(path, .{}) catch std.fs.cwd().openFile(other, .{}) catch return;
    defer file.close();
}

/// A handler that hands back a handle it computed keeps the obligation too:
/// the binding holds that handle on the failure arm, and nothing releases it.
/// A labelled block leaves through its own exit, so this arm reaches the
/// binding rather than returning past it.
fn blockFallbackAcquiresAndLeaks(path: []const u8, other: []const u8) void {
    const file = std.fs.cwd().openFile(path, .{}) catch openReplacement: {
        const replacement = std.fs.cwd().openFile(other, .{}) catch return;
        break :openReplacement replacement;
    };
    _ = file;
}

/// Parentheses around a failure arm are not a different arm:
/// `catch (return)` exits the function the way a bare `catch return` does,
/// so the successful open is the only acquisition here and the deferred
/// close settles it.
fn groupedReturnCloses(path: []const u8) void {
    const file = std.fs.cwd().openFile(path, .{}) catch (return);
    defer file.close();
}

/// The same arm without its close leaks what the bare `catch return` above
/// leaks: the parens buy the obligation nothing.
fn groupedReturnLeaks(path: []const u8) void {
    const file = std.fs.cwd().openFile(path, .{}) catch (return);
    _ = file;
}

/// `catch (null)` binds the same optional `catch null` does, so the deferred
/// guard releases the open that happened and owes nothing on the arm where
/// it did not.
fn groupedNullCloses(path: []const u8) void {
    const maybe = std.fs.cwd().openFile(path, .{}) catch (null);
    defer if (maybe) |file| file.close();
}

/// Nothing releases the open here. The optional the parens bind is not a
/// release: the handle the success arm produced is still held.
fn groupedNullLeaks(path: []const u8) void {
    const maybe = std.fs.cwd().openFile(path, .{}) catch (null);
    _ = maybe;
}

// EXPECT: line=9 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=16 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=24 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=40 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=41 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=59 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=74 rule=store-violations-engine severity=error message=resource leak
