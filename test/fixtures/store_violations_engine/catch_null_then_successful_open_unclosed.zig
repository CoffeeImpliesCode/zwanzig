const std = @import("std");

/// `catch null` turns the binding into an optional: the arm where the open
/// failed holds no handle at all, and the optional is how it says so. The
/// guard below releases the one that did happen and owes nothing on the other.
///
/// What is left unreleased is the independent open that follows. It is an
/// acquisition of its own, and the `catch null` above did not make it and
/// cannot excuse it.
fn nullCatchThenUnclosedOpen(path: []const u8, other: []const u8) void {
    const maybe = std.fs.cwd().openFile(path, .{}) catch null;
    defer if (maybe) |file| file.close();
    const file = std.fs.cwd().openFile(other, .{}) catch return;
    _ = file;
}

/// The same two steps with the second open released as well: the guard on the
/// optional settles the open that happened, and the close below settles the
/// one after it, so neither arm of the `catch null` owes anything.
fn nullCatchThenClosedOpen(path: []const u8, other: []const u8) void {
    const maybe = std.fs.cwd().openFile(path, .{}) catch null;
    defer if (maybe) |file| file.close();
    const file = std.fs.cwd().openFile(other, .{}) catch return;
    defer file.close();
}

// EXPECT: line=13 rule=store-violations-engine severity=error message=resource leak
