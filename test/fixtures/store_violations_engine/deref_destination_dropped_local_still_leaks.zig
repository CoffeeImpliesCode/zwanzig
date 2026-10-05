const std = @import("std");

const Payload = struct {
    src: []const u8,
};

/// Hands back the pointer it was given, so the block it names is the one a
/// caller's store writes into.
fn lengthSlot(length: *usize) *usize {
    return length;
}

/// The cast reaches a local block that leaves with this function. A store is
/// not a release, so the bytes it handed over are still reported: nothing
/// returns the block and nothing disposes of it.
fn droppedCastedStore(allocator: std.mem.Allocator, input: []const u8) !void {
    var payload: Payload = undefined;
    const owned = try allocator.dupe(u8, input);
    (@as(*Payload, &payload)).* = .{ .src = owned };
}

/// The helper names the `usize` block the caller already holds, and a `usize`
/// pointee cannot hold a reference: the store below writes a number and hands
/// nothing over. The bytes stay this function's to release, and it never
/// does.
fn droppedScalarStore(allocator: std.mem.Allocator, input: []const u8, length: *usize) !void {
    const owned = try allocator.dupe(u8, input);
    lengthSlot(length).* = owned.len;
}

// EXPECT: line=18 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=27 rule=store-violations-engine severity=error message=resource leak
