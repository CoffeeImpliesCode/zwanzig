// EXPECT: none
const std = @import("std");

const Payload = struct {
    src: []const u8,
};

/// Hands back the pointer it was given, so the block it names is the one a
/// caller's store writes into.
fn payloadAddress(payload: *Payload) *Payload {
    return payload;
}

/// The cast keeps the address of `payload`, so the store writes the bytes into
/// the block `&payload` names and the returned value hands them to the
/// caller, which releases them.
fn castedStore(allocator: std.mem.Allocator, input: []const u8) !Payload {
    var payload: Payload = undefined;
    const owned = try allocator.dupe(u8, input);
    (@as(*Payload, &payload)).* = .{ .src = owned };
    return payload;
}

/// The helper keeps the address too, so this store writes into the same block
/// and the returned value hands the bytes to the caller, which releases them.
fn calledStore(allocator: std.mem.Allocator, input: []const u8) !Payload {
    var payload: Payload = undefined;
    const owned = try allocator.dupe(u8, input);
    payloadAddress(&payload).* = .{ .src = owned };
    return payload;
}
