const std = @import("std");

const Payload = struct {
    src: []const u8,
};

/// The cast in the initializer still names the block `a.create` handed back,
/// so the store below writes a derived scalar into a heap `usize`. A `usize`
/// pointee cannot hold a reference: nothing carries the duplicated bytes out
/// of this frame and nothing releases them. The `errdefer` settles the failure
/// path only, so the success path leaves them reported here.
fn castScalarSlot(a: std.mem.Allocator, input: []const u8) !*usize {
    const bytes = try a.dupe(u8, input);
    errdefer a.free(bytes);
    const slot = @as(*usize, try a.create(usize));
    slot.* = bytes.len;
    return slot;
}

/// The same cast in the initializer with a different pointee. `Payload` holds
/// a reference, so the store writes the bytes into the block `a.create` handed
/// back and the returned pointer carries that block, and the bytes it holds,
/// out to the caller. The `errdefer` still settles the failure path, so
/// nothing is left behind on either side of the return.
fn castContainerSlot(a: std.mem.Allocator, input: []const u8) !*Payload {
    const bytes = try a.dupe(u8, input);
    errdefer a.free(bytes);
    const slot = @as(*Payload, try a.create(Payload));
    slot.* = .{ .src = bytes };
    return slot;
}

test "the cast container slot hands its bytes to the caller" {
    const a = std.testing.allocator;
    const slot = try castContainerSlot(a, "kept bytes");
    defer a.destroy(slot);
    defer a.free(slot.src);
    try std.testing.expectEqualStrings("kept bytes", slot.src);
    _ = &castScalarSlot;
    _ = &groupedScalarSlot;
}

/// The parentheses around `slot` change nothing about which block `(slot).*`
/// writes into: the store writes a derived scalar into the heap `usize`, and
/// a `usize` pointee cannot hold a reference. The returned pointer carries
/// only that integer, so nothing releases the duplicated bytes on the success
/// path. Both `errdefer`s settle the failure path only, so the success path
/// leaves the bytes reported here.
fn groupedScalarSlot(a: std.mem.Allocator, input: []const u8) !*usize {
    const bytes = try a.dupe(u8, input);
    errdefer a.free(bytes);
    const slot = try a.create(usize);
    errdefer a.destroy(slot);
    (slot).* = bytes.len;
    return slot;
}

// EXPECT: line=13 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=50 rule=store-violations-engine severity=error message=resource leak
