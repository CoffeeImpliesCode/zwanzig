const std = @import("std");

const Box = struct {
    payload: []u8,

    /// Keeps the first argument it is given in its result and drops the
    /// second, so the second stays the caller's to release.
    fn wrap(_: *Box, payload: []u8, ignored: []u8) Box {
        _ = ignored;
        return .{ .payload = payload };
    }

    /// Hands back the pointer it was given, so the store a caller writes
    /// through the result lands in that block and no other.
    fn addressOfFirst(_: *Box, target: *Box, _: *Box) *Box {
        return target;
    }

    /// Hands back the receiver itself, so the store a caller writes through
    /// the result lands in the block the call was written on.
    fn selfAddress(self: *Box) *Box {
        return self;
    }
};

/// The block the callee returns rides out inside the returned box, so the
/// bytes stored in it are the caller's to release. The block the callee
/// ignores never leaves this function and nothing disposes of it, so it is
/// still reported.
fn methodKeepsOnlyRetainedParameter(allocator: std.mem.Allocator) !*Box {
    const kept = try allocator.alloc(u8, 8);
    const dropped = try allocator.alloc(u8, 8);
    const box = try allocator.create(Box);
    box.* = box.wrap(kept, dropped);
    return box;
}

/// The method hands back the argument it returns, so the bytes land in `kept`
/// rather than in the block the store is written through. Nothing returns
/// `kept` and nothing disposes of it, so the block and the bytes stored in it
/// are both still reported. `dropped` leaves the function as the returned
/// pointer and is the caller's to release.
fn methodDestinationMustNotEscapeDroppedBytes(allocator: std.mem.Allocator) !*Box {
    const kept = try allocator.create(Box);
    const dropped = try allocator.create(Box);
    kept.* = .{ .payload = &.{} };
    dropped.* = .{ .payload = &.{} };
    const bytes = try allocator.alloc(u8, 8);
    kept.addressOfFirst(kept, dropped).* = .{ .payload = bytes };
    return dropped;
}

/// A method that hands back its receiver writes into the block the call was
/// written on, not into some argument beside it. Nothing returns `kept` and
/// nothing disposes of it, so the block and the bytes the store put in it are
/// both still reported, while `returned` leaves as the returned pointer.
fn receiverMustNotEscapeStoredBytes(allocator: std.mem.Allocator) !*Box {
    const kept = try allocator.create(Box);
    const returned = try allocator.create(Box);
    kept.* = .{ .payload = &.{} };
    returned.* = .{ .payload = &.{} };
    const bytes = try allocator.alloc(u8, 8);
    kept.selfAddress().* = .{ .payload = bytes };
    return returned;
}

/// The same receiver, but the block it names is the one this function
/// returns, so the bytes ride out inside it and nothing is reported.
fn receiverReturnedWithBlock(allocator: std.mem.Allocator) !*Box {
    const box = try allocator.create(Box);
    const bytes = try allocator.alloc(u8, 8);
    box.selfAddress().* = .{ .payload = bytes };
    return box;
}

/// The same method writing into the block this function returns: the bytes
/// ride out with it, and the block the store is written through is released
/// here, so nothing is reported.
fn methodDestinationReturnedWithBlock(allocator: std.mem.Allocator) !*Box {
    const target = try allocator.create(Box);
    const other = try allocator.create(Box);
    target.* = .{ .payload = &.{} };
    other.* = .{ .payload = &.{} };
    const bytes = try allocator.alloc(u8, 8);
    defer allocator.destroy(other);
    other.addressOfFirst(target, other).* = .{ .payload = bytes };
    return target;
}

/// A block made of a container is that container: the bytes the store hands
/// it ride out inside the returned block, even though the pointee's own type
/// is read off the allocation rather than written down.
fn inferredContainerPointeeRetainsPayload(allocator: std.mem.Allocator) !*Box {
    const bytes = try allocator.alloc(u8, 8);
    const box = try allocator.create(Box);
    box.* = .{ .payload = bytes };
    return box;
}

// EXPECT: line=32 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=44 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=48 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=58 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=62 rule=store-violations-engine severity=error message=resource leak

/// The same box as `Box`, written with an inferred receiver and an inferred
/// ignored sibling. Zig records an `anytype` parameter as a bare token
/// rather than as a type expression, so neither slot here carries a readable
/// declared type and only the payload slot between them does.
const AnypeBox = struct {
    payload: []u8,

    /// Keeps the payload it is given in its result and drops the ignored one,
    /// so the ignored block stays the caller's to release. The receiver and
    /// the ignored slot are both written `anytype`: neither carries a
    /// readable declared type, and only the payload slot between them does,
    /// so the payload is the second written argument and not the first.
    pub fn adopt(self: anytype, payload: []u8, ignored: anytype) AnypeBox {
        _ = self;
        _ = ignored;
        return .{ .payload = payload };
    }

    /// Hands back the block named by the argument written after the receiver,
    /// so a store written through the result lands in that block and no
    /// other. The receiver and the ignored slot are written `anytype` here
    /// too, so the block that comes back is the second written argument.
    pub fn addressOfArgument(self: anytype, target: *AnypeBox, ignored: anytype) *AnypeBox {
        _ = self;
        _ = ignored;
        return target;
    }
};

/// The payload this function allocates rides out inside the returned block:
/// `adopt` hands the argument written in the middle slot back in its result,
/// and the returned block is the one that result is stored into. The ignored
/// block is dropped by the callee and released here, so it is not reported.
fn anytypeRetainedParameterRidesOut(allocator: std.mem.Allocator) !*AnypeBox {
    const payload = try allocator.alloc(u8, 8);
    const ignored = try allocator.alloc(u8, 8);
    const box = try allocator.create(AnypeBox);
    defer allocator.free(ignored);
    box.* = box.adopt(payload, ignored);
    return box;
}

/// The same method with the ignored sibling left to the caller: the payload
/// still rides out inside the returned block, and the ignored block is
/// neither returned nor released here, so it is still reported.
fn anytypeIgnoredSiblingStillLeaks(allocator: std.mem.Allocator) !*AnypeBox {
    const payload = try allocator.alloc(u8, 8);
    const leaked = try allocator.alloc(u8, 8);
    const box = try allocator.create(AnypeBox);
    box.* = box.adopt(payload, leaked);
    return box;
}

/// The method hands back the block named by its second written argument, so
/// the bytes land in `target` rather than in the block the call is written
/// on. `target` is what this function returns, so the bytes ride out with
/// it, and the block the store is written through is released here.
fn anytypeDestinationArgumentRetainsBytes(allocator: std.mem.Allocator) !*AnypeBox {
    const receiver = try allocator.create(AnypeBox);
    const target = try allocator.create(AnypeBox);
    receiver.* = .{ .payload = &.{} };
    target.* = .{ .payload = &.{} };
    const bytes = try allocator.alloc(u8, 8);
    defer allocator.destroy(receiver);
    receiver.addressOfArgument(target, receiver).* = .{ .payload = bytes };
    return target;
}

/// The same method reached through the type name rather than through a
/// value: the call writes the receiver as its own first argument, so the
/// payload is the second argument and the ignored sibling the third.
fn anytypeNamespaceCallControl(allocator: std.mem.Allocator) !*AnypeBox {
    const payload = try allocator.alloc(u8, 8);
    const ignored = try allocator.alloc(u8, 8);
    const box = try allocator.create(AnypeBox);
    defer allocator.free(ignored);
    box.* = AnypeBox.adopt(box, payload, ignored);
    return box;
}

// EXPECT: line=153 rule=store-violations-engine severity=error message=resource leak

// Instance and namespace calls must return the retained block, not its sibling.
test "adopt hands back the payload slot for an instance call and a namespace call" {
    const a = std.testing.allocator;

    const kept_by_instance = try a.dupe(u8, "keep-1");
    defer a.free(kept_by_instance);
    const dropped_by_instance = try a.dupe(u8, "drop-1");
    defer a.free(dropped_by_instance);
    const instance_box = try a.create(AnypeBox);
    defer a.destroy(instance_box);
    instance_box.* = instance_box.adopt(kept_by_instance, dropped_by_instance);
    try std.testing.expectEqualStrings("keep-1", instance_box.payload);
    try std.testing.expectEqual(kept_by_instance.ptr, instance_box.payload.ptr);

    const kept_by_namespace = try a.dupe(u8, "keep-2");
    defer a.free(kept_by_namespace);
    const dropped_by_namespace = try a.dupe(u8, "drop-2");
    defer a.free(dropped_by_namespace);
    const namespace_box = try a.create(AnypeBox);
    defer a.destroy(namespace_box);
    namespace_box.* = AnypeBox.adopt(namespace_box, kept_by_namespace, dropped_by_namespace);
    try std.testing.expectEqualStrings("keep-2", namespace_box.payload);
    try std.testing.expectEqual(kept_by_namespace.ptr, namespace_box.payload.ptr);
}

// Execute every safe generic body, then release its returned bytes and box.
test "the safe anytype bodies return owned regions the caller releases once" {
    const a = std.testing.allocator;

    const rides_out: *const fn (std.mem.Allocator) anyerror!*AnypeBox = anytypeRetainedParameterRidesOut;
    const destination_retains: *const fn (std.mem.Allocator) anyerror!*AnypeBox = anytypeDestinationArgumentRetainsBytes;
    const namespace_control: *const fn (std.mem.Allocator) anyerror!*AnypeBox = anytypeNamespaceCallControl;

    const cases = [_]struct {
        name: []const u8,
        build: *const fn (std.mem.Allocator) anyerror!*AnypeBox,
        fill: u8,
    }{
        .{ .name = "anytypeRetainedParameterRidesOut", .build = rides_out, .fill = 0x11 },
        .{ .name = "anytypeDestinationArgumentRetainsBytes", .build = destination_retains, .fill = 0x22 },
        .{ .name = "anytypeNamespaceCallControl", .build = namespace_control, .fill = 0x33 },
    };

    for (cases) |case| {
        const box = try case.build(a);
        // The block that comes back is written here before any of it is read.
        @memset(box.payload, case.fill);
        std.testing.expectEqualSlices(u8, &[_]u8{case.fill} ** 8, box.payload) catch |err| {
            std.debug.print("{s} did not return the eight bytes it owns\n", .{case.name});
            return err;
        };
        a.free(box.payload);
        a.destroy(box);
    }
}
