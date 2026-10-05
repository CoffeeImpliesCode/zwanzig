const std = @import("std");

/// Carries a payload block, so a block made of it can hold a reference.
const Record = struct {
    payload: []u8,
};

/// The block this function returns is a `usize`. The store writes a number,
/// and a number names no owner, so the bytes stay this function's to release
/// - and it never does. The slot carries no annotation of its own, so the
/// type it points at is read off the allocation that made it.
fn inferredScalarDerefStoreLeaks(allocator: std.mem.Allocator) !*usize {
    const bytes = try allocator.alloc(u8, 8);
    const length = try allocator.create(usize);
    length.* = bytes.len;
    return length;
}

/// The same store with the slot's type written down answers the same way:
/// what the store hands over is the pointee's type, not the shape of the
/// value written into it.
fn writtenScalarDerefStoreLeaks(allocator: std.mem.Allocator) !*usize {
    const bytes = try allocator.alloc(u8, 8);
    const length: *usize = try allocator.create(usize);
    length.* = bytes.len;
    return length;
}

/// Releasing the slot releases nothing else, because the bytes were never
/// handed to it. The bytes are the only leak this leaves.
fn inferredScalarSlotReleasedHere(allocator: std.mem.Allocator) !void {
    const bytes = try allocator.alloc(u8, 8);
    const length = try allocator.create(usize);
    length.* = bytes.len;
    allocator.destroy(length);
}

/// The same store with both blocks released is clean.
fn inferredScalarStoreReleased(allocator: std.mem.Allocator) !void {
    const bytes = try allocator.alloc(u8, 8);
    const length = try allocator.create(usize);
    length.* = bytes.len;
    allocator.destroy(length);
    allocator.free(bytes);
}

/// A block made of a container is that container: the bytes the store hands
/// it ride out inside the returned record, so nothing is reported even
/// though the record's type is read off the allocation.
fn inferredContainerRetainsPayload(allocator: std.mem.Allocator) !*Record {
    const bytes = try allocator.alloc(u8, 8);
    const record = try allocator.create(Record);
    record.* = .{ .payload = bytes };
    return record;
}

// EXPECT: line=13 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=23 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=32 rule=store-violations-engine severity=error message=resource leak
