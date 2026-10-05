// EXPECT: none
const std = @import("std");

const Entry = struct {
    data: []u8,
};

const Cache = struct {
    entry: *Entry,
};

/// The store writes the duplicated bytes into the block `a.create` named, and
/// the returned struct carries that block out by pointer, so the bytes ride out
/// inside the value the caller receives. Nothing is left unreleased behind: the
/// caller walks the pointer the struct carries, reads the bytes it finds there
/// and releases both blocks. The two `errdefer`s settle the failure path only.
fn returnedCache(a: std.mem.Allocator, input: []const u8) !Cache {
    const bytes = try a.dupe(u8, input);
    errdefer a.free(bytes);
    const entry = try a.create(Entry);
    errdefer a.destroy(entry);
    const cache: Cache = .{ .entry = entry };
    cache.entry.* = .{ .data = bytes };
    return cache;
}

/// The store lands in the same block, but here the escape is the binding the
/// field was filled from: `return entry` hands the caller the very block the
/// bytes were written into, so they ride out with it while `cache` itself dies
/// at the end of the function. Reaching the payload only through the holder
/// would miss that route and call the bytes leaked. The caller reads them off
/// the entry it received and releases both blocks; the `errdefer`s settle the
/// failure path only.
fn returnedEntry(a: std.mem.Allocator, input: []const u8) !*Entry {
    const bytes = try a.dupe(u8, input);
    errdefer a.free(bytes);
    const entry = try a.create(Entry);
    errdefer a.destroy(entry);
    const cache: Cache = .{ .entry = entry };
    cache.entry.* = .{ .data = bytes };
    return entry;
}

test "the returned field pointer hands its bytes to the caller" {
    const a = std.testing.allocator;
    const cache = try returnedCache(a, "kept bytes");
    defer a.destroy(cache.entry);
    defer a.free(cache.entry.data);
    try std.testing.expectEqualStrings("kept bytes", cache.entry.data);
}

test "the original entry binding hands its bytes to the caller" {
    const a = std.testing.allocator;
    const entry = try returnedEntry(a, "kept entry bytes");
    defer a.destroy(entry);
    defer a.free(entry.data);
    try std.testing.expectEqualStrings("kept entry bytes", entry.data);
}
