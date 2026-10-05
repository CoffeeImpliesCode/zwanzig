// EXPECT: none
const std = @import("std");

pub const ParseError = error{ OutOfMemory, EmptySource };

pub const Payload = struct {
    src: []const u8,
};

pub const Owner = struct {
    arena: std.heap.ArenaAllocator,
    payload: *Payload,
    bytes: []const u8,

    pub fn deinit(self: *Owner) void {
        self.arena.deinit();
        self.* = undefined;
    }
};

/// Builds its result out of the argument it was handed, so the caller's block
/// rides out inside the returned value and nothing new is allocated here.
fn parseInto(src: []const u8) ParseError!Payload {
    if (src.len == 0) return error.EmptySource;
    return .{ .src = src };
}

/// The store writes the parsed payload into the block `a` allocated, so the
/// duplicated bytes belong to that block from then on and leave with the
/// pointer this function returns. The arena behind `a` stays the disposer.
fn createPayload(a: std.mem.Allocator, bytes: []const u8) ParseError!*Payload {
    const owned = try a.dupe(u8, bytes);
    const p = try a.create(Payload);
    p.* = try parseInto(owned);
    return p;
}

/// `errdefer` holds the arena until the owner that carries it is built; from
/// then on the owner is the one that disposes it.
pub fn init(gpa: std.mem.Allocator) ParseError!Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const a = arena.allocator();
    const payload = try createPayload(a, "abc");
    return .{
        .arena = arena,
        .payload = payload,
        .bytes = payload.src,
    };
}

/// The existing-owner path allocates through the arena the caller already
/// holds, so the same bytes are released by `Owner.deinit` and not here.
pub fn loadFromBytes(self: *Owner, gpa: std.mem.Allocator, bytes: []const u8) ParseError!*Payload {
    const buffer = try gpa.dupe(u8, bytes);
    defer gpa.free(buffer);
    const face = try createPayload(self.arena.allocator(), buffer);
    self.bytes = face.src;
    return face;
}
