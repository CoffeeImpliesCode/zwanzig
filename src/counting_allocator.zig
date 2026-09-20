const std = @import("std");

/// Counts requested live payload bytes, not allocator metadata or backing slack.
/// Keep this object at a stable address until all forwarded allocations are freed.
pub const CountingAllocator = struct {
    backing: std.mem.Allocator,
    live_bytes: usize = 0,

    pub fn init(backing: std.mem.Allocator) CountingAllocator {
        return .{ .backing = backing };
    }

    pub fn allocator(self: *CountingAllocator) std.mem.Allocator {
        return .{
            .ptr = self,
            .vtable = &.{
                .alloc = alloc,
                .resize = resize,
                .remap = remap,
                .free = free,
            },
        };
    }

    fn alloc(
        context: *anyopaque,
        length: usize,
        alignment: std.mem.Alignment,
        return_address: usize,
    ) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(context));
        const result = self.backing.rawAlloc(length, alignment, return_address) orelse return null;
        self.live_bytes += length;
        return result;
    }

    fn resize(
        context: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_length: usize,
        return_address: usize,
    ) bool {
        const self: *CountingAllocator = @ptrCast(@alignCast(context));
        if (!self.backing.rawResize(memory, alignment, new_length, return_address)) return false;
        self.live_bytes -= memory.len;
        self.live_bytes += new_length;
        return true;
    }

    fn remap(
        context: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        new_length: usize,
        return_address: usize,
    ) ?[*]u8 {
        const self: *CountingAllocator = @ptrCast(@alignCast(context));
        const result = self.backing.rawRemap(memory, alignment, new_length, return_address) orelse
            return null;
        self.live_bytes -= memory.len;
        self.live_bytes += new_length;
        return result;
    }

    fn free(
        context: *anyopaque,
        memory: []u8,
        alignment: std.mem.Alignment,
        return_address: usize,
    ) void {
        const self: *CountingAllocator = @ptrCast(@alignCast(context));
        self.backing.rawFree(memory, alignment, return_address);
        self.live_bytes -= memory.len;
    }
};

test "CountingAllocator tracks successful resize and remap payloads" {
    var storage: [256]u8 align(16) = undefined;
    var fixed = std.heap.FixedBufferAllocator.init(&storage);
    var counting = CountingAllocator.init(fixed.allocator());
    const allocator = counting.allocator();

    var bytes = try allocator.alignedAlloc(u8, .@"16", 32);
    defer allocator.free(bytes);
    try std.testing.expectEqual(@as(usize, 32), counting.live_bytes);
    try std.testing.expect(allocator.resize(bytes, 64));
    bytes = bytes.ptr[0..64];
    try std.testing.expectEqual(@as(usize, 64), counting.live_bytes);
    bytes = allocator.remap(bytes, 96) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, 96), counting.live_bytes);
    try std.testing.expect(allocator.resize(bytes, 48));
    bytes = bytes.ptr[0..48];
    bytes = allocator.remap(bytes, 16) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(usize, 16), counting.live_bytes);
    try std.testing.expect(!allocator.resize(bytes, 1024));
    try std.testing.expect(allocator.remap(bytes, 1024) == null);
    try std.testing.expectError(error.OutOfMemory, allocator.alloc(u8, 1024));
    try std.testing.expectEqual(@as(usize, 16), counting.live_bytes);
    allocator.free(bytes);
    bytes = bytes[0..0];
    try std.testing.expectEqual(@as(usize, 0), counting.live_bytes);
}

test "CountingAllocator preserves counts when realloc moves or fails" {
    var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{
        .resize_fail_index = 0,
    });
    var counting = CountingAllocator.init(failing.allocator());
    const allocator = counting.allocator();
    var bytes = try allocator.alloc(u8, 16);
    defer allocator.free(bytes);
    @memset(bytes, 0x5a);
    const old_pointer = bytes.ptr;
    bytes = try allocator.realloc(bytes, 64);
    try std.testing.expect(bytes.ptr != old_pointer);
    try std.testing.expectEqualSlices(u8, &([_]u8{0x5a} ** 16), bytes[0..16]);
    try std.testing.expectEqual(@as(usize, 64), counting.live_bytes);
    failing.fail_index = failing.alloc_index;
    try std.testing.expectError(error.OutOfMemory, allocator.realloc(bytes, 128));
    try std.testing.expectEqual(@as(usize, 64), counting.live_bytes);
    allocator.free(bytes);
    bytes = bytes[0..0];
    try std.testing.expectEqual(@as(usize, 0), counting.live_bytes);
}
