const std = @import("std");

/// The C callback shape of the working pair, with the transfer done wrong:
/// the block is released before it is handed back.
pub const CFreed = struct {
    gpa: std.mem.Allocator,

    fn stateOf(user: ?*anyopaque) ?*CFreed {
        const ptr = user orelse return null;
        return @ptrCast(@alignCast(ptr));
    }

    /// Reading the block after its release is a use after free, and so is
    /// handing the freed pointer to the caller: the pointer cast carries the
    /// block out, it does not undo the release.
    pub fn alloc(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
        const self = stateOf(user) orelse return null;
        const bytes = self.gpa.alloc(u8, len) catch return null;
        self.gpa.free(bytes);
        std.mem.doNotOptimizeAway(bytes.ptr);
        return @ptrCast(bytes.ptr);
    }
};

/// A second release of a block this frame already released is a genuine
/// double free, and it stays reported however the block leaves the frame.
pub fn releaseTwice(gpa: std.mem.Allocator, len: u32) !void {
    const bytes = try gpa.alloc(u8, len);
    gpa.free(bytes);
    gpa.free(bytes);
}

// EXPECT: line=20 rule=store-violations-engine severity=error message=use after free
// EXPECT: line=21 rule=store-violations-engine severity=error message=use after free
// EXPECT: line=30 rule=store-violations-engine severity=error message=double-free
