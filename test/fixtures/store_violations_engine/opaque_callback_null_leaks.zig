const std = @import("std");

/// The C allocator descriptor the callback is reached through. Neither the
/// descriptor nor the callconv signature decides ownership; the block the
/// callback hands back does.
pub const CAllocator = extern struct {
    alloc: ?*const fn (user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque,
    user: ?*anyopaque,
};

pub const CLeaking = struct {
    gpa: std.mem.Allocator,
    live: usize,

    fn stateOf(user: ?*anyopaque) ?*CLeaking {
        const ptr = user orelse return null;
        return @ptrCast(@alignCast(ptr));
    }

    /// Reports failure after allocating, so the block never reaches the caller
    /// and nothing releases it. Everything else here is the shape of the
    /// working callback pair, so the only difference is the missing transfer.
    pub fn alloc(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
        const self = stateOf(user) orelse return null;
        const bytes = self.gpa.alloc(u8, len) catch return null;
        self.live += bytes.len;
        return null;
    }
};

// EXPECT: line=25 rule=store-violations-engine severity=error message=resource leak
//
// The block is allocated and then dropped: `return null` names no allocation,
// so the callback still owns `bytes` and still has to release it. A nullable
// void pointer return only transfers ownership when it actually carries the
// pointer.
