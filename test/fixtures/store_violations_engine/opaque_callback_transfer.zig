const std = @import("std");

pub const CAllocator = extern struct {
    alloc: ?*const fn (user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque,
    dealloc: ?*const fn (user: ?*anyopaque, ptr: ?*anyopaque, len: u32) callconv(.c) void,
    user: ?*anyopaque,
};

const Counted = struct {
    state: State,

    const State = struct {
        gpa: std.mem.Allocator,
        live: usize,

        fn stateOf(user: ?*anyopaque) ?*State {
            const ptr = user orelse {
                std.debug.print("c abi test allocator: NULL user pointer\n", .{});
                return null;
            };
            return @ptrCast(@alignCast(ptr));
        }

        fn alloc(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
            const self = stateOf(user) orelse return null;
            const bytes = self.gpa.alloc(u8, len) catch return null;
            self.live += bytes.len;
            return @ptrCast(bytes.ptr);
        }

        fn dealloc(user: ?*anyopaque, ptr: ?*anyopaque, len: u32) callconv(.c) void {
            const self = stateOf(user) orelse return;
            const block = ptr orelse {
                std.debug.print("c abi test allocator: NULL pointer to free\n", .{});
                return;
            };
            self.gpa.free(@as([*]u8, @ptrCast(block))[0..len]);
            self.live -= len;
        }
    };

    fn init(gpa: std.mem.Allocator) Counted {
        return .{ .state = .{ .gpa = gpa, .live = 0 } };
    }

    fn desc(self: *Counted) CAllocator {
        return .{
            .alloc = State.alloc,
            .dealloc = State.dealloc,
            .user = &self.state,
        };
    }
};

pub fn main() !void {
    var heap: std.heap.DebugAllocator(.{}) = .init;
    defer if (heap.deinit() != .ok) @panic("callback ownership leaked");
    var counted: Counted = Counted.init(heap.allocator());
    const desc = counted.desc();
    const block = desc.alloc.?(desc.user, 32) orelse return error.AllocationFailed;
    desc.dealloc.?(desc.user, block, 32);
    if (counted.state.live != 0) return error.LeakedBytes;
    std.debug.print("callback live bytes: {d}; cleanup checked\n", .{counted.state.live});
}

// EXPECT: none
//
// The allocating callback hands the block to the caller as `@ptrCast(bytes.ptr)`
// through a nullable opaque pointer, and the matching deallocation callback
// releases the very same block. The block leaves the callback, so the callback
// no longer owns it and reports nothing. Nothing about the C descriptor, the
// callconv signature or the name of the callback is what proves this: the
// allocation's ordinary origin survives `.ptr` and the pointer-preserving cast,
// and the transfer is what the caller's release depends on.
