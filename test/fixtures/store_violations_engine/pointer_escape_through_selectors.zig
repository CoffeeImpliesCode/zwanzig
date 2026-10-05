//! The escape walk stops at the expressions that select a value, and what
//! each selection does to the block behind it.
//!
//! One allocator descriptor, one `Counted` pair, and a family of allocating
//! callbacks that differ only in the shape of the expression they return.
//! Every callback allocates through the allocator inside `State`, bumps the
//! `live` counter, and either hands the block to its caller or drops it.
//!
//! Rows whose driver releases the block are leak-free at runtime and quiet in
//! the analyzer. The rows that drop it are analyzer controls: the test below
//! runs the released rows only, so what pins a dropped block is the reported
//! diagnostics and not a leak some driver is built to observe.

const std = @import("std");

/// The C allocator descriptor the allocating callbacks are reached through.
/// Neither the descriptor nor the `callconv` signature decides ownership; the
/// returned block does.
pub const CAllocator = extern struct {
    alloc: ?*const fn (user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque,
    dealloc: ?*const fn (user: ?*anyopaque, ptr: ?*anyopaque, len: u32) callconv(.c) void,
    user: ?*anyopaque,
};

/// The `alloc` slot's own spelling, so a row's callback can be handed to
/// `descFor` without a second, differently-typed function-pointer declaration.
pub const AllocFn = *const fn (user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque;

/// Length the released rows allocate at. Strictly less than `transfer_limit`,
/// so S2 is driven through its `else` arm.
const safe_len: u32 = 32;

/// The threshold U1 and U2 branch on. Rows that transfer only below it, and
/// drop at or above it.
const transfer_limit: u32 = 48;

const Counted = struct {
    state: State,

    const State = struct {
        gpa: std.mem.Allocator,
        live: usize,

        fn stateOf(user: ?*anyopaque) ?*State {
            const ptr = user orelse return null;
            return @ptrCast(@alignCast(ptr));
        }

        /// S1: the control. A bare pointer-preserving cast. The block leaves
        /// the callback, so the callback no longer owns it. Every other row
        /// in this file is measured against this one.
        fn alloc(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
            const self = stateOf(user) orelse return null;
            const bytes = self.gpa.alloc(u8, len) catch return null;
            self.live += bytes.len;
            return @ptrCast(bytes.ptr);
        }

        /// S2: an `if` whose two arms are the same pointer-preserving cast.
        /// The condition is a real one, but neither arm drops the block, so
        /// neither arm can leak it. The redundancy is deliberate and is the
        /// whole point of the row: it isolates "a selector is present" from
        /// "an arm drops the block", which is what makes U1 and U2 mean
        /// something.
        fn allocIfBothArms(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
            const self = stateOf(user) orelse return null;
            const bytes = self.gpa.alloc(u8, len) catch return null;
            self.live += bytes.len;
            return if (len >= transfer_limit) @ptrCast(bytes.ptr) else @ptrCast(bytes.ptr);
        }

        /// S3: a known-nonnull pointer-preserving cast lifted into an optional
        /// and unwrapped again. The cast of a real `bytes.ptr` can never be
        /// null, so the `orelse` fallback is unreachable at runtime and this
        /// row is expected clean rather than expected to warn. The escape is
        /// still one hop away, and that hop is the point.
        fn allocOrelseNonnul(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
            const self = stateOf(user) orelse return null;
            const bytes = self.gpa.alloc(u8, len) catch return null;
            self.live += bytes.len;
            return @as(?*anyopaque, @ptrCast(bytes.ptr)) orelse return null;
        }

        /// U1: the same `if` with a `null` in the `then` arm. A length at or
        /// above `transfer_limit` takes that arm, so a real block is allocated
        /// and then dropped: there is no pointer left to release, and the
        /// callback that allocated it is gone.
        fn allocIfDropsArm(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
            const self = stateOf(user) orelse return null;
            const bytes = self.gpa.alloc(u8, len) catch return null;
            self.live += bytes.len;
            return if (len >= transfer_limit) null else @ptrCast(bytes.ptr);
        }

        /// U2: the same shape through a `switch`. One prong returns the
        /// pointer, the other returns `null`, and the `null` prong is the one
        /// a length at or above `transfer_limit` takes.
        fn allocSwitchDropsProng(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
            const self = stateOf(user) orelse return null;
            const bytes = self.gpa.alloc(u8, len) catch return null;
            self.live += bytes.len;
            return switch (len) {
                transfer_limit...std.math.maxInt(u32) => null,
                else => @ptrCast(bytes.ptr),
            };
        }

        /// U3: the scalar boundary. The return type is an unsigned integer,
        /// and the body converts the block pointer to that integer. The
        /// integer does not convey ownership, so the caller has no way to
        /// release the block. This row is not a selector at all, which is why
        /// it is the one that has to survive any widening of the escape walk:
        /// it is stopped before the walk starts, by the declared return type.
        fn allocAddr(user: ?*anyopaque, len: u32) callconv(.c) usize {
            const self = stateOf(user) orelse return 0;
            const bytes = self.gpa.alloc(u8, len) catch return 0;
            self.live += bytes.len;
            return @intFromPtr(bytes.ptr);
        }

        /// A1: the two-statement local-alias form. The block is bound to a
        /// local optional first, and the selector then unwraps that local.
        /// Unlike S3 the cast is not an operand of the returned expression; it
        /// is the local's initializer, so the escape has to cross a pointer
        /// copy rather than an expression edge.
        fn allocLocalAlias(user: ?*anyopaque, len: u32) callconv(.c) ?*anyopaque {
            const self = stateOf(user) orelse return null;
            const bytes = self.gpa.alloc(u8, len) catch return null;
            self.live += bytes.len;
            const block: ?*anyopaque = @as(?*anyopaque, @ptrCast(bytes.ptr));
            return block orelse return null;
        }

        fn dealloc(user: ?*anyopaque, ptr: ?*anyopaque, len: u32) callconv(.c) void {
            const self = stateOf(user) orelse return;
            const block = ptr orelse return;
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

    /// The same descriptor with a different callback in the `alloc` slot. Each
    /// row in this file is a different allocating implementation behind one
    /// identical C ABI, which is the whole point of the family.
    fn descFor(self: *Counted, alloc: AllocFn) CAllocator {
        return .{
            .alloc = alloc,
            .dealloc = State.dealloc,
            .user = &self.state,
        };
    }
};

/// Reconstruct the block the caller was handed, write a value into every byte
/// and read them all back. The non-null check is here, at the function that
/// dereferences, so no call site can reach the slice through a null handle.
fn writeThrough(block: ?*anyopaque, len: u32) !void {
    const handle = block orelse return error.NullBlock;
    const view: []u8 = @as([*]u8, @ptrCast(handle))[0..len];
    for (view, 0..) |*byte, i| {
        byte.* = @truncate(i);
    }
    var sum: u32 = 0;
    for (view) |byte| {
        sum += byte;
    }
    std.mem.doNotOptimizeAway(sum);
}

fn exerciseS1(counted: *Counted) !void {
    const desc = counted.desc();
    const block = desc.alloc.?(desc.user, safe_len) orelse return error.S1NoBlock;
    try writeThrough(block, safe_len);
    desc.dealloc.?(desc.user, block, safe_len);
}

fn exerciseS2(counted: *Counted) !void {
    const desc = counted.descFor(Counted.State.allocIfBothArms);
    const block = desc.alloc.?(desc.user, safe_len) orelse return error.S2NoBlock;
    try writeThrough(block, safe_len);
    desc.dealloc.?(desc.user, block, safe_len);
}

fn exerciseS3(counted: *Counted) !void {
    const desc = counted.descFor(Counted.State.allocOrelseNonnul);
    const block = desc.alloc.?(desc.user, safe_len) orelse return error.S3NoBlock;
    try writeThrough(block, safe_len);
    desc.dealloc.?(desc.user, block, safe_len);
}

fn exerciseA1(counted: *Counted) !void {
    const desc = counted.descFor(Counted.State.allocLocalAlias);
    const block = desc.alloc.?(desc.user, safe_len) orelse return error.A1NoBlock;
    try writeThrough(block, safe_len);
    desc.dealloc.?(desc.user, block, safe_len);
}

test "the rows that hand the block to their caller release it" {
    var heap: std.heap.DebugAllocator(.{}) = .init;
    var counted: Counted = Counted.init(heap.allocator());

    try exerciseS1(&counted);
    try exerciseS2(&counted);
    try exerciseS3(&counted);
    try exerciseA1(&counted);

    // The live count is the first gate: it proves every block the driver was
    // handed came back. The allocator's own `deinit` is the second, so a row
    // that dropped its block on the way here fails rather than passes quietly.
    try std.testing.expectEqual(@as(usize, 0), counted.state.live);
    try std.testing.expectEqual(std.heap.Check.ok, heap.deinit());
}

// EXPECT: line=90 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=100 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=116 rule=store-violations-engine severity=error message=resource leak
//
// U1 and U2 drop the block on an arm a length at or above `transfer_limit`
// takes, and U3 launders it into an integer the caller cannot release, so all
// three must stay reported after any widening of the escape walk.
//
// S2 and S3 really do hand the block to the caller through the expression
// that selects it, and A1 hands it over through a local the same cast filled:
// neither is reported. A selection only transfers the block when every arm
// carries it, which is what keeps U1 and U2 reported while S2 is quiet.
