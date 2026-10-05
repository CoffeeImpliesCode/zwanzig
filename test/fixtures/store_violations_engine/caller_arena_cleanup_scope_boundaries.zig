const std = @import("std");

/// The context carries the allocator the block below is charged to, and a name
/// that is a field of the context's own rather than of the arena.
const Context = struct {
    pool: std.mem.Allocator,
    name: []const u8,
};

/// A disposal registered below the call does not come too late. Registration
/// order inside one scope decides nothing about when that scope ends: control
/// below runs to the end of the scope, the `defer` written under it runs there
/// too, and the arena it disposes is the arena this block was charged to.
fn formatAfterLateRegistration(context: *const Context) void {
    const label = std.fmt.allocPrint(context.pool, "entry={d}", .{9}) catch @panic("oom");
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runAfterLateRegistration(gpa: std.mem.Allocator) void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    formatAfterLateRegistration(&context);
    defer arena.deinit();
}

/// The `defer` is written as a block, which is the same registration spelled
/// another way. It belongs to the frame that declares the arena, so it settles
/// the error path and the way out that reaches the end of the frame alike.
fn formatUnderBlockDefer(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runUnderBlockDefer(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer {
        arena.deinit();
    }
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatUnderBlockDefer(&context);
}

/// The disposal is registered inside a block of its own and that block runs to
/// its end before the frame carries on. By the time the frame reaches the way
/// out, the arena behind this block has already been disposed, so nothing this
/// block made outlives it.
fn formatUnderCompletedInnerDefer(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runUnderCompletedInnerDefer(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    {
        defer arena.deinit();
        try formatUnderCompletedInnerDefer(&context);
    }
    return;
}

test "every defer scope boundary still disposes the arena its scope allocated through" {
    // All three frames below dispose the arena the block above them was charged
    // to, so none of the three leaves what that block made unowned: where the
    // `defer` sits inside the scope, and how it is spelled, settles nothing
    // about whether it runs.
    runAfterLateRegistration(std.testing.allocator);
    try runUnderBlockDefer(std.testing.allocator);
    try runUnderCompletedInnerDefer(std.testing.allocator);
}

/// One block of its own, charged to the arena its caller declares and read by
/// two callers that differ only in what they do once control comes back. What
/// this block hands back is nothing on either path, so what it makes stays the
/// caller's to settle.
fn formatInsideErrorTail(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{7});
    std.debug.assert(std.mem.eql(u8, label, "entry=7"));
}

/// The final `if` returns from both of its arms, so this frame cannot reach the
/// end of its body: there is no falling-off-the-end exit to settle here. Every
/// way out of the frame hands back an error, and the `errdefer` beside the
/// arena settles the error path, so no way out of this frame escapes it and
/// nothing the block above allocated outlives the frame.
fn runErrorOnlyTail(gpa: std.mem.Allocator, flag: bool) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatInsideErrorTail(&context);
    if (flag) {
        return error.NoOwner;
    } else {
        return error.NoOwner;
    }
}

/// The `errdefer` beside the arena settles the error path and nothing else. The
/// arm that returns without an owner disposes nothing and hands nothing back,
/// so what the block above allocated stays charged to a frame that is gone by
/// the time anything could release it.
fn runUnownedSuccessTail(gpa: std.mem.Allocator, keep: bool) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatInsideUnownedTail(&context);
    if (keep) return;
    return error.NoOwner;
}

test "a frame whose every way out hands back an error the errdefer beside it settles" {
    // Both flag values leave the frame through the same final `if`, and each of
    // its arms hands back an error, so the arena the call above was charged to
    // is disposed on the way out of both.
    try std.testing.expectError(error.NoOwner, runErrorOnlyTail(std.testing.allocator, true));
    try std.testing.expectError(error.NoOwner, runErrorOnlyTail(std.testing.allocator, false));
}

/// The owner the alias carrier hands back. The arena rides under the same field
/// name the other owners in this file use, so a write to that field is the same
/// substitution in each of them.
const AliasCarrier = struct { arena: std.heap.ArenaAllocator };

/// The label is charged to the arena the caller declares and is read here and
/// then forgotten, so nothing this block makes is what disposes it. What the
/// block hands back is nothing, and the arena holding what it made stays the
/// caller's to settle.
fn formatInsideAliasCarrier(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{6});
    std.debug.assert(std.mem.eql(u8, label, "entry=6"));
}

/// A copy of an arena is that arena by value, so the owner below is built out of
/// an arena that is this one, and the write after it replaces the field that
/// copy sat in. What comes back holds an arena that never allocated anything,
/// while the arena the block above was charged to is gone with the frame - and
/// what the caller disposes is the arena handed back in its place.
pub fn makeAliasedCarrier(gpa: std.mem.Allocator) !AliasCarrier {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatInsideAliasCarrier(&context);
    const held = arena;
    var owner: AliasCarrier = .{ .arena = held };
    owner.arena = std.heap.ArenaAllocator.init(gpa);
    return owner;
}

/// One block of its own, charged to the arena the caller declares and read by
/// the frame that calls it. The caller is what disposes it: nothing here hands
/// an owner back, so whether what this block made is released is decided above.
fn formatInsideUnownedTail(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{5});
    std.debug.assert(std.mem.eql(u8, label, "entry=5"));
}

/// Charged to the arena the caller declares, like every other block in this
/// file, and forgotten the moment the call returns. What it hands back is
/// nothing, so the frame that called it is left holding the only reference to
/// what it made.
fn formatInsideLabeledTail(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{4});
    std.debug.assert(std.mem.eql(u8, label, "entry=4"));
}

/// The last statement of this frame is a labeled block with two ways out
/// of it: the `break` completes the block, so control then runs off the
/// end of the body. The `errdefer` settles only the arm that hands back an
/// error, and the fall off the end disposes nothing and hands nothing back.
/// What the block above allocated leaves with a frame that is gone.
fn runLabeledTail(gpa: std.mem.Allocator, skip: bool) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatInsideLabeledTail(&context);
    exit: {
        if (skip) break :exit;
        return error.NoOwner;
    }
}

// EXPECT: line=129 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=153 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=162 rule=store-violations-engine severity=error message=resource leak
