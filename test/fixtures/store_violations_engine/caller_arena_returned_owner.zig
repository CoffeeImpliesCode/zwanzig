const std = @import("std");

const Context = struct { pool: std.mem.Allocator };

/// The owner carries the arena itself and nothing taken out of it: an
/// allocator copied out of the arena would point at a frame that is gone by
/// the time the owner is read.
const Owner = struct { arena: std.heap.ArenaAllocator };

/// The same arena beside a field of its own, so a hand-off written as a struct
/// initializer carrying more than one entry is read for what it carries.
const TaggedOwner = struct {
    arena: std.heap.ArenaAllocator,
    tag: u8,
};

/// An owner written as the address of the arena rather than as the arena. What
/// a hand-off carries decides whether the frame that allocated is still there
/// to be read from, and a pointer into a frame that is gone carries nothing.
const PointerOwner = struct { arena: *std.heap.ArenaAllocator };

fn formatInsideOwner(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// The arena behind the context is the arena this frame hands back, so what the
/// frame above allocated rides out inside the owner and is released when that
/// owner disposes it. `errdefer` alone would not settle it: that runs on the
/// error path only, and the success path settles itself by carrying the arena
/// out of the frame.
pub fn makeOwner(gpa: std.mem.Allocator) !Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideOwner(&context);
    return .{ .arena = arena };
}

fn formatInsideEveryPath(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{5});
    std.debug.assert(std.mem.eql(u8, label, "entry=5"));
}

/// One owner or the other, and both carry this arena. Every way out of the frame
/// hands the same arena on, which is what makes the hand-off one the caller can
/// count on.
pub fn makeEveryPathOwner(gpa: std.mem.Allocator, tag: u8) !TaggedOwner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideEveryPath(&context);
    if (tag == 0) return .{ .arena = arena, .tag = tag };
    return .{ .arena = arena, .tag = 7 };
}

fn formatInsideLiteral(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{4});
    std.debug.assert(std.mem.eql(u8, label, "entry=4"));
}

/// The arena is disposed where the call sits instead of handed back. The
/// `errdefer` settles the error the call can take out of the frame, and the
/// plain statement settles the way out that reaches it.
pub fn makeLiteralRelease(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideLiteral(&context);
    arena.deinit();
}

fn formatInsideConditional(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{3});
    std.debug.assert(std.mem.eql(u8, label, "entry=3"));
}

/// One path hands the arena back and the next hands back nothing at all. The
/// `errdefer` runs on the error path only, so the second path leaves what the
/// frame above allocated charged to a frame that is gone.
pub fn makeConditionalOwner(gpa: std.mem.Allocator, keep: bool) !?Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideConditional(&context);
    if (keep) return .{ .arena = arena };
    return null;
}

fn formatInsideForeignArena(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{8});
    std.debug.assert(std.mem.eql(u8, label, "entry=8"));
}

/// Two arenas, and the one handed back is not the one the block below was
/// charged to. The first arena goes out of reach the moment this frame returns,
/// and what it holds goes with it.
pub fn makeForeignOwner(gpa: std.mem.Allocator) !Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideForeignArena(&context);
    const kept = std.heap.ArenaAllocator.init(gpa);
    return .{ .arena = kept };
}

fn formatInsideScoped(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{2});
    std.debug.assert(std.mem.eql(u8, label, "entry=2"));
}

/// The arena the block below is charged to is written in a block of its own, and
/// the arena the owner carries is the one the frame declared. Leaving the frame
/// carries that one out and leaves this one behind with what it holds. A second
/// binding spelled like the first would say nothing new here: the two are read
/// by identity, not by their spelling.
pub fn makeScopedOwner(gpa: std.mem.Allocator) !Owner {
    const arena = std.heap.ArenaAllocator.init(gpa);
    {
        var scratch = std.heap.ArenaAllocator.init(gpa);
        const context: Context = .{ .pool = scratch.allocator() };
        try formatInsideScoped(&context);
    }
    return .{ .arena = arena };
}

fn formatInsideScalar(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{1});
    std.debug.assert(std.mem.eql(u8, label, "entry=1"));
}

/// What comes back is a number read off the arena, not the arena. What the
/// block below was charged to stays charged to a frame that is gone by the time
/// anyone reads that number.
pub fn makeScalarOwner(gpa: std.mem.Allocator) !usize {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideScalar(&context);
    return arena.queryCapacity();
}

fn formatInsideForgotten(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{7});
    std.debug.assert(std.mem.eql(u8, label, "entry=7"));
}

/// Nothing disposes this arena and nothing hands it back, so what the block
/// below was charged to stays this caller's to release - and is not released.
pub fn makeForgotten(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideForgotten(&context);
}

fn formatInsidePlainPool(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{6});
    std.debug.assert(std.mem.eql(u8, label, "entry=6"));
}

/// An ordinary allocator belongs to nobody's arena: there is nothing here to
/// dispose and nothing to hand back, so the block below is a free obligation of
/// the frame that made it.
pub fn makePlainPoolOwner(gpa: std.mem.Allocator) !void {
    const context: Context = .{ .pool = gpa };
    try formatInsidePlainPool(&context);
}

fn formatInsideLateDefer(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{10});
    std.debug.assert(std.mem.eql(u8, label, "entry=10"));
}

/// The way out written above the `defer` leaves the frame without ever
/// registering it. A `defer` a `return` can jump over settles nothing on the
/// path that jumps it.
pub fn makeLateDefer(gpa: std.mem.Allocator, drop: bool) !?Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideLateDefer(&context);
    if (drop) return null;
    defer arena.deinit();
    return null;
}

fn formatInsideLabeledEscape(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{11});
    std.debug.assert(std.mem.eql(u8, label, "entry=11"));
}

/// The `defer` belongs to the block its label names, and one way out of that
/// block is written above it. The `break` skips the registration, and what
/// either way out hands back settles nothing.
pub fn makeLabeledEscape(gpa: std.mem.Allocator, drop: bool) !?Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    return label: {
        try formatInsideLabeledEscape(&context);
        if (drop) break :label null;
        defer arena.deinit();
        break :label null;
    };
}

fn formatInsideReturnOperand(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{12});
    std.debug.assert(std.mem.eql(u8, label, "entry=12"));
}

/// The call is written inside the operand of the return, so that return is the
/// way out the call takes and not one written ahead of it. What it hands back
/// is nothing, and the `errdefer` beside it settles the error path only.
pub fn makeReturnOperand(gpa: std.mem.Allocator) !?Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    return label: {
        try formatInsideReturnOperand(&context);
        break :label null;
    };
}

fn formatInsidePointerOwner(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{13});
    std.debug.assert(std.mem.eql(u8, label, "entry=13"));
}

/// What the owner carries is the address of a local. The frame holding the
/// arena is gone by the time the pointer is read, so what the arena holds rides
/// out behind a dead pointer.
pub fn makePointerOwner(gpa: std.mem.Allocator) !PointerOwner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsidePointerOwner(&context);
    return .{ .arena = &arena };
}

fn formatInsideNestedFrame(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{14});
    std.debug.assert(std.mem.eql(u8, label, "entry=14"));
}

/// The frame declares a helper of its own, and that helper disposes an arena
/// of its own. A disposal made in a frame nested in the caller is a disposal
/// of that frame: the arena this frame allocated through is untouched by it,
/// and nothing else here releases it.
pub fn makeNestedFrame(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    const Nested = struct {
        fn dispose(inner: std.mem.Allocator) void {
            var nested_arena = std.heap.ArenaAllocator.init(inner);
            defer nested_arena.deinit();
            _ = nested_arena.allocator();
        }
    };
    Nested.dispose(gpa);
    try formatInsideNestedFrame(&context);
}

fn formatInsideExplicitError(context: *const Context) error{OutOfMemory}!void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{15});
    std.debug.assert(std.mem.eql(u8, label, "entry=15"));
}

/// The frame hands back an error the source spells out on one way out, and the
/// arena itself on the one beside it. The `errdefer` settles the exit that
/// carries the error, and the value beside it carries the arena by value, so
/// both ways out are settled.
pub fn makeExplicitErrorOwner(gpa: std.mem.Allocator, fail: bool) !Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator() };
    try formatInsideExplicitError(&context);
    if (fail) return error.NoOwner;
    return .{ .arena = arena };
}

test "the arena the owner carries owns the block the context allocated" {
    var owner = try makeOwner(std.testing.allocator);
    defer owner.arena.deinit();

    // Every way out of a frame is settled by one of the two things it has: the
    // error it hands back by the `errdefer` beside it, the success it hands
    // back by the arena that value carries.
    try std.testing.expectError(error.NoOwner, makeExplicitErrorOwner(std.testing.allocator, true));
    var explicit = try makeExplicitErrorOwner(std.testing.allocator, false);
    defer explicit.arena.deinit();

    var every_path = try makeEveryPathOwner(std.testing.allocator, 4);
    defer every_path.arena.deinit();

    // The disposal written where the call sits settles the way out that reaches
    // it, and `errdefer` settles the one the call can take.
    try makeLiteralRelease(std.testing.allocator);
}

// EXPECT: line=74 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=91 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=108 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=128 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=144 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=157 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=170 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=188 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=208 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=226 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=242 rule=store-violations-engine severity=error message=resource leak
