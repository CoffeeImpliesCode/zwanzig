const std = @import("std");

/// The context carries the allocator the block below is charged to, and a name
/// that is a field of the context's own rather than of the arena.
const Context = struct {
    pool: std.mem.Allocator,
    name: []const u8,
};

/// The same allocator reached one field further out, through a context that
/// carries another context by value.
const Inner = struct {
    pool: std.mem.Allocator,
};

const Outer = struct {
    inner: Inner,
};

/// The owner carries the arena itself and nothing taken out of it. Whatever
/// rides out belongs to the arena the caller receives.
const Owner = struct {
    arena: std.heap.ArenaAllocator,
};

/// What the block below makes rides out inside the arena this frame hands back,
/// so the caller that receives the arena receives the block with it.
fn formatUnderReturnedOwner(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runReturnedOwner(gpa: std.mem.Allocator) !Owner {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatUnderReturnedOwner(&context);
    const owner: Owner = .{ .arena = arena };
    return owner;
}

/// The address of the context is taken and the call is made through it. Nothing
/// is written through that address, so the field this block runs through is
/// still the one the declaration put there.
fn formatUnderPointerSlot(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runPointerSlot(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    const slot = &context;
    try formatUnderPointerSlot(slot);
    arena.deinit();
}

/// A number read off the context is a value of its own. Reading one and adding
/// to it writes nothing into the context, so the field this block runs through
/// still belongs to the arena the caller disposes.
fn formatUnderScalarRead(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runScalarRead(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    var length: usize = context.name.len;
    length += 1;
    std.debug.assert(length == 6);
    try formatUnderScalarRead(&context);
}

/// The allocator sits one field further out, inside a context the outer one
/// carries by value. Reading it at that distance is reading the same allocator
/// the caller put there.
fn formatUnderNestedBinding(context: *const Outer) !void {
    const label = try std.fmt.allocPrint(context.inner.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runNestedBinding(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    const inner: Inner = .{ .pool = arena.allocator() };
    const outer: Outer = .{ .inner = inner };
    try formatUnderNestedBinding(&outer);
    arena.deinit();
}

/// Writes the address it is handed straight into the field that address points
/// at. What the caller's declaration put in that field is gone from here on,
/// and the caller cannot read what replaced it.
fn installPool(slot: *std.mem.Allocator, gpa: std.mem.Allocator) void {
    slot.* = gpa;
}

/// The field is replaced before the block below is allocated, and the
/// replacement arrives through a pointer this frame cannot read. What the block
/// makes is charged to an allocator the arena the caller disposes never owned,
/// so nothing the caller does releases it.
fn formatAfterInlineReplacement(context: *Context, gpa: std.mem.Allocator) !void {
    installPool(&context.pool, gpa);
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runInlineReplacement(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatAfterInlineReplacement(&context, gpa);
}

test "a context binding the caller leaves alone owns the block its callee made" {
    // An arena handed back by value carries what it was charged to, so the
    // caller disposing it releases the block too.
    var owner = try runReturnedOwner(std.testing.allocator);
    defer owner.arena.deinit();

    // An address taken of the context, a scalar read off it and a context
    // carried inside another one are all reads: none of the three replaces the
    // field the block above them runs through, so all three frames own it.
    try runPointerSlot(std.testing.allocator);
    try runScalarRead(std.testing.allocator);
    try runNestedBinding(std.testing.allocator);
}

test "the substitution that leaves the arena owning nothing is made by hand here" {
    // The frame above makes this substitution and then allocates through the
    // substituted field, so what it makes is charged to an allocator the arena
    // never owned. That frame is not run here: this test makes the same
    // substitution, allocates its own control block through the substituted
    // field, reads it, and releases it itself.
    const gpa = std.testing.allocator;
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    installPool(&context.pool, gpa);
    const control = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    defer gpa.free(control);
    try std.testing.expectEqualStrings("entry=9", control);
    try std.testing.expect(context.pool.ptr == gpa.ptr);
    _ = &runInlineReplacement;
}

/// The same read as the one above, reached through four copies of the
/// context: a grouping, the parameter written out under a name of its own, a
/// cast that hands that same pointer back, and an `@as` that names the type
/// the value already has. All four leave the caller's context where it was,
/// so what each block makes is still charged to the arena the caller
/// disposes.
fn formatUnderGroupedCopy(context: *const Context) !void {
    const alias = (context);
    const label = try std.fmt.allocPrint(alias.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runGroupedCopy(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatUnderGroupedCopy(&context);
}

fn formatUnderPlainCopy(context: *const Context) !void {
    const alias = context;
    const label = try std.fmt.allocPrint(alias.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runPlainCopy(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatUnderPlainCopy(&context);
}

fn formatUnderCastCopy(context: *const Context) !void {
    const alias = @constCast(context);
    const label = try std.fmt.allocPrint(alias.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runCastCopy(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatUnderCastCopy(&context);
}

fn formatUnderAsCopy(context: *const Context) !void {
    const alias = @as(*const Context, context);
    const label = try std.fmt.allocPrint(alias.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runAsCopy(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatUnderAsCopy(&context);
}

/// A cast hands back the very pointer the parameter holds, so a write through
/// the copy lands in the caller's context exactly where a write through the
/// parameter itself does, whichever way the copy is spelled. What the block
/// below is charged to is then an allocator the arena the caller disposes
/// never owned.
fn formatThroughCastAlias(context: *const Context, gpa: std.mem.Allocator) !void {
    const alias = @constCast(context);
    alias.*.pool = gpa;
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runCastAlias(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatThroughCastAlias(&context, gpa);
}

fn formatThroughAsAlias(context: *Context, gpa: std.mem.Allocator) !void {
    const alias = @as(*Context, context);
    alias.*.pool = gpa;
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn runAsAlias(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try formatThroughAsAlias(&context, gpa);
}

test "a copy of the context reads the field it points at and writes nothing" {
    // All four frames above read the one field and write nothing, so each of
    // them leaves the context the caller declared alone.
    try runGroupedCopy(std.testing.allocator);
    try runPlainCopy(std.testing.allocator);
    try runCastCopy(std.testing.allocator);
    try runAsCopy(std.testing.allocator);
    _ = &runCastAlias;
    _ = &runAsAlias;
}

// EXPECT: line=107 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=216 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=230 rule=store-violations-engine severity=error message=resource leak
