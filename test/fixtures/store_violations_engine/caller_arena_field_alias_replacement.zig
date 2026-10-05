const std = @import("std");

const Context = struct {
    pool: std.mem.Allocator,
    name: []const u8,
};

/// The frame takes the address of the field the allocation arrives through and
/// writes the allocator out through it. What the block below is charged to is
/// then an allocator the arena the caller disposes never owned, so nothing the
/// caller did proves anything here.
fn replacedThroughPointer(context: *Context) !void {
    const slot = &context.pool;
    slot.* = std.heap.page_allocator;
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// The same substitution one binding further out: a pointer to a pointer
/// reaches the field exactly where the pointer itself does.
fn replacedThroughChainedAlias(context: *Context) !void {
    const slot = &context.pool;
    const alias = slot;
    alias.* = std.heap.page_allocator;
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn install(slot: *std.mem.Allocator, gpa: std.mem.Allocator) void {
    slot.* = gpa;
}

/// The frame hands the address of the field to another function. What that
/// function writes cannot be read off this frame, and the block below may come
/// from whatever allocator it put there.
fn handedOutPointer(context: *Context, gpa: std.mem.Allocator) !void {
    const slot = &context.pool;
    install(slot, gpa);
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// Taking the address of the field and reading through it leaves the caller's
/// context alone, so the block below still belongs to the arena the caller
/// disposes.
fn readThroughPointer(context: *const Context) !void {
    const slot = &context.pool;
    std.debug.assert(slot.* == context.pool);
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// The address copied from one local into another is that same address under
/// another name, and reading through the far end of the chain still only reads
/// the caller's field.
fn readThroughChainedAlias(context: *const Context) !void {
    const slot = &context.pool;
    const again = slot;
    const also = again;
    std.debug.assert(also.* == context.pool);
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// A method reaches its own receiver through a parameter the call site never
/// writes, so the written argument of `installer.count(context)` is the second
/// parameter of the frame below and not its first.
const Installer = struct {
    gpa: std.mem.Allocator,
    installed: usize,

    /// Writes the address it is handed: the caller's allocator field holds
    /// this allocator from here on.
    fn replace(self: *Installer, slot: *std.mem.Allocator) void {
        self.installed += 1;
        slot.* = self.gpa;
    }

    /// Writes its own state, which is a state of its own, and reads one field
    /// off the context it is handed. The allocator field is not the field it
    /// reads, and no address is taken of it.
    fn count(self: *Installer, context: *const Context) void {
        self.installed += @intFromBool(context.name.len != 0);
    }
};

/// The address of the field reaches a method that writes through it, so the
/// frame does not leave the caller's context alone.
fn replacedThroughMethodPointer(context: *Context, installer: *Installer) !void {
    const slot = &context.pool;
    installer.replace(slot);
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// The address reaches a method that only reads the field it is handed and
/// writes its own receiver, so the caller's context is left alone and the
/// block below still belongs to the arena the caller disposes.
fn readThroughMethodPointer(context: *const Context, installer: *Installer) !void {
    const slot = &context;
    installer.count(slot);
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

/// The field beside the allocator is a value of the context's own. Writing it
/// swaps nothing the allocation below runs through, so the block still belongs
/// to the arena the caller disposes.
fn writesBesideTheAllocator(context: *const Context) !void {
    const name = &context.name;
    name.* = "arena";
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn replacementCaller(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try replacedThroughPointer(&context);
}

fn chainedAliasCaller(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try replacedThroughChainedAlias(&context);
}

fn handOffCaller(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try handedOutPointer(&context, gpa);
}

fn readonlyCaller(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try readThroughPointer(&context);
}

fn readonlyChainedCaller(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try readThroughChainedAlias(&context);
}

fn siblingFieldCaller(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    try writesBesideTheAllocator(&context);
}

fn methodPointerCaller(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    var context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    var installer: Installer = .{ .gpa = gpa, .installed = 0 };
    try replacedThroughMethodPointer(&context, &installer);
}

fn methodReaderCaller(gpa: std.mem.Allocator) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const context: Context = .{ .pool = arena.allocator(), .name = "arena" };
    var installer: Installer = .{ .gpa = arena.allocator(), .installed = 0 };
    try readThroughMethodPointer(&context, &installer);
}

// EXPECT: line=15 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=25 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=39 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=92 rule=store-violations-engine severity=error message=resource leak
