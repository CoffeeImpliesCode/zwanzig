// EXPECT: line=11 rule=store-violations-engine severity=error message=resource leak
const std = @import("std");

const Context = struct { pool: std.mem.Allocator };

/// The `break` below is written above the registration, so the arm that takes
/// it leaves the block before `defer arena.deinit();` is ever registered. The
/// arena rides out of the frame still holding what this block made, and the
/// `errdefer` beside it settles the error path only.
fn formatSkippedRegistration(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{9});
    std.debug.assert(std.mem.eql(u8, label, "entry=9"));
}

fn cleanupBeforeRegistration(gpa: std.mem.Allocator, drop: bool) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    errdefer arena.deinit();
    inner: {
        const context: Context = .{ .pool = arena.allocator() };
        try formatSkippedRegistration(&context);
        if (drop) break :inner;
        defer arena.deinit();
    }
}

/// The registration is written above the `break` here, so both ways out of the
/// block carry it: the arm that breaks has already registered the disposal, and
/// the arm that runs to the end of the block registers it and then runs it as
/// the block ends.
fn formatRegisteredFirst(context: *const Context) !void {
    const label = try std.fmt.allocPrint(context.pool, "entry={d}", .{8});
    std.debug.assert(std.mem.eql(u8, label, "entry=8"));
}

fn cleanupAfterRegistration(gpa: std.mem.Allocator, drop: bool) !void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    inner: {
        defer arena.deinit();
        const context: Context = .{ .pool = arena.allocator() };
        try formatRegisteredFirst(&context);
        if (drop) break :inner;
    }
}

test "a labeled break settles the arena only where the registration precedes it" {
    // The first frame writes its registration below the `break`, so the arm the
    // break takes leaves the frame holding what the block above it allocated.
    // That arm is the leak pinned above, so this call runs on the page
    // allocator: the frame loses the arena whichever allocator it is handed,
    // and a page handed to the operating system instead of back settles nothing
    // at exit, so the arm that leaks here is a plain run and not a leak report.
    // The second frame writes its registration above the `break`, so the arm
    // that breaks has already registered the disposal and the arm that falls
    // through the block registers it and runs it at the end of that block. Both
    // of its arms settle the arena, so both run on the testing allocator, where
    // a disposal that stops running fails this test.
    try cleanupBeforeRegistration(std.heap.page_allocator, true);
    try cleanupAfterRegistration(std.testing.allocator, true);
    try cleanupAfterRegistration(std.testing.allocator, false);
}
