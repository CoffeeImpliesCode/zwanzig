const std = @import("std");
const Error = error{OutOfMemory};

/// The resize failed on this arm, so the fallback ran and handed back a block
/// it never allocated. The original is still live and nothing releases it:
/// reading the resize off the `catch` expression as a whole consumed the
/// source the success arm owns and hid this leak.
fn lostFallback(gpa: std.mem.Allocator) Error![]u8 {
    const original = try gpa.alloc(u8, 4);
    return gpa.realloc(original, 8) catch &.{};
}

/// The fallback releases the original before it returns, so this arm owns
/// nothing by the time it hands back the empty slice.
fn freedFallback(gpa: std.mem.Allocator) Error![]u8 {
    const original = try gpa.alloc(u8, 4);
    return gpa.realloc(original, 8) catch {
        gpa.free(original);
        return &.{};
    };
}

/// The handler propagates the very error the guarded call produced, so the
/// errdefer above still owns the original here and releases it. Reading the
/// rethrow as an ordinary handled value left that release unapplied and
/// reported a block this path does free.
fn rethrownFailure(gpa: std.mem.Allocator) Error![]u8 {
    const original = try gpa.alloc(u8, 4);
    errdefer gpa.free(original);
    return gpa.realloc(original, 8) catch |err| return err;
}

/// The fallback hands the original itself to the caller, so this arm
/// transfers the block to the caller rather than dropping it.
fn fallbackReturnsOriginal(gpa: std.mem.Allocator) Error![]u8 {
    const original = try gpa.alloc(u8, 4);
    return gpa.realloc(original, 8) catch original;
}

// A fallback that falls through is an ordinary return and not an error path:
// the handler ran and the error was handled, so what it left live still
// belongs to this frame and keeps being reported. A handler that propagates
// the error is the opposite and is quiet.

/// The same fallback with the parentheses the control above does not have:
/// `return (gpa.realloc(original, 8) catch &.{});`. Which arm is read is not
/// settled by those parentheses: the group wraps the same `catch`, and the
/// fallback still hands back a block it never allocated. This arm owns
/// nothing, so the original is still live on it and nothing releases it.
fn parenthesizedLostFallback(gpa: std.mem.Allocator) Error![]u8 {
    const original = try gpa.alloc(u8, 4);
    return (gpa.realloc(original, 8) catch &.{});
}

/// The same rethrow with its payload parenthesised, `return (err);` where the
/// control above writes `return err;`. The handler still propagates the very
/// error the guarded call produced, so the `errdefer` above still owns the
/// original on that path and still releases it. Grouping the payload does not
/// change the arm that runs, or what that arm owns.
fn parenthesizedRethrownFailure(gpa: std.mem.Allocator) Error![]u8 {
    const original = try gpa.alloc(u8, 4);
    errdefer gpa.free(original);
    return gpa.realloc(original, 8) catch |err| return (err);
}

test "the returned fallback remains live after a failed growth" {
    const testing = std.testing;
    var failing = std.testing.FailingAllocator.init(testing.allocator, .{
        .fail_index = 1,
        .resize_fail_index = 0,
    });
    {
        const bytes = try fallbackReturnsOriginal(failing.allocator());
        defer failing.allocator().free(bytes);
        try testing.expectEqual(@as(usize, 4), bytes.len);
        @memset(bytes, 0x5a);
        try testing.expectEqualSlices(u8, &([_]u8{0x5a} ** 4), bytes);
    }
    try testing.expectEqual(failing.allocated_bytes, failing.freed_bytes);
}

test "the parenthesized rethrow releases the original when the growth fails" {
    const testing = std.testing;

    // Refuse both the in-place remap and its replacement allocation.
    var failing = std.testing.FailingAllocator.init(testing.allocator, .{
        .fail_index = 1,
        .resize_fail_index = 0,
    });
    try testing.expectError(
        error.OutOfMemory,
        parenthesizedRethrownFailure(failing.allocator()),
    );
    try testing.expectEqual(@as(usize, 4), failing.allocated_bytes);
    try testing.expectEqual(failing.allocated_bytes, failing.freed_bytes);
}

// EXPECT: line=9 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=51 rule=store-violations-engine severity=error message=resource leak
