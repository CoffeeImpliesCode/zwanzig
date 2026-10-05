const std = @import("std");
const Error = error{OutOfMemory};

/// Every arm of this nested `catch` opens a handle and the one deferred close
/// settles whichever arm ran: the fallback's on the arm where the primary
/// failed, and the inner handler's `return` reaches nothing it owns.
fn nestedOpenClosesEveryArm(path: []const u8, other: []const u8) void {
    const file = std.fs.cwd().openFile(path, .{}) catch (std.fs.cwd().openFile(other, .{}) catch return);
    defer file.close();
}

/// The same binding with the close left out. The arm where the primary failed
/// really did open the fallback, so the handle the binding holds there is
/// reported. The inner `catch`'s success edge puts the error state back to
/// normal, so reading the binding off the outer `catch` named the primary
/// instead - a call that arm never made.
fn nestedFallbackOpenLeaks(path: []const u8, other: []const u8) void {
    const file = std.fs.cwd().openFile(path, .{}) catch (std.fs.cwd().openFile(other, .{}) catch return);
    _ = file;
}

/// `catch` is left-associative, so the binding below is
/// `(openFile(path) catch openFile(other)) catch return`: the inner expression
/// is the guarded operand of the outer one rather than its handler, and it is
/// still an expression that decides arms of its own. The control flow builds
/// it as a node of its own, so each arm that leaves it says which of the two
/// opens ran. The obligation is one open either way, and the fallback's must
/// not be dropped because it is written inside the outer operand.
fn leftAssociatedNestedCatchLeaks(path: []const u8, other: []const u8) void {
    const file = std.fs.cwd().openFile(path, .{}) catch std.fs.cwd().openFile(other, .{}) catch return;
    _ = file;
}

/// The inner `catch` failed too, so the binding holds the empty fallback and
/// the resize that would have consumed `original` never ran. The original is
/// still live and nothing releases it. Reading the binding off the outer
/// `catch` as a whole named the primary's resize instead and consumed a block
/// this path still owns.
fn nestedResizeKeepsOriginal(gpa: std.mem.Allocator) Error![]u8 {
    const original = try gpa.alloc(u8, 4);
    return gpa.realloc(original, 8) catch (gpa.realloc(original, 8) catch &.{});
}

/// The two arms allocate through different allocators, and only the one this
/// path ran owns the block: the arena's own `deinit` releases what the primary
/// allocated, and nothing releases what the fallback allocated through the
/// plain allocator.
fn nestedFallbackPlainAllocatorLeaks(gpa: std.mem.Allocator) void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const arena_allocator = arena.allocator();
    const block = arena_allocator.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch return);
    _ = block;
}

/// `catch` is left-associative, so the binding below is
/// `(arena_allocator.alloc(u8, 8) catch gpa.alloc(u8, 8)) catch return`: the
/// inner expression is the guarded operand of the outer one rather than its
/// handler, and the arm where that operand's own fallback ran really did
/// allocate through the plain allocator. The arena's `deinit` releases what
/// the primary allocated; nothing releases what the fallback allocated.
fn leftAssociatedMixedAllocatorLeaks(gpa: std.mem.Allocator) void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const arena_allocator = arena.allocator();
    const block = arena_allocator.alloc(u8, 8) catch gpa.alloc(u8, 8) catch return;
    _ = block;
}

/// The same left-associated shape with both arms on one allocator the body
/// releases, so whichever arm ran has its block settled on every path.
fn leftAssociatedSameAllocatorIsReleased(gpa: std.mem.Allocator) void {
    const block = gpa.alloc(u8, 8) catch gpa.alloc(u8, 8) catch return;
    defer gpa.free(block);
}

/// Six nested handlers, so the path carries more pending arms than a state
/// holds itself, and the arm that produced the block is the innermost one:
/// the arena released what the five primaries allocated, and nothing
/// releases what the plain allocator allocated in the fallback.
fn sixNestedFallbackLeaks(gpa: std.mem.Allocator) void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const arena_allocator = arena.allocator();
    const block = arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch return)))));
    _ = block;
}

/// The same six-deep chain with every arm on one allocator the body releases:
/// the extra arms decide which call the binding names, and none of them
/// leaves a block behind.
fn sixNestedSameAllocatorIsReleased(gpa: std.mem.Allocator) void {
    const block = gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch return)))));
    defer gpa.free(block);
}

/// The arm that produced the returned block is the operand's own fallback,
/// which is not a resize: the primary's resize never ran, so the block it was
/// handed is still live here and nothing consumed it. Reading the binding
/// off the `catch` as a whole named the primary's resize instead and
/// consumed that block on an arm where the resize never happened.
fn leftAssociatedFallbackKeepsResizeSource(gpa: std.mem.Allocator) Error![]u8 {
    const original = try gpa.alloc(u8, 4);
    return gpa.realloc(original, 8) catch gpa.alloc(u8, 8) catch gpa.realloc(original, 8);
}

/// Forty-one nested handlers, so the chain runs deeper than any fixed number
/// of parentheses or arms a walk could bound itself to. The arm that produced
/// `block` is the innermost fallback, a plain-allocator allocation nothing
/// releases, while the arena's own `deinit` releases what the forty primaries
/// allocated. Reading the chain off to a depth it was written past hands the
/// binding one of those primaries instead, and the leak is reported nowhere.
fn fortyOneNestedFallbackLeaks(gpa: std.mem.Allocator) void {
    var arena = std.heap.ArenaAllocator.init(gpa);
    defer arena.deinit();
    const arena_allocator = arena.allocator();
    const block = arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (arena_allocator.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch return))))))))))))))))))))))))))))))))))))))));
    _ = block;
}

/// The same forty-one-deep chain with every arm on one allocator the body
/// releases: the extra arms decide which call the binding names, and none of
/// them leaves a block behind.
fn fortyOneNestedSameAllocatorIsReleased(gpa: std.mem.Allocator) void {
    const block = gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch (gpa.alloc(u8, 8) catch return))))))))))))))))))))))))))))))))))))))));
    defer gpa.free(block);
}

// EXPECT: line=18 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=30 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=40 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=52 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=66 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=85 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=103 rule=store-violations-engine severity=error message=resource leak
// EXPECT: line=117 rule=store-violations-engine severity=error message=resource leak
