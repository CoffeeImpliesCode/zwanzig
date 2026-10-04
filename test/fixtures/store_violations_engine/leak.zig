const std = @import("std");

fn foo(allocator: std.mem.Allocator) !void {
    var ptr = try allocator.alloc(u8, 1);
    ptr[0] = 1;
    std.mem.doNotOptimizeAway(ptr.ptr);
}

// EXPECT: line=4 rule=store-violations-engine severity=error message=resource leak
//
// The binding has to be a mutated, used local: `var ptr` that is never mutated
// and a `_ = ptr;` discard after the allocation are both rejected by both
// frontends ("local variable is never mutated", "pointless discard of local
// constant"), which made this file an AstGen error and the leak unreachable.
// Writing through the slice keeps the allocation in this frame.
