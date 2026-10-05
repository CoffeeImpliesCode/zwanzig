const std = @import("std");
const Error = error{OutOfMemory};

fn lostReplacement(gpa: std.mem.Allocator) Error!usize {
    const bytes = try gpa.alloc(u8, 16);
    errdefer gpa.free(bytes);
    const replacement = try gpa.realloc(bytes, 8);
    return replacement.len;
}

fn discardedReplacement(gpa: std.mem.Allocator) Error!void {
    const bytes = try gpa.alloc(u8, 16);
    errdefer gpa.free(bytes);
    _ = try gpa.realloc(bytes, 8);
}

// A successful realloc consumes the original, so only the replacement is
// left to report, and it is the binding the call was given rather than the
// slice the call was handed. `return replacement.len` hands back a length
// and not the block, which is what keeps the replacement from escaping into
// a caller that could never release it.

// EXPECT: line=7 rule=store-violations-engine severity=error message=resource
// EXPECT: line=14 rule=store-violations-engine severity=error message=resource
