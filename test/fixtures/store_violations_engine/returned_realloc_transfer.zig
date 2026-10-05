const std = @import("std");
const Error = error{OutOfMemory};

fn prefix(gpa: std.mem.Allocator, input: []const u8, keep: usize) Error![]u8 {
    const bytes = try gpa.alloc(u8, input.len);
    errdefer gpa.free(bytes);
    @memcpy(bytes, input);
    return gpa.realloc(bytes, keep);
}

fn caller(gpa: std.mem.Allocator) Error!void {
    const result = try prefix(gpa, "abcdef", 3);
    defer gpa.free(result);
    std.debug.assert(std.mem.eql(u8, result, "abc"));
}

// A successful realloc hands the block to the caller, so the errdefer above
// no longer owns anything and the original must not be reported as leaked.
// The source slice is read as an argument while the block is still live, so
// neither is a use after free.

// EXPECT: none
