const std = @import("std");
const Error = error{ OutOfMemory, BadInput };

fn growInPlace(gpa: std.mem.Allocator, n: usize) Error!void {
    var bytes = try gpa.alloc(u8, 16);
    errdefer gpa.free(bytes);
    bytes = try gpa.realloc(bytes, n);
    bytes[0] = 1;
    gpa.free(bytes);
}

fn growThenFail(gpa: std.mem.Allocator, n: usize) Error!void {
    var bytes = try gpa.alloc(u8, 16);
    errdefer gpa.free(bytes);
    bytes = try gpa.realloc(bytes, n);
    if (n == 0) return Error.BadInput;
    gpa.free(bytes);
}

// `bytes = realloc(bytes, n)` names one region on both sides: the assignment
// has already replaced what the binding held, so the successful resize
// consumes nothing and the replacement stays live until this frame releases
// it. Reading or releasing it afterwards is ordinary, and the error path out
// of `growThenFail` still owns the original the failed resize left behind.

// EXPECT: none
