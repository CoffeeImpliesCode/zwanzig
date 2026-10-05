const std = @import("std");

/// One fresh allocation per iteration, released on exactly one of three
/// mutually exclusive exits: an early return, a `continue`, or the loop tail.
/// The `continue` arm and the tail arm release different iterations' items,
/// so a release reported across them describes a double free this function
/// cannot perform.
fn process(gpa: std.mem.Allocator, items: []const usize, stop: usize) !void {
    var index: usize = 0;
    while (index < items.len) : (index += 1) {
        const item = try std.fmt.allocPrint(gpa, "item-{d}", .{items[index]});
        if (items[index] == stop) {
            gpa.free(item);
            return error.Stopped;
        }
        if (items[index] == 0) {
            gpa.free(item);
            continue;
        }
        gpa.free(item);
    }
}

/// The single real leak in this file, kept so that silencing the releases
/// above cannot also silence an allocation nothing releases.
fn unsafeLeak(gpa: std.mem.Allocator) !void {
    _ = try gpa.alloc(u8, 16);
}

// EXPECT: line=27 rule=store-violations-engine severity=error message=resource leak
