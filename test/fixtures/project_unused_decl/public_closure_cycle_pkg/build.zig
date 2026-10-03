const std = @import("std");

pub fn build(b: *std.Build) void {
    _ = b.addModule("public-closure-cycle-fixture", .{
        .root_source_file = b.path("src/root.zig"),
    });
}
