// EXPECT: none
// Zig 0.16.0 fixture: the `Io` spellings below do not exist in Zig 0.15.2.
const std = @import("std");

const max_search_depth = 6;

const Walker = struct {
    gpa: std.mem.Allocator,

    fn joinAlloc(self: *Walker, parts: []const []const u8) ?[]const u8 {
        return std.fs.path.join(self.gpa, parts) catch null;
    }

    /// Issue #60: the iterable directory is released on every exit after the
    /// open - the found return, the exhausted iteration, the iterator error
    /// and the recursive return all leave the scope.
    fn findInTree(
        self: *Walker,
        io: std.Io,
        root: []const u8,
        name: []const u8,
        depth: u32,
    ) ?[]const u8 {
        if (depth > max_search_depth) return null;
        var dir = std.Io.Dir.openDir(.cwd(), io, root, .{ .iterate = true }) catch return null;
        defer dir.close(io);
        var it = dir.iterate();
        while (it.next(io) catch return null) |entry| {
            switch (entry.kind) {
                .file => {
                    if (std.mem.startsWith(u8, entry.name, name)) {
                        return self.joinAlloc(&.{ root, entry.name });
                    }
                },
                .directory, .sym_link => {
                    const sub = self.joinAlloc(&.{ root, entry.name }) orelse continue;
                    if (self.findInTree(io, sub, name, depth + 1)) |p| return p;
                },
                else => {},
            }
        }
        return null;
    }
};
