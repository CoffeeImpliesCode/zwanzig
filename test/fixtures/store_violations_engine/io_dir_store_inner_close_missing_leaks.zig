const std = @import("std");

/// Control for issue #61: only the nested close is removed, so the directory
/// the recursive search opens is reported while the outer store handle stays
/// released. The report names the inner binding, not the outer one.
const Walker = struct {
    gpa: std.mem.Allocator,

    fn joinAlloc(self: *Walker, parts: []const []const u8) ?[]const u8 {
        return std.fs.path.join(self.gpa, parts) catch null;
    }

    fn findInTree(self: *Walker, io: std.Io, root: []const u8, name: []const u8) ?[]const u8 {
        var dir = std.Io.Dir.openDir(.cwd(), io, root, .{ .iterate = true }) catch return null;
        var it = dir.iterate();
        while (it.next(io) catch return null) |entry| {
            if (std.mem.startsWith(u8, entry.name, name)) {
                return self.joinAlloc(&.{ root, entry.name });
            }
            if (entry.kind == .directory or entry.kind == .sym_link) {
                const sub = self.joinAlloc(&.{ root, entry.name }) orelse continue;
                if (self.findInTree(io, sub, name)) |p| return p;
            }
        }
        return null;
    }

    fn findInStore(self: *Walker, io: std.Io, store: []const u8, name: []const u8) ?[]const u8 {
        var root = std.Io.Dir.openDir(.cwd(), io, store, .{ .iterate = true }) catch return null;
        defer root.close(io);
        var it = root.iterate();
        while (it.next(io) catch return null) |entry| {
            if (entry.kind != .directory and entry.kind != .sym_link) continue;
            if (!std.mem.containsAtLeast(u8, entry.name, 1, "fonts")) continue;
            const share = self.joinAlloc(&.{ store, entry.name, "share", "fonts" }) orelse continue;
            if (self.findInTree(io, share, name)) |p| return p;
        }
        return null;
    }
};

// EXPECT: line=14 rule=store-violations-engine severity=error message=resource leak
