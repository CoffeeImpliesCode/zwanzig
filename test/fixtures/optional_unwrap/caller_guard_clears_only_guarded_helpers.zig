// EXPECT: line=61 rule=optional-unwrap severity=warning
// EXPECT: line=67 rule=optional-unwrap severity=warning
//
// A private drawing helper inherits the guard its one reachable caller
// establishes on that exact field of that exact object. A helper no caller
// proves, or one whose only caller checks a different field, keeps the warning.
const std = @import("std");

const Allocator = std.mem.Allocator;

const Band = struct {
    width: u16 = 80,
    height: u16 = 24,

    fn setHeight(self: *Band, h: u16) void {
        self.height = h;
    }
};

fn appendNumber(sink: *std.ArrayList(u8), gpa: Allocator, n: u16) !void {
    var buf: [8]u8 = undefined;
    const text = std.fmt.bufPrint(&buf, "{d}", .{n}) catch return error.NoSpace;
    try sink.appendSlice(gpa, text);
}

const App = struct {
    interactive: ?Band = null,
    plain: ?Band = null,

    fn paintInteractive(self: *App, sink: *std.ArrayList(u8), gpa: Allocator) !void {
        const b = self.interactive.?;
        try sink.appendSlice(gpa, "interactive ");
        try appendNumber(sink, gpa, b.width);
        try sink.appendSlice(gpa, "x");
        try appendNumber(sink, gpa, b.height);
    }

    fn paintPlain(self: *App, sink: *std.ArrayList(u8), gpa: Allocator) !void {
        const b = self.plain.?;
        try sink.appendSlice(gpa, "plain ");
        try appendNumber(sink, gpa, b.width);
        try sink.appendSlice(gpa, "x");
        try appendNumber(sink, gpa, b.height);
    }

    fn teardown(self: *App, sink: *std.ArrayList(u8), gpa: Allocator) !void {
        if (self.interactive) |*b| {
            _ = b;
            try self.paintInteractive(sink, gpa);
            self.interactive = null;
        }
        if (self.plain) |*b| {
            _ = b;
            try self.paintPlain(sink, gpa);
            self.plain = null;
        }
    }

    // No caller proves `plain`, so the forced unwrap stays a warning.
    fn resetPlain(self: *App, sink: *std.ArrayList(u8), gpa: Allocator) !void {
        try appendNumber(sink, gpa, self.plain.?.width);
    }

    // The guard on `plain` says nothing about `interactive`.
    fn resetInteractive(self: *App, sink: *std.ArrayList(u8), gpa: Allocator) !void {
        if (self.plain != null) {
            try appendNumber(sink, gpa, self.interactive.?.width);
        }
    }
};

test "caller guard: teardown paints both bands it proves" {
    var sink: std.ArrayList(u8) = .empty;
    defer sink.deinit(std.testing.allocator);

    var app: App = .{
        .interactive = .{ .width = 100, .height = 40 },
        .plain = .{ .width = 20, .height = 10 },
    };
    try app.teardown(&sink, std.testing.allocator);
    try std.testing.expect(std.mem.indexOf(u8, sink.items, "interactive 100x40") != null);
    try std.testing.expect(std.mem.indexOf(u8, sink.items, "plain 20x10") != null);
}
