// EXPECT: line=127 rule=optional-unwrap severity=warning
// EXPECT: line=131 rule=optional-unwrap severity=warning
//
// An executed start phase installs its owner fields before any running-phase
// callback, so a running-phase read is proven by the caller's successful start
// rather than by the method name. A pre-start probe and a never-installed
// field have no such evidence and keep the warning.
const std = @import("std");

const Allocator = std.mem.Allocator;

const Band = struct {
    height: u16 = 24,
    first_frame: bool = true,

    fn setHeight(self: *Band, h: u16) void {
        self.height = h;
    }

    fn render(self: *const Band) u16 {
        return self.height;
    }

    fn commit(self: *Band) void {
        self.first_frame = false;
    }
};

const Queue = struct {
    capacity: usize = 0,
    watermark: usize = 0,

    fn init(capacity: usize, watermark: usize) Queue {
        return .{ .capacity = capacity, .watermark = watermark };
    }

    fn drainAll(self: *const Queue, sink: *std.ArrayList(u8), gpa: Allocator) !void {
        _ = self;
        try sink.appendSlice(gpa, "drained");
    }

    fn deinit(self: *Queue) void {
        self.capacity = 0;
        self.watermark = 0;
    }
};

const Caps = struct {
    color: u8 = 0,
};

var queue_budget: usize = 1;

fn resetQueueBudget() void {
    queue_budget = 1;
}

fn openQueue() error{Exhausted}!Queue {
    if (queue_budget == 0) return error.Exhausted;
    queue_budget -= 1;
    return Queue.init(24, 8);
}

fn openTerminal() error{NoTerminal}!u32 {
    return 9;
}

const App = struct {
    gpa: Allocator = undefined,
    band: ?Band = null,
    queue: ?Queue = null,
    io: ?u64 = null,
    tty: ?u32 = null,
    caps: ?Caps = null,
    started: bool = false,

    fn start(self: *App, gpa: Allocator) !void {
        self.gpa = gpa;
        errdefer self.abortSession();
        self.tty = try openTerminal();
        self.io = 1;
        self.queue = try openQueue();
        self.band = Band{};
        self.started = true;
    }

    fn abortSession(self: *App) void {
        if (self.queue) |*q| q.deinit();
        self.queue = null;
        self.band = null;
        self.io = null;
        self.tty = null;
        self.started = false;
    }

    fn stage(self: *App, height: u16) u16 {
        self.band.?.setHeight(height);
        return self.band.?.render();
    }

    fn retire(self: *App, sink: *std.ArrayList(u8)) !void {
        try self.queue.?.drainAll(sink, self.gpa);
        self.band.?.commit();
    }

    fn probeTerminal(self: *App) u32 {
        return self.tty.?;
    }

    fn flushIfQueued(self: *App, sink: *std.ArrayList(u8)) !void {
        if (self.queue) |*q| {
            try q.drainAll(sink, self.gpa);
            _ = self.tty.?;
        }
    }

    fn teardown(self: *App) void {
        if (self.queue) |*q| q.deinit();
        self.queue = null;
        self.band = null;
        self.io = null;
        self.tty = null;
        self.started = false;
    }

    fn probeBeforeStart(self: *App) u16 {
        return self.band.?.render();
    }

    fn probeNeverInstalled(self: *App) u8 {
        return self.caps.?.color;
    }
};

test "lifecycle phases: the post-start helpers see every installed field" {
    resetQueueBudget();
    var sink: std.ArrayList(u8) = .empty;
    defer sink.deinit(std.testing.allocator);

    var app: App = .{};
    try app.start(std.testing.allocator);
    try std.testing.expectEqual(@as(u16, 40), app.stage(40));
    try std.testing.expectEqual(@as(u32, 9), app.probeTerminal());
    try app.retire(&sink);
    try app.flushIfQueued(&sink);
    app.teardown();
    try std.testing.expectEqualStrings("draineddrained", sink.items);
}

test "lifecycle phases: a failed start clears whatever it managed to install" {
    resetQueueBudget();
    queue_budget = 0;
    var app: App = .{};
    try std.testing.expectError(error.Exhausted, app.start(std.testing.allocator));
    try std.testing.expect(app.band == null);
    try std.testing.expect(app.queue == null);
    try std.testing.expect(app.tty == null);
}

test "lifecycle phases: the pre-start controls really have null fields" {
    const app: App = .{};
    try std.testing.expect(app.band == null);
    try std.testing.expect(app.caps == null);
    _ = &App.probeBeforeStart;
    _ = &App.probeNeverInstalled;
}
