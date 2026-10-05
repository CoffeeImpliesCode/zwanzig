// EXPECT: line=88 rule=optional-unwrap severity=warning
// EXPECT: line=93 rule=optional-unwrap severity=warning
//
// A fallible constructor that installs its optional fields on every success
// path hands those facts to the value the caller receives, and through a
// nested owner wrapper. A default-constructed owner and an undefined owner
// carry no such fact and keep the warning.
const std = @import("std");

const Allocator = std.mem.Allocator;

const Region = struct {
    height: u16 = 24,
    first_frame: bool = true,

    fn setHeight(self: *Region, h: u16) void {
        self.height = h;
    }

    fn render(self: *const Region) u16 {
        return self.height;
    }
};

const Queue = struct {
    capacity: usize = 0,

    fn init(capacity: usize) Queue {
        return .{ .capacity = capacity };
    }

    fn deinit(self: *Queue) void {
        self.capacity = 0;
    }
};

var budget: usize = 4;

fn resetBudget() void {
    budget = 4;
}

fn openQueue() error{Exhausted}!Queue {
    if (budget == 0) return error.Exhausted;
    budget -= 1;
    return Queue.init(24);
}

const Session = struct {
    region: ?Region = null,
    queue: ?Queue = null,
    height: u16 = 0,

    fn deinit(self: *Session) void {
        if (self.queue) |*q| q.deinit();
        self.queue = null;
        self.region = null;
    }
};

fn setupSession(height: u16) error{Exhausted}!Session {
    return .{
        .region = Region{},
        .queue = try openQueue(),
        .height = height,
    };
}

const LoopDriver = struct {
    session: Session,
    gpa: Allocator,

    fn deinit(self: *LoopDriver) void {
        self.session.deinit();
    }

    fn frameHeight(self: *const LoopDriver) u16 {
        return self.session.region.?.render();
    }
};

fn setupLoopDriver(gpa: Allocator, height: u16) error{Exhausted}!LoopDriver {
    return .{ .session = try setupSession(height), .gpa = gpa };
}

fn bareSession() u16 {
    const s: Session = .{};
    return s.region.?.render();
}

fn probeBeforeSetup() u16 {
    const driver: LoopDriver = undefined;
    return driver.session.region.?.render();
}

test "constructor value: the caller reads every field the constructor set" {
    resetBudget();
    var s = try setupSession(30);
    defer s.deinit();
    s.region.?.setHeight(30);
    try std.testing.expectEqual(@as(u16, 30), s.region.?.render());
    try std.testing.expect(s.queue.?.capacity == 24);
}

test "constructor value: a driver over a constructed session reports its frame" {
    resetBudget();
    var driver = try setupLoopDriver(std.testing.allocator, 40);
    defer driver.deinit();
    try std.testing.expectEqual(@as(u16, 24), driver.frameHeight());
    try std.testing.expect(driver.session.queue.?.capacity == 24);
}

test "constructor value: an exhausted budget makes the constructor fail" {
    resetBudget();
    budget = 0;
    try std.testing.expectError(error.Exhausted, setupSession(24));
}

test "constructor value: the pre-construction controls really are empty" {
    const s: Session = .{};
    try std.testing.expect(s.region == null);
    _ = bareSession;
    _ = probeBeforeSetup;
}
