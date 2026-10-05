// EXPECT: line=35 rule=optional-unwrap severity=warning
// EXPECT: line=41 rule=optional-unwrap severity=warning
//
// One callback reached two ways — through `self.queue.?` and through a `*Queue`
// parameter — writes the same module-level `session`, so both unwraps warn.
const std = @import("std");

const Band = struct {
    width: u16 = 80,
};

/// Set by whatever asks the running phase to stop. It is false on every path
/// that reads the region, so this file is a reproducer and not a panicking
/// program; test two shows what the flag is there for.
var stop_requested: bool = false;

const Queue = struct {
    stops: u32 = 0,

    /// The reentry. The only name this file has for the object the receiver
    /// stands for is the module-level `session`.
    fn stopSession(self: *Queue) void {
        self.stops += 1;
        if (stop_requested) session.region = null;
    }
};

const Session = struct {
    region: ?Band = null,
    queue: ?Queue = null,

    /// Through the payload: the callback writes the global, not `queue`.
    fn readThroughPayload(self: *Session) u16 {
        self.queue.?.stopSession();
        return self.region.?.width;
    }

    /// The same callback, reached through a pointer parameter.
    fn readThroughSlot(self: *Session, q: *Queue) u16 {
        q.stopSession();
        return self.region.?.width;
    }
};

var session: Session = .{};

fn drivePayload() u16 {
    session.region = .{ .width = 80 };
    session.queue = Queue{};
    return session.readThroughPayload();
}

fn driveSlot(q: *Queue) u16 {
    session.region = .{ .width = 80 };
    session.queue = q.*;
    return session.readThroughSlot(q);
}

test "both readers report the width their caller installed" {
    var q: Queue = .{};
    stop_requested = false;
    try std.testing.expectEqual(@as(u16, 80), drivePayload());
    try std.testing.expectEqual(@as(u16, 80), driveSlot(&q));
}

test "the payload callback clears the module-level region once stop is requested" {
    var q: Queue = .{};
    session.region = .{ .width = 80 };
    stop_requested = true;
    q.stopSession();
    try std.testing.expect(session.region == null);
    stop_requested = false;
    session.region = .{ .width = 80 };
}
