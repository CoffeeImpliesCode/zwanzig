// EXPECT: line=26 rule=optional-unwrap severity=warning
//
// A caller's guard travels into a private method, and what that method does
// with a foreign parameter decides whether the guard survives. `driveAfterSink`
// stores a band into the module-level `session` before it calls
// `readAfterSink`, so the unwrap in there inherits `region` as non-null — until
// `sink.drop()` runs. A method on a foreign parameter reaches the very global
// the receiver points at and stores the null back over what the guard proved,
// so the unwrap after that call is a demonstrated null path.
//
// The other foreign parameter carries storage of its own and reaches none of
// the guarded bytes: `cache.clear()` writes `Cache.hits` and leaves the
// `session.region` its caller installed exactly where it was, so the unwrap it
// precedes is still proven and must keep its silence.
const std = @import("std");

const Band = struct {
    width: u16 = 80,
};

const Session = struct {
    region: ?Band = null,

    fn readAfterSink(self: *Session, sink: *Sink) u16 {
        sink.drop();
        return self.region.?.width;
    }

    fn readAfterCache(self: *Session, cache: *Cache) u16 {
        cache.clear();
        return self.region.?.width;
    }
};

const Sink = struct {
    marks: u8 = 0,

    fn drop(self: *Sink) void {
        self.marks = 0;
        session.region = null;
    }
};

const Cache = struct {
    hits: u32 = 0,

    fn clear(self: *Cache) void {
        self.hits = 0;
    }
};

var session: Session = .{};

fn driveAfterSink(sink: *Sink) u16 {
    session.region = .{ .width = 80 };
    return session.readAfterSink(sink);
}

fn driveAfterCache(cache: *Cache) u16 {
    session.region = .{ .width = 80 };
    return session.readAfterCache(cache);
}

test "a foreign method clears the global region the caller's guard proved" {
    var sink: Sink = .{};
    var cache: Cache = .{};

    session.region = .{ .width = 80 };
    sink.drop();
    try std.testing.expect(session.region == null);

    session.region = .{ .width = 80 };
    cache.clear();
    try std.testing.expect(session.region != null);

    _ = &driveAfterSink;
    _ = &driveAfterCache;
}
