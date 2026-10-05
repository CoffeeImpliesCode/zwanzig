// EXPECT: line=34 rule=optional-unwrap severity=warning
// EXPECT: line=39 rule=optional-unwrap severity=warning
// EXPECT: line=44 rule=optional-unwrap severity=warning
//
// A start phase proves its fields only for callers that reach them on the
// success path. An ignored startup error, a teardown that cleared the fields
// again and a pre-start call each defeat the proof, and none of them is
// repaired by the method name.
const std = @import("std");

const App = struct {
    band: ?u32 = null,

    fn start(self: *App) !void {
        errdefer self.abort();
        self.band = 1;
    }

    fn abort(self: *App) void {
        self.band = null;
    }

    fn teardown(self: *App) void {
        self.abort();
    }

    // Reached only by a caller whose start completed successfully.
    fn probeInstalled(self: *App) u32 {
        return self.band.?;
    }

    // Reached by a caller that tore the session down first.
    fn probeAfterTeardown(self: *App) u32 {
        return self.band.?;
    }

    // Reached by a caller that ignored the startup error and carried on.
    fn probeAfterIgnoredStartFailure(self: *App) u32 {
        return self.band.?;
    }

    // Reached by a caller that never ran a start at all.
    fn probeUnstarted(self: *App) u32 {
        return self.band.?;
    }

    fn runAfterSuccessfulStart(self: *App) !u32 {
        try self.start();
        return self.probeInstalled();
    }

    fn runAfterTeardown(self: *App) !u32 {
        try self.start();
        self.teardown();
        return self.probeAfterTeardown();
    }

    fn runAfterIgnoredStartFailure(self: *App) !u32 {
        self.start() catch {};
        return self.probeAfterIgnoredStartFailure();
    }

    fn runBeforeStart(self: *App) !u32 {
        return self.probeUnstarted();
    }
};

test "lifecycle controls: only the installed probe is read" {
    var app: App = .{};
    try app.start();
    try std.testing.expectEqual(@as(u32, 1), try app.runAfterSuccessfulStart());
    app.teardown();
}
