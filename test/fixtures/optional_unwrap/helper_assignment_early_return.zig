// EXPECT: line=48 rule=optional-unwrap
// EXPECT: line=53 rule=optional-unwrap
//
// A helper the caller only reaches after a successful return has to leave
// the field non-null on every such exit, not merely on the one that stores
// it. Both `self.value = maybe() orelse return;` and
// `self.value = load() catch return;` return successfully without ever
// writing the field, so the caller's unwrap keeps its warning. A helper
// that always stores, and one whose early exit happens exactly while the
// field is installed already, both stay quiet.
const std = @import("std");

pub const State = struct {
    value: ?u32 = null,

    fn maybeValue() ?u32 {
        return null;
    }

    fn loadValue() error{Unavailable}!u32 {
        return error.Unavailable;
    }

    /// Stores a value when there is one and returns successfully without
    /// writing anything when there is not.
    fn maybeInitialize(self: *State) void {
        self.value = maybeValue() orelse return;
    }

    /// The same through an error union: the handler returns without storing.
    fn loadOrInitialize(self: *State) void {
        self.value = loadValue() catch return;
    }

    /// Always stores, so every successful exit carries the value.
    fn initialize(self: *State) void {
        self.value = 5;
    }

    /// The early exit happens exactly while the field is installed already.
    fn initializeUnlessReady(self: *State) void {
        if (self.value != null) return;
        self.value = 6;
    }

    pub fn readMaybeInitialized(self: *State) u32 {
        self.maybeInitialize();
        return self.value.?; // maybeInitialize returns without writing `value`
    }

    pub fn readLoadOrInitialized(self: *State) u32 {
        self.loadOrInitialize();
        return self.value.?; // loadOrInitialize returns without storing it
    }

    pub fn readInitialized(self: *State) u32 {
        self.initialize();
        return self.value.?; // initialize always stores
    }

    pub fn readUnlessReady(self: *State) u32 {
        self.initializeUnlessReady();
        return self.value.?; // initializeUnlessReady only returns while set
    }
};

test "the fallible helper skips an empty field and keeps an installed one" {
    var installed: State = .{};
    try std.testing.expectEqual(@as(u32, 5), installed.readInitialized());

    var guarded: State = .{};
    try std.testing.expectEqual(@as(u32, 6), guarded.readUnlessReady());

    var skipped: State = .{};
    skipped.loadOrInitialize();
    try std.testing.expectEqual(@as(?u32, null), skipped.value);

    var kept: State = .{ .value = 42 };
    try std.testing.expectEqual(@as(u32, 42), kept.readLoadOrInitialized());
    try std.testing.expectEqual(@as(?u32, 42), kept.value);
}
