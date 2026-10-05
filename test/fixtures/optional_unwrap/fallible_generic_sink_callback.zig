// EXPECT: none
//
// The unwrap is decided by the whole chain of calls that reach it, and every
// link of that chain is one this file contains. A fallible helper the caller
// `try`s fills the field on every success path, including the one that only
// fills a null — the other path is running precisely because the field was not
// null — so what follows the `try` sees a field that is there. A structure
// this file builds carries its owner into the field the generic parameter is
// handed, so the reducer behind `sink.append` reads the very same field on the
// very same object, and the callback the prototype leaves untyped is attributed
// to that reducer and not to the same-named method of the sink itself.
const std = @import("std");

const Owner = struct {
    index: ?u32 = null,

    // Fails before it installs anything, so the caller that `try`s it only ever
    // reaches what follows on the path where the field is filled.
    fn ensure(self: *Owner, fail: bool) error{Unavailable}!void {
        if (fail) return error.Unavailable;
        if (self.index == null) self.index = 0;
    }

    fn append(self: *Owner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *Owner, value: u8, fail: bool) !void {
        try self.ensure(fail);
        var sink: Sink = .{ .owner = self };
        scan(value, &sink);
    }
};

const Sink = struct {
    owner: *Owner,

    // The same name the owner's reducer carries, in a container of its own and
    // reached through a receiver of its own type.
    fn append(self: *Sink, value: u8) void {
        self.owner.append(value);
    }
};

/// The receiver's type is not written down here, so what `append` reaches is
/// decided by the object each visible call of this function passes.
fn scan(value: u8, sink: anytype) void {
    sink.append(value);
}

pub fn consume(value: u8, fail: bool) !?u32 {
    var owner: Owner = .{};
    try owner.process(value, fail);
    return owner.index;
}

// A teardown written after the call it follows runs after the reducer has read
// the field, so it outruns nothing. The two calls share one statement, and
// Zig evaluates its operands left to right: that order is what keeps the
// guard the chain proved above from being undone before the unwrap.
const TeardownOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *TeardownOwner) !void {
        if (self.index == null) self.index = 0;
    }

    fn teardown(self: *TeardownOwner) void {
        self.index = null;
    }

    fn add(self: *TeardownOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *TeardownOwner, value: u8) !void {
        try self.ensure();
        var sink: TeardownSink = .{ .owner = self };
        teardownScan(value, &sink);
    }
};

const TeardownSink = struct {
    owner: *TeardownOwner,

    /// Answers what the reducer left behind, so the pair the scan below writes
    /// is a pair of values and is read in the order it is written in.
    fn add(self: *TeardownSink, value: u8) ?u32 {
        self.owner.add(value);
        return self.owner.index;
    }

    fn teardown(self: *TeardownSink) ?u32 {
        self.owner.teardown();
        return self.owner.index;
    }
};

fn teardownScan(value: u8, sink: anytype) void {
    _ = .{ sink.add(value), sink.teardown() };
}

pub fn addThenTeardown(owner: *TeardownOwner, value: u8) !void {
    return owner.process(value);
}

test "the fallible helper dominates the generic sink unwrap" {
    try std.testing.expectEqual(@as(?u32, 9), try consume(9, false));
    try std.testing.expectError(error.Unavailable, consume(9, true));
}

test "a teardown written after the call it follows does not outrun it" {
    var owner: TeardownOwner = .{};
    try addThenTeardown(&owner, 9);
    // The reducer read a filled field and only then was the null put back.
    try std.testing.expectEqual(@as(?u32, null), owner.index);
}
