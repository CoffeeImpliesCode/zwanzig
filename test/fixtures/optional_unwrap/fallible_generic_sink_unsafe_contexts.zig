// EXPECT: line=37 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=70 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=106 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=141 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=175 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=207 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=240 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=285 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
//
// A context this file cannot read is a context the proof cannot be read
// through. Twelve chains below each hand the same private reducer the same
// established field, and each one breaks in exactly one way: a callback code
// outside this file may call, a callback address that leaves this file, a
// generic context that reaches itself, a context field replaced after the
// structure was built, an installer failure that was swallowed, a reset
// between the installation and the call, a receiver the callback mutates
// before it uses it, a mutation written into the argument of the guarded
// call, a mutation written ahead of the unwrap in the same statement, an
// installer whose deferred write only sometimes runs, a helper that reaches
// the owner through the sink it was handed, and a bare parameter written
// ahead of the typed one. Every one of them keeps the warning, and every one
// of them really runs.

const std = @import("std");

// --- 1: a generic callback another file may call ----------------------------

const PublicOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *PublicOwner, fail: bool) error{Unavailable}!void {
        if (fail) return error.Unavailable;
        if (self.index == null) self.index = 0;
    }

    fn append(self: *PublicOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *PublicOwner, value: u8, fail: bool) !void {
        try self.ensure(fail);
        var sink: PublicSink = .{ .owner = self };
        publicScan(value, &sink);
    }
};

const PublicSink = struct {
    owner: *PublicOwner,

    fn append(self: *PublicSink, value: u8) void {
        self.owner.append(value);
    }
};

/// The instantiation this file cannot see is a context the proof never reads.
pub fn publicScan(value: u8, sink: anytype) void {
    sink.append(value);
}

// --- 2: a callback whose address leaves this file --------------------------

const BoundOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *BoundOwner) !void {
        if (self.index == null) self.index = 0;
    }

    fn push(self: *BoundOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *BoundOwner, value: u8) !void {
        try self.ensure();
        var sink: BoundSink = .{ .owner = self };
        hold(&sink, value);
    }
};

const BoundSink = struct {
    owner: *BoundOwner,

    fn push(self: *BoundSink, value: u8) void {
        self.owner.push(value);
    }
};

/// The address below is the method with its receiver still in its signature,
/// so whoever holds it can pass a sink built around any owner at all.
fn hold(sink: *BoundSink, value: u8) void {
    const callback: *const fn (*BoundSink, u8) void = &BoundSink.push;
    _ = callback;
    sink.push(value);
}

// --- 3: a generic context that reaches itself --------------------------------

const DepthOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *DepthOwner) !void {
        if (self.index == null) self.index = 0;
    }

    fn emit(self: *DepthOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *DepthOwner, value: u8) !void {
        try self.ensure();
        var sink: DepthSink = .{ .owner = self };
        recurse(value, &sink, 1);
    }
};

const DepthSink = struct {
    owner: *DepthOwner,

    fn emit(self: *DepthSink, value: u8) void {
        self.owner.emit(value);
    }
};

/// The recursive call passes the untyped parameter straight back, so it names
/// an object no declaration in this file describes.
fn recurse(value: u8, sink: anytype, depth: u8) void {
    sink.emit(value);
    if (depth > 0) recurse(value, sink, depth - 1);
}

// --- 4: a context field replaced after the structure was built --------------

const TwinOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *TwinOwner) !void {
        if (self.index == null) self.index = 0;
    }

    fn store(self: *TwinOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *TwinOwner, value: u8, other: *TwinOwner) !void {
        try self.ensure();
        var sink: TwinSink = .{ .owner = self };
        sink.owner = other;
        twinScan(value, &sink);
    }
};

const TwinSink = struct {
    owner: *TwinOwner,

    fn store(self: *TwinSink, value: u8) void {
        self.owner.store(value);
    }
};

fn twinScan(value: u8, sink: anytype) void {
    sink.store(value);
}

// --- 5: a swallowed installer failure ----------------------------------------

const LenientOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *LenientOwner, fail: bool) error{Unavailable}!void {
        if (fail) return error.Unavailable;
        if (self.index == null) self.index = 0;
    }

    fn record(self: *LenientOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *LenientOwner, value: u8, fail: bool) void {
        _ = self.ensure(fail) catch {};
        var sink: LenientSink = .{ .owner = self };
        lenientScan(value, &sink);
    }
};

const LenientSink = struct {
    owner: *LenientOwner,

    fn record(self: *LenientSink, value: u8) void {
        self.owner.record(value);
    }
};

fn lenientScan(value: u8, sink: anytype) void {
    sink.record(value);
}

// --- 6: a reset between the installation and the call -----------------------

const ClearedOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *ClearedOwner) !void {
        if (self.index == null) self.index = 0;
    }

    fn bump(self: *ClearedOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *ClearedOwner, value: u8, reset: bool) !void {
        try self.ensure();
        if (reset) self.index = null;
        var sink: ClearedSink = .{ .owner = self };
        clearedScan(value, &sink);
    }
};

const ClearedSink = struct {
    owner: *ClearedOwner,

    fn bump(self: *ClearedSink, value: u8) void {
        self.owner.bump(value);
    }
};

fn clearedScan(value: u8, sink: anytype) void {
    sink.bump(value);
}

// --- 7: a receiver the callback mutates before it uses it -------------------

const TallyOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *TallyOwner) !void {
        if (self.index == null) self.index = 0;
    }

    fn count(self: *TallyOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *TallyOwner, value: u8, wipe: bool) !void {
        try self.ensure();
        var sink: TallySink = .{ .owner = self };
        tallyScan(value, &sink, wipe);
    }
};

const TallySink = struct {
    owner: *TallyOwner,

    /// Clears the very field the caller installed, which is what the callback
    /// below walks straight into.
    fn clear(self: *TallySink, wipe: bool) void {
        if (wipe) self.owner.index = null;
    }

    fn count(self: *TallySink, value: u8) void {
        self.owner.count(value);
    }
};

fn tallyScan(value: u8, sink: anytype, wipe: bool) void {
    sink.clear(wipe);
    sink.count(value);
}

// --- 8: a mutation written into the argument of the guarded call -------

const WipingOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *WipingOwner) !void {
        if (self.index == null) self.index = 0;
    }

    /// Clears the field, and answers the argument it is written into.
    fn wipe(self: *WipingOwner) u8 {
        self.index = null;
        return 0;
    }

    fn add(self: *WipingOwner, value: u8) void {
        self.index.? += value;
    }

    /// The guard holds where it is written and is outrun inside the very
    /// statement it guards: Zig evaluates the argument before it enters the
    /// call, so the null `wipe` puts back is what `add` reaches.
    fn process(self: *WipingOwner, value: u8) !void {
        try self.ensure();
        self.add(self.wipe() +% value);
    }
};

/// The one caller of `add` this file contains.
pub fn wipeThenAdd(owner: *WipingOwner, value: u8) !void {
    return owner.process(value);
}

// --- 9: a mutation written ahead of the unwrap in the same statement ----

const PairOwner = struct {
    index: ?u32 = null,

    fn install(self: *PairOwner) void {
        self.index = 0;
    }

    /// Clears the field, and answers the element it is written beside.
    fn clear(self: *PairOwner) u32 {
        self.index = null;
        return 0;
    }

    /// The guard is the statement before, and the element beside the unwrap
    /// runs first: Zig evaluates a tuple's elements left to right, so the
    /// null `clear` puts back is what the `.?` reaches.
    fn readPair(self: *PairOwner) [2]u32 {
        if (self.index == null) return .{ 0, 0 };
        return .{ self.clear(), self.index.? };
    }
};

/// The one caller of `readPair` this file contains.
pub fn pairRead(owner: *PairOwner) [2]u32 {
    return owner.readPair();
}

// --- 10: an installer whose deferred write only sometimes runs ----------

const DeferredOwner = struct {
    index: ?u32 = null,

    /// The write that reads like an installation runs only when the flag says
    /// so, so a caller that lets the scope end cannot count on it.
    fn ensure(self: *DeferredOwner, ready: bool) !void {
        defer if (ready) {
            self.index = 0;
        };
    }

    fn add(self: *DeferredOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *DeferredOwner, value: u8, ready: bool) !void {
        try self.ensure(ready);
        var sink: DeferredSink = .{ .owner = self };
        deferredScan(value, &sink);
    }
};

const DeferredSink = struct {
    owner: *DeferredOwner,

    fn add(self: *DeferredSink, value: u8) void {
        self.owner.add(value);
    }
};

/// The receiver's type is not written down here, so what `add` reaches is
/// decided by the object this file hands it.
fn deferredScan(value: u8, sink: anytype) void {
    sink.add(value);
}

/// The one caller of `process` this file contains.
pub fn deferredAdd(owner: *DeferredOwner, value: u8, ready: bool) !void {
    return owner.process(value, ready);
}

// --- 11: a helper that reaches the owner through the sink it was handed ------

const DrivenOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *DrivenOwner) !void {
        if (self.index == null) self.index = 0;
    }

    /// Clears the field the caller's installer filled.
    fn reset(self: *DrivenOwner) void {
        self.index = null;
    }

    fn add(self: *DrivenOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *DrivenOwner, value: u8) !void {
        try self.ensure();
        var sink: DrivenSink = .{ .owner = self };
        drive(&sink);
        drivenScan(value, &sink);
    }
};

const DrivenSink = struct {
    owner: *DrivenOwner,

    fn add(self: *DrivenSink, value: u8) void {
        self.owner.add(value);
    }

    /// Reaches the owner through the field this structure carries, so the
    /// generic call below hands a reducer that the helper has already walked
    /// into.
    fn drive(self: *DrivenSink, value: u8) void {
        self.owner.add(value);
    }
};

/// The sink is handed over as an argument and the owner is written through a
/// field of it, so this call passes no storage of its own and only the
/// receiver says what the callee may write.
fn drive(target: *DrivenSink) void {
    target.owner.reset();
}

/// The receiver's type is not written down here, so what `drive` reaches is
/// decided by the object this file hands it.
fn drivenScan(value: u8, sink: anytype) void {
    sink.drive(value);
}

/// The one caller of `process` this file contains.
pub fn drivenAdd(owner: *DrivenOwner, value: u8) !void {
    return owner.process(value);
}

// --- 12: a bare parameter written ahead of the typed one --------------------

const RelayedOwner = struct {
    index: ?u32 = null,

    fn ensure(self: *RelayedOwner) !void {
        if (self.index == null) self.index = 0;
    }

    fn add(self: *RelayedOwner, value: u8) void {
        self.index.? += value;
    }

    fn process(self: *RelayedOwner, value: u8) !void {
        try self.ensure();
        var sink: RelayedSink = .{ .owner = self };
        relay(0, &sink, true);
        relayedScan(value, &sink);
    }
};

const RelayedSink = struct {
    owner: *RelayedOwner,

    fn add(self: *RelayedSink, value: u8) void {
        self.owner.add(value);
    }
};

/// The second of these three arguments names the typed parameter, and the
/// prototype's own list holds that parameter first: the arguments are not
/// the list, so a reader that takes the argument's position for its place in
/// the list reaches `mode` and leaves the sink rewritten by nothing.
fn relay(tag: anytype, target: *RelayedSink, mode: anytype) void {
    _ = tag;
    _ = mode;
    target.owner.index = null;
}

fn relayedScan(value: u8, sink: anytype) void {
    sink.add(value);
}

/// The one caller of `process` this file contains.
pub fn relayedAdd(owner: *RelayedOwner, value: u8) !void {
    return owner.process(value);
}

// Each unwrap above is reached with a null in place: the first seven through a
// context this file cannot read, the next three through an operand the language
// evaluates first or an installation that only sometimes runs, and the last two
// because a helper this file does contain cleared the field on the way there.
// EXPECT: line=322 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=345 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=389 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime
// EXPECT: line=443 rule=optional-unwrap severity=warning message=forced optional unwrap can panic at runtime

test "every context that cannot be read keeps its forced unwrap" {
    var public_owner: PublicOwner = .{};
    try public_owner.process(3, false);

    var bound: BoundOwner = .{};
    try bound.process(3);

    // The recursive context delivers the value twice: the callback hands the
    // sink straight back to itself.
    var depth: DepthOwner = .{};
    try depth.process(3);

    var lenient: LenientOwner = .{};
    lenient.process(3, false);

    var cleared: ClearedOwner = .{};
    try cleared.process(3, false);

    var tally: TallyOwner = .{};
    try tally.process(3, false);

    // The context field is rebound to another owner before the reducer is
    // reached, so the write lands on that owner and leaves the one that ran the
    // installer with the value the installer gave it.
    var twin: TwinOwner = .{};
    var other: TwinOwner = .{ .index = 0 };
    try twin.process(3, &other);

    // The last two chains reach the reducer through a helper that writes
    // through a field of the sink it was handed, which is what puts the null
    // back. Reading the reducer is the panic itself, so what this drives is the
    // helper: it leaves the field null however the installer went.
    var driven: DrivenOwner = .{};
    try driven.ensure();
    var driven_sink: DrivenSink = .{ .owner = &driven };
    drive(&driven_sink);

    var relayed: RelayedOwner = .{};
    try relayed.ensure();
    var relayed_sink: RelayedSink = .{ .owner = &relayed };
    relay(0, &relayed_sink, true);

    try std.testing.expectEqual(@as(?u32, 3), public_owner.index);
    try std.testing.expectEqual(@as(?u32, 3), bound.index);
    try std.testing.expectEqual(@as(?u32, 6), depth.index);
    try std.testing.expectEqual(@as(?u32, 3), lenient.index);
    try std.testing.expectEqual(@as(?u32, 3), cleared.index);
    try std.testing.expectEqual(@as(?u32, 3), tally.index);
    try std.testing.expectEqual(@as(?u32, 0), twin.index);
    try std.testing.expectEqual(@as(?u32, 3), other.index);
    try std.testing.expectEqual(@as(?u32, null), driven.index);
    try std.testing.expectEqual(@as(?u32, null), relayed.index);
}

test "an operand the statement evaluates first is the null the unwrap reaches" {
    // The argument of `self.add(self.wipe() +% value)` runs before `add` is
    // entered, so the field the guard installed is already null when the
    // callee reads it.
    var wiping: WipingOwner = .{};
    try wiping.ensure();
    try std.testing.expectEqual(@as(?u32, 0), wiping.index);
    try std.testing.expectEqual(@as(u8, 0), wiping.wipe());
    try std.testing.expectEqual(@as(?u32, null), wiping.index);

    // The first element of the tuple `readPair` returns runs before the `.?`
    // beside it, for the same reason.
    var pair: PairOwner = .{};
    pair.install();
    try std.testing.expectEqual(@as(?u32, 0), pair.index);
    try std.testing.expectEqual(@as(u32, 0), pair.clear());
    try std.testing.expectEqual(@as(?u32, null), pair.index);

    // A deferred write under a flag leaves the field null when the flag says
    // so, which is the whole of what the caller may count on.
    var deferred: DeferredOwner = .{};
    try deferred.ensure(false);
    try std.testing.expectEqual(@as(?u32, null), deferred.index);

    // The same installer with the flag set is the one that really fills the
    // field, so the chain it opens does not panic.
    try deferredAdd(&deferred, 9, true);
    try std.testing.expectEqual(@as(?u32, 9), deferred.index);
}
