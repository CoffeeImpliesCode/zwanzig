// EXPECT: line=17 rule=optional-unwrap severity=warning
// EXPECT: line=30 rule=optional-unwrap severity=warning
//
// Caller guards do not transfer: a caller that establishes nothing, and a
// caller that establishes a sibling field instead, both leave the helper's own
// forced unwrap as a demonstrated null path.
const std = @import("std");

const Band = struct {
    width: u16 = 80,
};

const UnguardedCaller = struct {
    field: ?Band = null,

    fn readWidth(self: *UnguardedCaller) u16 {
        return self.field.?.width;
    }

    fn run(self: *UnguardedCaller) u16 {
        return self.readWidth();
    }
};

const SiblingGuardCaller = struct {
    guarded: ?Band = null,
    field: ?Band = null,

    fn readWidth(self: *SiblingGuardCaller) u16 {
        return self.field.?.width;
    }

    fn run(self: *SiblingGuardCaller) u16 {
        if (self.guarded != null) {
            return self.readWidth();
        }
        return 0;
    }
};

// Entry points a caller outside this file reaches. The owner arrives as a bare
// pointer with nothing said about its optional field, so these callers neither
// establish `field` nor establish a sibling of it.
pub fn exerciseUnguarded(owner: *UnguardedCaller) u16 {
    return owner.run();
}

pub fn exerciseSiblingGuard(owner: *SiblingGuardCaller) u16 {
    return owner.run();
}

test "caller guards: the unguarded and mismatched helpers still warn" {
    var unguarded: UnguardedCaller = .{ .field = Band{} };
    var sibling: SiblingGuardCaller = .{ .guarded = Band{}, .field = Band{} };
    try std.testing.expectEqual(@as(u16, 80), unguarded.run());
    try std.testing.expectEqual(@as(u16, 80), sibling.run());
    try std.testing.expectEqual(@as(u16, 80), exerciseUnguarded(&unguarded));
    try std.testing.expectEqual(@as(u16, 80), exerciseSiblingGuard(&sibling));
}
