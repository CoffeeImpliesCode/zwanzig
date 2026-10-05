// EXPECT: line=31 rule=unreachable-code-engine
// EXPECT: line=39 rule=unreachable-code-engine
// EXPECT: line=53 rule=unreachable-code-engine
// A compile-time capacity guard is an invariant check, not dead code. Its arm
// never runs because the invariant holds, and deleting it would remove the
// protection a future capacity change depends on. A user module spelled `std`
// names no assertion; that negative lives in comptime_assertion_guard_fake_std.
const std = @import("std");

pub const max_control_bytes: usize = 80;
pub const worst_case_bytes: usize = 77;
pub const feature_flags: u8 = 0;

comptime {
    const guard_limit: usize = 80;
    const guard_worst_case: usize = 77;
    if (guard_worst_case > guard_limit) {
        @compileError("max_control_bytes must hold the worst-case control sequence");
    }
}

comptime {
    if (feature_flags == 2) {
        std.debug.assert(worst_case_bytes == max_control_bytes);
    }
}

// A comptime branch that runs application logic is still dead code.
comptime {
    const dead_flag: bool = false;
    if (dead_flag) {
        std.debug.print("unreachable feature\n", .{});
    }
}

/// An assertion outside a comptime scope is dead code like any other.
pub fn scale(value: u8) u8 {
    const unsupported: bool = false;
    if (unsupported) {
        @compileError("an assertion outside comptime is dead code");
    }
    return value;
}

/// A `var` alias of the assertion can be rebound before the call, so its
/// spelling proves nothing even while it names the real assertion.
pub fn mutableAssertAlias(value: u8) u8 {
    var assert = std.debug.assert;
    defer assert = std.debug.assert;
    comptime {
        const limit: usize = 80;
        const worst: usize = 77;
        if (worst > limit) {
            assert(worst <= limit);
        }
    }
    return value;
}

test "capacity invariant holds" {
    try std.testing.expect(worst_case_bytes <= max_control_bytes);
    try std.testing.expectEqual(@as(u8, 7), digitValue('7').?);
    try std.testing.expect(digitValue('x') == null);
    try std.testing.expectEqual(@as(u8, 21), scale(21));
}

pub fn digitValue(byte: u8) ?u8 {
    if (byte >= '0' and byte <= '9') return byte - '0';
    return null;
}
