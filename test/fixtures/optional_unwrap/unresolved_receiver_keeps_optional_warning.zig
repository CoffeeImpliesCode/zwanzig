// EXPECT: line=19 rule=optional-unwrap severity=warning
// EXPECT: line=37 rule=optional-unwrap severity=warning
//
// A name alone never settles which declaration a call reaches, so a receiver
// this file cannot type defeats the proof even where every call it can read
// establishes the field: that one call may still be this method, from a caller
// the scan never sees. A method reference asks the same question of its
// receiver, and one nothing here can type stops the proof exactly as a
// reference the file can place in another container does not.
const std = @import("std");

const Owner = struct {
    field: ?u32 = null,
    spare: ?u32 = null,

    // Every call this file can read establishes the field; the one it cannot
    // read names a receiver no declaration in this file describes.
    fn read(self: *Owner) u32 {
        return self.field.?;
    }

    fn drive(self: *Owner) void {
        if (self.field != null) {
            _ = self.read();
        }
    }

    fn driveUntyped(self: *Owner, other: anytype) void {
        if (self.field != null) {
            _ = other.read();
        }
    }

    // Its one reachable caller establishes the field, but a reference handed to
    // a receiver this file cannot type can still be called from outside it.
    fn readSpare(self: *Owner) u32 {
        return self.spare.?;
    }

    fn driveSpare(self: *Owner) void {
        if (self.spare != null) {
            _ = self.readSpare();
        }
    }

    fn publish(other: anytype) void {
        const alias = other.readSpare;
        _ = alias;
    }
};

test "unresolved receivers and references keep both warnings" {
    var owner: Owner = .{ .field = 1, .spare = 2 };
    owner.drive();
    owner.driveSpare();

    try std.testing.expectEqual(@as(u32, 1), owner.read());
    try std.testing.expectEqual(@as(u32, 2), owner.readSpare());
}
