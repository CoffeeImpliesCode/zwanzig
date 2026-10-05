// EXPECT: line=29 rule=optional-unwrap
// EXPECT: line=35 rule=optional-unwrap
// EXPECT: line=42 rule=optional-unwrap
// EXPECT: line=47 rule=optional-unwrap
// EXPECT: line=52 rule=optional-unwrap
//
// A write through a real alias still reaches the receiver, and an alias the
// receiver carries itself may point back at the very object the caller handed
// in, so a write through it clears what the guard established. A second pointer
// parameter tells the same story without any stored field: the caller may pass
// the receiver in twice, so `other.tag = null` writes the receiver's own bytes
// and the guard the body wrote proves nothing there. A guard on another field
// says nothing about `tag`, and an inverted null guard proves the opposite of
// what the code after it needs. Every receiver is the caller's own object rather
// than a copy: a copy owns storage of its own, which no caller can alias or
// write through.
const Flags = struct { first: bool = false, second: bool = false };

const Packet = struct {
    tag: ?u8,
    flags: Flags,
    peer: ?*Packet,
    seen: bool = false,

    pub fn matchesThroughAlias(self: *Packet, tag: u8) bool {
        const alias: *Packet = self;
        if (self.tag == null) return false;
        alias.tag = null;
        return tag == self.tag.?;
    }

    pub fn matchesAfterClearingAlias(self: *Packet, tag: u8, other: *Packet) bool {
        if (self.tag == null) return false;
        other.tag = null;
        return tag == self.tag.?;
    }

    pub fn matchesThroughStoredAlias(self: *Packet, tag: u8) bool {
        if (self.tag == null) return false;
        if (self.peer == null) return false;
        self.peer.?.tag = null;
        return tag == self.tag.?;
    }

    pub fn matchesInvertedGuard(self: *Packet, tag: u8) bool {
        if (self.tag != null) return false;
        return tag == self.tag.?;
    }

    pub fn matchesOtherField(self: *Packet, tag: u8) bool {
        if (self.flags.first) return false;
        return tag == self.tag.?;
    }

    // A second pointer parameter only carries as far as the field the write
    // spells. `Packet` lays `seen` and `tag` over bytes of their own, so
    // whichever object the caller handed in twice, `other.seen = true` never
    // touches the tag the guard established — while `other.tag = null` above
    // writes the very bytes the guard is about.
    pub fn matchesSiblingWriteThroughPointer(self: *Packet, tag: u8, other: *Packet) bool {
        if (self.tag == null) return false;
        other.seen = true;
        return tag == self.tag.?;
    }

    // The same through a field the receiver carries by value: replacing the
    // whole `flags` object writes every byte that object owns and none of
    // `tag`'s, and the path is still a single name below the parameter.
    pub fn matchesSiblingStructWriteThroughPointer(self: *Packet, tag: u8, other: *Packet) bool {
        if (self.tag == null) return false;
        other.flags = Flags{ .first = true, .second = false };
        return tag == self.tag.?;
    }
};
