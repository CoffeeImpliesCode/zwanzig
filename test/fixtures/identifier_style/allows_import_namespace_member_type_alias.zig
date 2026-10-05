// EXPECT: none
// #76: `Chord` and `Vertex` alias lowercase exported type members of a
// namespace declared by another file. That namespace is not resolved here, so
// the type-versus-value result of the member is unknown, and an unknown result
// is not turned into an asserted value classification: the alias keeps the
// PascalCase name its resolved type would require.
const kit = @import("detects_lowercase_type_members_of_import_namespace.zig").kit;

const Chord = kit.chord;

const Vertex = kit.vertex;

const Fret = u8;

const tuning: [6]u8 = .{ 40, 45, 50, 55, 59, 64 };

pub fn chordAt(fret: Fret) Chord {
    return .{ .string = 2, .fret = fret };
}

pub fn fretCount() usize {
    return tuning.len;
}

test "namespace member aliases name types" {
    const std = @import("std");
    const c = chordAt(3);
    try std.testing.expectEqual(@as(Fret, 3), c.fret);
    try std.testing.expectEqual(@as(usize, 6), fretCount());
}
