// EXPECT: line=31 rule=optional-unwrap
//
// A row is appended to a function-local buffer only after the *same* lookup
// call on the *same* query succeeded for those bytes, and the replay runs that
// call again over the retained prefix. The proof comes from the store, the
// counter, and the immutable row type, never from the loop itself.
const std = @import("std");

/// Deterministic: the answer depends on nothing but the two arguments.
fn locate(text: []const u8, query: []const u8) ?usize {
    return std.mem.indexOf(u8, text, query);
}

pub fn sumPositions(items: []const []const u8, query: []const u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = locate(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += locate(row, query).?;
    return sum;
}

/// No filter ran here, so a caller-supplied row can be anything at all. A
/// public function is not assumed to receive validated rows.
pub fn unchecked(row: []const u8, query: []const u8) usize {
    return locate(row, query).?;
}

test "the filter retains only matches for the unchanged query" {
    const items = [_][]const u8{ "no", "ab", "xxab", "absent", "zab" };
    try std.testing.expectEqual(@as(usize, 3), sumPositions(&items, "ab"));
    try std.testing.expectEqual(@as(usize, 0), sumPositions(&items, "missing"));
}
