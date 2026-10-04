// EXPECT: none
//
// `init` asserts the fill is non-null exactly when the comptime `pad`
// parameter says a padded tail lane will exist, and `next` unwraps it only
// on the iteration where that parameter holds. The proof comes from the
// stored value and that parameter, never from the constructor's name.
const std = @import("std");

fn ChunkIterator(comptime T: type, comptime pad: bool) type {
    return struct {
        const Self = @This();

        /// `null` only when `pad` is `false`, where no lane is ever padded.
        fill: ?T,
        rest: []const T,

        pub fn init(data: []const T, fill: ?T) Self {
            if (pad) {
                std.debug.assert(fill != null);
            }
            return .{
                .fill = fill,
                .rest = data,
            };
        }

        pub fn next(self: *Self) ?T {
            if (self.rest.len == 0 or !pad) return null;
            self.rest = self.rest[1..];
            return self.fill.?;
        }
    };
}

fn windows(comptime T: type, comptime pad: bool, data: []const T, fill: ?T) usize {
    var it = ChunkIterator(T, pad).init(data, fill);
    var total: usize = 0;
    while (it.next()) |_| total += 1;
    return total;
}

test "private padded construction preserves its non-null field" {
    try std.testing.expectEqual(@as(usize, 4), windows(u8, true, "abcd", 'z'));
    try std.testing.expectEqual(@as(usize, 0), windows(u8, false, "abcd", null));
}