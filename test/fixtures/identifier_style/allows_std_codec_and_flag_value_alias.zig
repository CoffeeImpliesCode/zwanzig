// EXPECT: none
// #79: `std.base64.standard` is a `Codecs` value, so its `Encoder` and `Decoder`
// members hold initialized codec instances and a snake_case binding of one is
// correct. Capitalization of a library member does not make it a type, and an
// uppercase packed-struct flag is a bool field rather than a type.
const std = @import("std");

pub fn decodePayload(payload: []const u8, out: []u8) !usize {
    const decoder = std.base64.standard.Decoder;
    const size = try decoder.calcSizeForSlice(payload);
    if (size > out.len) return error.NoSpaceLeft;
    try decoder.decode(out[0..size], payload);
    return size;
}

pub fn encodePayload(raw: []const u8, out: []u8) []const u8 {
    const encoder = std.base64.standard.Encoder;
    const size = encoder.calcSize(raw.len);
    return encoder.encode(out[0..size], raw);
}

pub const OpenMode = packed struct {
    NONBLOCK: bool = false,
    RDONLY: bool = true,
};

pub fn wantsNonBlocking(flags: OpenMode) bool {
    const nonblocking = flags.NONBLOCK;
    return nonblocking;
}

test "codec and flag bindings stay values" {
    var buf: [16]u8 = undefined;
    const encoded = encodePayload("hi", &buf);
    try std.testing.expectEqual(@as(usize, 4), encoded.len);
    const decoded = try decodePayload(encoded, &buf);
    try std.testing.expectEqualStrings("hi", buf[0..decoded]);
    try std.testing.expect(wantsNonBlocking(.{ .NONBLOCK = true }));
    try std.testing.expect(!wantsNonBlocking(.{}));
}
