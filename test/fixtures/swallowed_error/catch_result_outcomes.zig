// EXPECT: none
// Reducer for a catch handler that rejects through the function's own result.
// The boolean rejection and the returned failure count are observable at the
// caller; the rethrow, the log, and the empty discard keep their own paths.
const std = @import("std");

pub const Sanitizer = struct {
    last: []const u8 = "",

    pub fn acceptCluster(self: *Sanitizer, cluster: []const u8) bool {
        var accepted = true;
        var i: usize = 0;
        while (i < cluster.len) {
            const len: usize = std.unicode.utf8ByteSequenceLength(cluster[i]) catch {
                accepted = false;
                break;
            };
            if (len > cluster.len - i) {
                accepted = false;
                break;
            }
            i += len;
        }
        self.last = cluster;
        return accepted;
    }
};

fn mayFail(byte: u8) error{ PermissionDenied, BadByte }!u8 {
    _ = byte;
    return error.BadByte;
}

pub fn rethrown(byte: u8) error{ PermissionDenied, BadByte }!u8 {
    return mayFail(byte) catch |err| return err;
}

pub fn logged(byte: u8) u8 {
    return mayFail(byte) catch |err| blk: {
        std.log.err("cluster rejected: {any}", .{err});
        break :blk 0;
    };
}

pub fn discarded(byte: u8) void {
    _ = mayFail(byte) catch {};
}

pub fn tallied(byte: u8) u8 {
    var rejected: u8 = 0;
    _ = mayFail(byte) catch {
        rejected += 1;
    };
    return rejected;
}
