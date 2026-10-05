// EXPECT: none
//
// `self.reader = Reader.open(...) catch |err| return err;` stores whatever the
// operand produced whenever control reaches the code after the statement: the
// handler leaves the function, so it never supplies a stored value of its own
// and the stored value keeps the operand's nullability.
//
// The proof is about the statement's value, not its spelling: the handler is
// only peeled when it really leaves, and the operand's type decides the rest.
const Reader = struct {
    limit: usize = 0,

    fn open(source: []const u8, view: []const u32) !Reader {
        if (source.len == 0 or view.len == 0) return error.Empty;
        return .{ .limit = source.len };
    }

    fn reset(self: *Reader, source: []const u8, view: []const u32) !void {
        self.limit = source.len + view.len;
    }

    fn offset(self: *const Reader) usize {
        return self.limit;
    }
};

const Parser = struct {
    reader: ?Reader,

    fn validate(self: *Parser, source: []const u8, view: []const u32) !usize {
        var reader = if (self.reader) |*existing| blk: {
            existing.reset(source, view) catch |err| return err;
            break :blk existing;
        } else blk: {
            self.reader = Reader.open(source, view) catch |err| return err;
            break :blk &self.reader.?;
        };
        return reader.offset();
    }
};

test "a catch that leaves keeps the operand's value in the assigned field" {
    var parser = Parser{ .reader = null };
    _ = try parser.validate("payload", &.{ 1 });
    var warm = Parser{ .reader = Reader{} };
    _ = try warm.validate("again", &.{ 1, 2 });
}