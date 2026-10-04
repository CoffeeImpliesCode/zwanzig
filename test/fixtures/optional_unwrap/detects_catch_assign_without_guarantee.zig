// EXPECT: line=33 rule=optional-unwrap
// EXPECT: line=44 rule=optional-unwrap
// EXPECT: line=50 rule=optional-unwrap
// EXPECT: line=57 rule=optional-unwrap
//
// A `catch`/`try` wrapper never makes the stored value non-null on its own:
// the operand's own nullability decides, a handler that keeps running
// supplies the stored value instead, and a later write still clears the fact.
const Reader = struct {
    limit: usize = 0,

    fn open(source: []const u8) !Reader {
        if (source.len == 0) return error.Empty;
        return .{ .limit = source.len };
    }

    fn maybeOpen(source: []const u8) !?Reader {
        if (source.len == 0) return null;
        return try open(source);
    }

    fn offset(self: *const Reader) usize {
        return self.limit;
    }
};

const Parser = struct {
    reader: ?Reader,
    last_error: anyerror = error.Empty,

    fn optionalOperand(self: *Parser, source: []const u8) !usize {
        self.reader = Reader.maybeOpen(source) catch |err| return err;
        const reader = &self.reader.?;
        return reader.offset();
    }

    fn handlerKeepsRunning(self: *Parser, source: []const u8) !usize {
        self.reader = Reader.open(source) catch |err| blk: {
            self.last_error = err;
            // The handler supplies the value the assignment stores, and this
            // one is optional.
            break :blk Reader.maybeOpen(source) catch |other| return other;
        };
        const reader = &self.reader.?;
        return reader.offset();
    }

    fn tryKeepsOptionality(self: *Parser, source: []const u8) !usize {
        self.reader = try Reader.maybeOpen(source);
        const reader = &self.reader.?;
        return reader.offset();
    }

    fn clearedAfterAssign(self: *Parser, source: []const u8) !usize {
        self.reader = try Reader.open(source);
        self.reader = null;
        const reader = &self.reader.?;
        return reader.offset();
    }
};