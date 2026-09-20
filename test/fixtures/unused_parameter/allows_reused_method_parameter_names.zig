// EXPECT: none
const Lexer = @This();

position: usize = 0,

pub fn eat(self: *Lexer, count: usize) void {
    for (0..count) |_| {
        self.position += 1;
    }
}

pub fn peekNextSkippingEscapedLines(self: *Lexer, count: usize) ?usize {
    if (count == 0) return self.position;

    var offset: usize = 0;
    for (0..count) |_| {
        offset += 1;
    }
    return self.position + offset - 1;
}

pub fn eatNextSkippingEscapedLines(self: *Lexer, count: usize) ?usize {
    if (count == 0) return null;

    for (0..count) |_| {
        self.position += 1;
    }
    return self.position;
}
