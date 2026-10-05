// EXPECT: line=45 rule=optional-unwrap
// EXPECT: line=52 rule=optional-unwrap
// EXPECT: line=58 rule=optional-unwrap
// EXPECT: line=67 rule=optional-unwrap
//
// Each case below keeps a producer and a whitelist but breaks the link between
// them: a different error value, a whitelist that accepts a tag the producer
// leaves null, no guard at all, or a payload handed to a call that could
// rewrite it. None of them may be treated as proved.
const std = @import("std");

const ParseError = error{ BadEscape, UnexpectedEnd, OutOfMemory };
const Info = struct { position: ?usize };

fn diagnostic(err: ParseError) Info {
    return .{ .position = switch (err) {
        error.BadEscape, error.UnexpectedEnd => 6,
        error.OutOfMemory => null,
    } };
}

fn isPositioned(err: ParseError) bool {
    return switch (err) {
        error.BadEscape, error.UnexpectedEnd => true,
        error.OutOfMemory => false,
    };
}

/// The whitelist accepts every tag, including the allocation failure the
/// producer leaves null.
fn acceptsAny(err: ParseError) bool {
    return switch (err) {
        error.BadEscape, error.UnexpectedEnd, error.OutOfMemory => true,
    };
}

fn consume(value: Info) void {
    _ = value;
}

/// The producer partitioned a different error value than the guard checked.
pub fn mismatched(reported: ParseError) usize {
    const info = diagnostic(error.OutOfMemory);
    if (!isPositioned(reported)) return 0;
    return info.position.?;
}

/// The whitelist is unrelated: it also accepts `OutOfMemory`.
pub fn unrelated(err: ParseError) usize {
    const info = diagnostic(err);
    if (!acceptsAny(err)) return 0;
    return info.position.?;
}

/// No guard at all: the allocation-failure tag still reaches the unwrap.
pub fn unguarded(err: ParseError) usize {
    const info = diagnostic(err);
    return info.position.?;
}

/// The payload leaves for a call before the unwrap, so its partition no longer
/// describes what the unwrap reads.
pub fn escaped(err: ParseError) usize {
    const info = diagnostic(err);
    if (!isPositioned(err)) return 0;
    consume(info);
    return info.position.?;
}

test "a proved partition returns its payload; a mismatched one stops first" {
    // The guard is the only thing between `mismatched` and its unwrap, and the
    // one error it accepts is the one the producer left unfilled, so the
    // mismatched case never reaches the optional it cannot answer.
    try std.testing.expectEqual(@as(usize, 0), mismatched(error.OutOfMemory));
    try std.testing.expectEqual(@as(usize, 6), unrelated(error.BadEscape));
}
