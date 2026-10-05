// EXPECT: line=52 rule=optional-unwrap
// EXPECT: line=68 rule=optional-unwrap
// EXPECT: line=84 rule=optional-unwrap
// EXPECT: line=101 rule=optional-unwrap
// EXPECT: line=119 rule=optional-unwrap
// EXPECT: line=137 rule=optional-unwrap
// EXPECT: line=154 rule=optional-unwrap
// EXPECT: line=171 rule=optional-unwrap
//
// Each filter below breaks exactly one link the retained-row proof needs, so
// the replayed lookup is no longer known to have succeeded. The last four
// break the links a `[]const` element cannot answer for: that type stops
// *this* function from writing a row's bytes through the buffer, not a second
// alias of the same backing from rewriting them anyway.
const std = @import("std");

/// Deterministic: the answer depends on nothing but the two arguments.
fn locate(text: []const u8, query: []const u8) ?usize {
    return std.mem.indexOf(u8, text, query);
}

/// Stateful: a counter decides nothing about the row, and the replay could see
/// a different answer than the filter did.
fn stateful(text: []const u8, query: []const u8) ?usize {
    attempts += 1;
    return std.mem.indexOf(u8, text, query);
}

var attempts: usize = 0;

/// The memory the rows below are carved out of.
var backing: [4]u8 = [_]u8{ 'a', 'b', 'a', 'b' };

/// No argument at all, and nothing the proof tracks is named, yet the bytes
/// every row points at change.
fn clobberBacking() void {
    backing[0] = 'z';
}

/// The filter's own shape, replayed through a stateful lookup: the second
/// answer is not the answer the filter saw.
fn statefulReplay(items: []const []const u8, query: []const u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = stateful(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += stateful(row, query).?;
    return sum;
}

/// The replay passes a query the filter never matched, so its lookup can miss.
fn otherQuery(items: []const []const u8, query: []const u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = locate(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    const other = "zz";
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += locate(row, other).?;
    return sum;
}

/// A row the filter never inspected is appended before the replay.
fn unvalidatedAppend(items: []const []const u8, query: []const u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = locate(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    if (items.len > 0) retained[0] = items[0];
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += locate(row, query).?;
    return sum;
}

/// The counter moves outside the validated pair, so `retained[0..count]` no
/// longer describes exactly the rows the filter kept.
fn strayCounterMove(items: []const []const u8, query: []const u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = locate(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    count += 2;
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += locate(row, query).?;
    return sum;
}

/// The caller keeps a mutable view of the row bytes and rewrites one of them
/// between the filter and the replay. `retained` holds a `[]const u8` view, and
/// the replay below really does read the rewritten bytes.
fn changedBacking(items: []const []const u8, query: []const u8, editor: []u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = locate(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    if (editor.len > 0) editor[0] = 'z';
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += locate(row, query).?;
    return sum;
}

/// The same write, this time into the bytes behind the query itself. The query
/// is a `[]const u8` view, and the view says nothing about who may write the
/// memory behind it.
fn changedQueryBytes(items: []const []const u8, query: []const u8, editor: []u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = locate(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    if (editor.len > 0) editor[0] = 'z';
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += locate(row, query).?;
    return sum;
}

/// The same write, reached only by dereferencing: no slice is ever named, so
/// the call site does not even mention a mutable view.
fn indirectAlias(items: []const []const u8, query: []const u8, editor: *[]u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = locate(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    if (editor.*.len > 0) editor.*[0] = 'z';
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += locate(row, query).?;
    return sum;
}

/// A no-argument helper rewrites the global the rows are carved out of between
/// the filter and the replay.
fn clobberedByHelper(items: []const []const u8, query: []const u8) usize {
    var retained: [8][]const u8 = undefined;
    var count: usize = 0;
    for (items) |item| {
        _ = locate(item, query) orelse continue;
        if (count == retained.len) break;
        retained[count] = item;
        count += 1;
    }
    clobberBacking();
    var sum: usize = 0;
    for (retained[0..count]) |row| sum += locate(row, query).?;
    return sum;
}

test "an alias rewrites the row bytes the replay then reads" {
    var bytes = [_]u8{ 'a', 'b' };
    const rows = [_][]const u8{bytes[0..2]};
    // The guard matches "b" in "ab"; the alias turns that same two-byte row into
    // "zb", and the replay still finds "b" there.
    try std.testing.expectEqual(@as(usize, 1), changedBacking(&rows, "b", bytes[0..2]));
    try std.testing.expectEqual(@as(u8, 'z'), bytes[0]);
}

test "an alias rewrites the bytes behind the query view" {
    var bytes = [_]u8{ 'b', 'b' };
    const rows = [_][]const u8{"ab"};
    try std.testing.expectEqual(@as(usize, 1), changedQueryBytes(&rows, bytes[0..1], bytes[1..2]));
    try std.testing.expectEqual(@as(u8, 'z'), bytes[1]);
}

test "the same write lands when it is only reached by dereferencing" {
    var bytes = [_]u8{ 'a', 'b' };
    var view: []u8 = bytes[0..2];
    const rows = [_][]const u8{bytes[0..2]};
    try std.testing.expectEqual(@as(usize, 1), indirectAlias(&rows, "b", &view));
    try std.testing.expectEqual(@as(u8, 'z'), bytes[0]);
}

test "a no-argument helper still rewrites the backing" {
    const rows = [_][]const u8{"ab"};
    try std.testing.expectEqual(@as(usize, 1), clobberedByHelper(&rows, "b"));
    try std.testing.expectEqual(@as(u8, 'z'), backing[0]);
}

test "a stateful lookup decides nothing about the replay" {
    const rows = [_][]const u8{"ab"};
    try std.testing.expectEqual(@as(usize, 1), statefulReplay(&rows, "b"));
    try std.testing.expectEqual(@as(usize, 2), attempts);
    // `otherQuery` replays with a query the filter never matched, so running it
    // would unwrap a null; it stays a control the analyzer has to reject.
    try std.testing.expectEqual(@as(usize, 1), unvalidatedAppend(&rows, "b"));
}
