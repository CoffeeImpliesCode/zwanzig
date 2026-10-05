const std = @import("std");

const SuppressionError = error{
    OutOfMemory,
};

const LineRange = struct {
    start: usize,
    end: ?usize,
};

pub const SuppressionMap = struct {
    allocator: std.mem.Allocator,
    all_rules_suppressed_lines: std.AutoHashMap(usize, void),
    rule_specific_lines: std.StringHashMap(std.AutoHashMap(usize, void)),
    file_scope_ranges: std.StringHashMap(std.ArrayList(LineRange)),
    all_rules_file_scope_ranges: std.ArrayList(LineRange),

    pub fn init(allocator: std.mem.Allocator) SuppressionMap {
        return .{
            .allocator = allocator,
            .all_rules_suppressed_lines = std.AutoHashMap(usize, void).init(allocator),
            .rule_specific_lines = std.StringHashMap(std.AutoHashMap(usize, void)).init(allocator),
            .file_scope_ranges = std.StringHashMap(std.ArrayList(LineRange)).init(allocator),
            .all_rules_file_scope_ranges = .empty,
        };
    }

    pub fn deinit(self: *SuppressionMap) void {
        self.all_rules_suppressed_lines.deinit();
        var line_iter = self.rule_specific_lines.valueIterator();
        while (line_iter.next()) |line_set| {
            line_set.deinit();
        }
        self.rule_specific_lines.deinit();
        var range_iter = self.file_scope_ranges.valueIterator();
        while (range_iter.next()) |ranges| {
            ranges.deinit(self.allocator);
        }
        self.file_scope_ranges.deinit();
        self.all_rules_file_scope_ranges.deinit(self.allocator);
    }

    pub fn isSuppressed(self: *const SuppressionMap, line: usize, rule_id: []const u8) bool {
        if (self.all_rules_suppressed_lines.contains(line)) {
            return true;
        }

        if (self.rule_specific_lines.get(rule_id)) |lines_set| {
            if (lines_set.contains(line)) {
                return true;
            }
        }

        for (self.all_rules_file_scope_ranges.items) |range| {
            if (isLineInRange(line, range)) {
                return true;
            }
        }

        if (self.file_scope_ranges.get(rule_id)) |ranges| {
            for (ranges.items) |range| {
                if (isLineInRange(line, range)) {
                    return true;
                }
            }
        }

        return false;
    }

    fn isLineInRange(line: usize, range: LineRange) bool {
        if (line < range.start) return false;
        if (range.end) |end| {
            return line < end;
        }
        return true;
    }
};

const DirectiveKind = enum {
    next_line,
    file_scope,
    enable,
};

const DirectiveInfo = struct {
    prefix: []const u8,
    kind: DirectiveKind,
};

const directives = [_]DirectiveInfo{
    .{ .prefix = "zwanzig-disable-next-line", .kind = .next_line },
    .{ .prefix = "zwanzig-disable", .kind = .file_scope },
    .{ .prefix = "zwanzig-enable", .kind = .enable },
};

const ActiveSuppressions = struct {
    all_rules_start: ?usize,
    rule_starts: std.StringHashMap(usize),

    fn init(allocator: std.mem.Allocator) ActiveSuppressions {
        return .{
            .all_rules_start = null,
            .rule_starts = std.StringHashMap(usize).init(allocator),
        };
    }

    fn deinit(self: *ActiveSuppressions) void {
        self.rule_starts.deinit();
    }
};

pub fn parseSuppressions(
    allocator: std.mem.Allocator,
    content: []const u8,
) SuppressionError!SuppressionMap {
    var map = SuppressionMap.init(allocator);
    errdefer map.deinit();

    var active = ActiveSuppressions.init(allocator);
    defer active.deinit();

    // Walk one physical line per iteration, so the counter advances exactly
    // once per line whatever the line holds: code, a blank line, a
    // whitespace-only line, a comment-only line, a directive, or a final line
    // without a newline.
    var line_number: usize = 1;
    var line_start: usize = 0;

    while (line_start < content.len) {
        const newline = std.mem.indexOfScalarPos(u8, content, line_start, '\n');
        const line_end = newline orelse content.len;

        try parseLine(content[line_start..line_end], line_number, &map, &active);

        line_number += 1;
        line_start = line_end + 1;
    }

    if (active.all_rules_start) |start| {
        try map.all_rules_file_scope_ranges.append(allocator, .{ .start = start, .end = null });
    }
    var iter = active.rule_starts.iterator();
    while (iter.next()) |entry| {
        const ranges_entry = try map.file_scope_ranges.getOrPut(entry.key_ptr.*);
        if (!ranges_entry.found_existing) {
            ranges_entry.value_ptr.* = .empty;
        }
        try ranges_entry.value_ptr.append(allocator, .{ .start = entry.value_ptr.*, .end = null });
    }

    return map;
}

/// Scan one line, which holds the text without its newline terminator, for a
/// directive. A line can hold more than one comment, so the scan continues
/// past a comment that carries no directive.
fn parseLine(
    line: []const u8,
    line_number: usize,
    map: *SuppressionMap,
    active: *ActiveSuppressions,
) SuppressionError!void {
    var i: usize = 0;
    while (i + 1 < line.len) : (i += 1) {
        if (line[i] != '/' or line[i + 1] != '/') continue;

        var directive_start = i + 2;
        while (directive_start < line.len and
            (line[directive_start] == ' ' or line[directive_start] == '\t'))
        {
            directive_start += 1;
        }
        i = directive_start;

        if (try tryParseDirective(line, directive_start, line_number, map, active)) {
            return;
        }
    }
}

/// Apply the directive that starts at `start`, if one does. Reports false when
/// no known directive prefix sits there.
fn tryParseDirective(
    line: []const u8,
    start: usize,
    directive_line: usize,
    map: *SuppressionMap,
    active: *ActiveSuppressions,
) SuppressionError!bool {
    for (directives) |directive_info| {
        const prefix = directive_info.prefix;
        const kind = directive_info.kind;

        if (start + prefix.len > line.len) continue;
        if (!std.mem.eql(u8, line[start .. start + prefix.len], prefix)) continue;

        var rules_start = start + prefix.len;
        if (rules_start < line.len and line[rules_start] == ':') {
            rules_start += 1;
            try applyDirectiveWithRules(map, active, kind, directive_line, line[rules_start..]);
        } else {
            try applyDirectiveAllRules(map, active, kind, directive_line);
        }

        return true;
    }

    return false;
}

fn applyDirectiveAllRules(
    map: *SuppressionMap,
    active: *ActiveSuppressions,
    kind: DirectiveKind,
    directive_line: usize,
) SuppressionError!void {
    const target_line = directive_line + 1;

    switch (kind) {
        .next_line => {
            try map.all_rules_suppressed_lines.put(target_line, {});
        },
        .file_scope => {
            if (active.all_rules_start == null) {
                active.all_rules_start = directive_line;
            }
        },
        .enable => {
            if (active.all_rules_start) |start| {
                try map.all_rules_file_scope_ranges.append(map.allocator, .{ .start = start, .end = directive_line });
                active.all_rules_start = null;
            }
            var iter = active.rule_starts.iterator();
            while (iter.next()) |entry| {
                const ranges_entry = try map.file_scope_ranges.getOrPut(entry.key_ptr.*);
                if (!ranges_entry.found_existing) {
                    ranges_entry.value_ptr.* = .empty;
                }
                try ranges_entry.value_ptr.append(map.allocator, .{ .start = entry.value_ptr.*, .end = directive_line });
            }
            active.rule_starts.clearRetainingCapacity();
        },
    }
}

fn applyDirectiveWithRules(
    map: *SuppressionMap,
    active: *ActiveSuppressions,
    kind: DirectiveKind,
    directive_line: usize,
    rule_list_text: []const u8,
) SuppressionError!void {
    const target_line = directive_line + 1;

    var iter = std.mem.splitSequence(u8, rule_list_text, ",");
    while (iter.next()) |part| {
        const rule_id = std.mem.trim(u8, part, " \t");
        if (rule_id.len == 0) continue;

        switch (kind) {
            .next_line => {
                const entry = try map.rule_specific_lines.getOrPut(rule_id);
                if (!entry.found_existing) {
                    entry.value_ptr.* = std.AutoHashMap(usize, void).init(map.allocator);
                }
                try entry.value_ptr.put(target_line, {});
            },
            .file_scope => {
                if (!active.rule_starts.contains(rule_id)) {
                    try active.rule_starts.put(rule_id, directive_line);
                }
            },
            .enable => {
                if (active.rule_starts.fetchRemove(rule_id)) |kv| {
                    const ranges_entry = try map.file_scope_ranges.getOrPut(rule_id);
                    if (!ranges_entry.found_existing) {
                        ranges_entry.value_ptr.* = .empty;
                    }
                    try ranges_entry.value_ptr.append(map.allocator, .{ .start = kv.value, .end = directive_line });
                }
            },
        }
    }
}

test "parseSuppressions: next-line all rules" {
    const allocator = std.testing.allocator;
    const content =
        \\const x = 1;
        \\// zwanzig-disable-next-line
        \\const y = 2;
        \\const z = 3;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(1, "any-rule"));
    try std.testing.expect(!map.isSuppressed(2, "any-rule"));
    try std.testing.expect(map.isSuppressed(3, "any-rule"));
    try std.testing.expect(map.isSuppressed(3, "other-rule"));
    try std.testing.expect(!map.isSuppressed(4, "any-rule"));
}

test "parseSuppressions: next-line specific rules" {
    const allocator = std.testing.allocator;
    const content =
        \\// zwanzig-disable-next-line: empty-catch, todo
        \\const x = 1;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(map.isSuppressed(2, "empty-catch"));
    try std.testing.expect(map.isSuppressed(2, "todo"));
    try std.testing.expect(!map.isSuppressed(2, "unused-decl"));
}

test "parseSuppressions: file scope suppression" {
    const allocator = std.testing.allocator;
    const content =
        \\const x = 1;
        \\// zwanzig-disable: todo
        \\const y = 2;
        \\const z = 3;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(1, "todo"));
    try std.testing.expect(map.isSuppressed(2, "todo"));
    try std.testing.expect(map.isSuppressed(3, "todo"));
    try std.testing.expect(map.isSuppressed(4, "todo"));
    try std.testing.expect(!map.isSuppressed(1, "other-rule"));
    try std.testing.expect(!map.isSuppressed(4, "other-rule"));
}

test "parseSuppressions: file scope with re-enable" {
    const allocator = std.testing.allocator;
    const content =
        \\// zwanzig-disable: todo
        \\const x = 1;
        \\// zwanzig-enable: todo
        \\const y = 2;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(map.isSuppressed(1, "todo"));
    try std.testing.expect(map.isSuppressed(2, "todo"));
    try std.testing.expect(!map.isSuppressed(3, "todo"));
    try std.testing.expect(!map.isSuppressed(4, "todo"));
}

test "parseSuppressions: all rules file scope" {
    const allocator = std.testing.allocator;
    const content =
        \\const x = 1;
        \\// zwanzig-disable
        \\const y = 2;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(1, "any-rule"));
    try std.testing.expect(map.isSuppressed(2, "any-rule"));
    try std.testing.expect(map.isSuppressed(3, "any-rule"));
}

test "parseSuppressions: whitespace handling" {
    const allocator = std.testing.allocator;
    const content =
        \\//   zwanzig-disable-next-line:  empty-catch  ,  todo
        \\const x = 1;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(map.isSuppressed(2, "empty-catch"));
    try std.testing.expect(map.isSuppressed(2, "todo"));
}

test "parseSuppressions: empty content" {
    const allocator = std.testing.allocator;
    const content = "";

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(1, "any-rule"));
}

test "parseSuppressions: no directives" {
    const allocator = std.testing.allocator;
    const content =
        \\// This is a regular comment
        \\const x = 1;
        \\// Another comment
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(1, "any-rule"));
    try std.testing.expect(!map.isSuppressed(2, "any-rule"));
    try std.testing.expect(!map.isSuppressed(3, "any-rule"));
}

test "parseSuppressions: all rules re-enable" {
    const allocator = std.testing.allocator;
    const content =
        \\// zwanzig-disable
        \\const x = 1;
        \\// zwanzig-enable
        \\const y = 2;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(map.isSuppressed(1, "any-rule"));
    try std.testing.expect(map.isSuppressed(2, "any-rule"));
    try std.testing.expect(!map.isSuppressed(3, "any-rule"));
    try std.testing.expect(!map.isSuppressed(4, "any-rule"));
}

test "parseSuppressions: repeated disable preserves first start" {
    const allocator = std.testing.allocator;
    const content =
        \\// zwanzig-disable
        \\const x = 1;
        \\// zwanzig-disable
        \\const y = 2;
        \\// zwanzig-enable
        \\const z = 3;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(map.isSuppressed(1, "any-rule"));
    try std.testing.expect(map.isSuppressed(2, "any-rule"));
    try std.testing.expect(map.isSuppressed(3, "any-rule"));
    try std.testing.expect(map.isSuppressed(4, "any-rule"));
    try std.testing.expect(!map.isSuppressed(5, "any-rule"));
    try std.testing.expect(!map.isSuppressed(6, "any-rule"));
}

test "parseSuppressions: repeated rule-specific disable preserves first start" {
    const allocator = std.testing.allocator;
    const content =
        \\// zwanzig-disable: todo
        \\const x = 1;
        \\// zwanzig-disable: todo
        \\const y = 2;
        \\// zwanzig-enable: todo
        \\const z = 3;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(map.isSuppressed(1, "todo"));
    try std.testing.expect(map.isSuppressed(2, "todo"));
    try std.testing.expect(map.isSuppressed(3, "todo"));
    try std.testing.expect(map.isSuppressed(4, "todo"));
    try std.testing.expect(!map.isSuppressed(5, "todo"));
    try std.testing.expect(!map.isSuppressed(6, "todo"));
}

test "parseSuppressions: empty comment line keeps the line counter in step" {
    const allocator = std.testing.allocator;
    // Line 2 holds nothing after the comment marker. It still has to count as
    // a line, or the directive on line 3 is attributed to line 2 and
    // suppresses line 3 instead of line 4.
    const content =
        \\const a = 1;
        \\//
        \\// zwanzig-disable-next-line
        \\const b = 2;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(2, "any-rule"));
    try std.testing.expect(!map.isSuppressed(3, "any-rule"));
    try std.testing.expect(map.isSuppressed(4, "any-rule"));
    try std.testing.expect(!map.isSuppressed(5, "any-rule"));
}

test "parseSuppressions: whitespace-only comment line keeps the line counter in step" {
    const allocator = std.testing.allocator;
    // The blanks at the end of line 2 are written out rather than left as
    // trailing whitespace, so that the line stays visible.
    const content = "const a = 1;\n" ++
        "//   \t\n" ++
        "// zwanzig-disable-next-line\n" ++
        "const b = 2;\n";

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(3, "any-rule"));
    try std.testing.expect(map.isSuppressed(4, "any-rule"));
    try std.testing.expect(!map.isSuppressed(5, "any-rule"));
}

test "parseSuppressions: blank line keeps the line counter in step" {
    const allocator = std.testing.allocator;
    const content =
        \\const a = 1;
        \\
        \\// zwanzig-disable-next-line
        \\const b = 2;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(3, "any-rule"));
    try std.testing.expect(map.isSuppressed(4, "any-rule"));
    try std.testing.expect(!map.isSuppressed(5, "any-rule"));
}

test "parseSuppressions: full line comment keeps the line counter in step" {
    const allocator = std.testing.allocator;
    const content =
        \\const a = 1;
        \\// an ordinary comment
        \\// zwanzig-disable-next-line
        \\const b = 2;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(3, "any-rule"));
    try std.testing.expect(map.isSuppressed(4, "any-rule"));
    try std.testing.expect(!map.isSuppressed(5, "any-rule"));
}

test "parseSuppressions: file scope bounds after an empty comment line" {
    const allocator = std.testing.allocator;
    // The empty comment on line 1 must not pull both bounds of the region one
    // line up.
    const content =
        \\//
        \\// zwanzig-disable: todo
        \\const a = 1;
        \\// zwanzig-enable: todo
        \\const b = 2;
    ;

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(1, "todo"));
    try std.testing.expect(map.isSuppressed(2, "todo"));
    try std.testing.expect(map.isSuppressed(3, "todo"));
    try std.testing.expect(!map.isSuppressed(4, "todo"));
    try std.testing.expect(!map.isSuppressed(5, "todo"));
    // The region names only "todo", so it must leave every other rule
    // unsuppressed, including on the lines the region does cover.
    try std.testing.expect(!map.isSuppressed(1, "other-rule"));
    try std.testing.expect(!map.isSuppressed(3, "other-rule"));
}

test "parseSuppressions: last line without a trailing newline" {
    const allocator = std.testing.allocator;
    // The file ends on a code line that carries no newline.
    const content = "const a = 1;\n" ++ "// zwanzig-disable-next-line\n" ++ "const b = 2;";

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(2, "any-rule"));
    try std.testing.expect(map.isSuppressed(3, "any-rule"));
}

test "parseSuppressions: rule list on the last line without a trailing newline" {
    const allocator = std.testing.allocator;
    // The directive ends the file, carries a rule list, and follows an empty
    // comment.
    const content = "const a = 1;\n" ++ "//\n" ++ "// zwanzig-disable-next-line: todo";

    var map = try parseSuppressions(allocator, content);
    defer map.deinit();

    try std.testing.expect(!map.isSuppressed(3, "todo"));
    try std.testing.expect(map.isSuppressed(4, "todo"));
    try std.testing.expect(!map.isSuppressed(4, "other-rule"));
}
