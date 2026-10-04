// EXPECT: line=3 rule=identifier-style
const std = @import("std");
const Print = std.debug.print;
// The alias is a *value* constant (a function), so it keeps the snake_case
// value rule even though the same binding spelled for a namespace or a file
// struct may be lower_snake_case or PascalCase. The use has to sit in a
// function body: a top-level `_ = Print;` is not valid Zig, it makes the file
// a parse error, and the CLI could then never reach this diagnostic.
fn report() void {
    Print("identifier style\n", .{});
}
