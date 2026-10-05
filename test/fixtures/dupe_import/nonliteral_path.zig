// EXPECT: none
// Non-literal import paths are not treated as duplicate full paths
const std1 = @import("s" ++ "td");
const std2 = @import("std");

// zwanzig: not a standalone program: a non-literal operand to `@import` is an intentional compiler error because the rule verifies handling of non-literal import paths.
