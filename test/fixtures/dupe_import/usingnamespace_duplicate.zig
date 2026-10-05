// EXPECT: line=3 rule=dupe-import severity=warning
usingnamespace @import("std");
usingnamespace @import("std");

// zwanzig: not a standalone program: `usingnamespace` was removed from the Zig language and cannot compile on any supported frontend, but the rule continues to detect duplicate occurrences in older source patterns.
