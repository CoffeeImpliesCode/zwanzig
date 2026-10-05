// EXPECT: none
// Different literal strings should not be treated as the same full path
const foo = @import("foo");
const foo2 = @import("./foo.zig");

// zwanzig: not a standalone program: the dupe-import rule inspects import paths textually, and the imported modules `foo` and `./foo.zig` do not exist on disk.
