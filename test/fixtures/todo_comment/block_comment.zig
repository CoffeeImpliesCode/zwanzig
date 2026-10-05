// EXPECT: line=3 rule=todo message=clean up
const x: i32 = 42;
/* TODO: clean up */
const y: i32 = 43;

// zwanzig: not a standalone program: block comments `/* ... */` are not valid Zig in 0.15/0.16, but the analyzer scans them directly in source text.
