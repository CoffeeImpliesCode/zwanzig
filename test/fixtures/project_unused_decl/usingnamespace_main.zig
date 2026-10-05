usingnamespace @import("usingnamespace_api.zig");

pub fn main() void {
    exposed();
}

// zwanzig: not a standalone program: `usingnamespace` was removed from the Zig language and cannot compile on any supported frontend, but the file stays a syntax-error input the project pass must report without adding public non-use claims.
