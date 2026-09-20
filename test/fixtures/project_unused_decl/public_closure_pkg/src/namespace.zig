const builtin = @import("builtin");
const native_impl = @import("native.zig");
const fallback_impl = @import("fallback.zig");
const private_impl = @import("private.zig");

pub const selected = if (builtin.os.tag == .linux) native_impl else fallback_impl;
