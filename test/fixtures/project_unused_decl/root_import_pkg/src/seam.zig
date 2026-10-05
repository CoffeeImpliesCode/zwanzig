// A separately named module whose top-level comptime calls the compilation
// root's checker through `@import("root")`.
pub const ztex_abi_version: u32 = 1;

pub const ztex_context = anyopaque;

pub fn ztex_render_svg(context: *ztex_context) callconv(.c) void {
    _ = context;
}

comptime {
    const checker_root = @import("root");
    if (@hasDecl(checker_root, "ztex_abi_check_marker")) checker_root.checkSeam(.{
        .abi_version = @TypeOf(ztex_abi_version),
        .render = @TypeOf(ztex_render_svg),
    });
}
