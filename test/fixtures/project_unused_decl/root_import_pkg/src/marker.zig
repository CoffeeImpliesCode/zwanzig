// Stand-in for the translated C header the ABI checker compares against.
pub const ztex_abi_version: u32 = 1;

pub const ztex_context = anyopaque;

pub fn ztex_render_svg(context: *ztex_context) callconv(.c) void {
    _ = context;
}
