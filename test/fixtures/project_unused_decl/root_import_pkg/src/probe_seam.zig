// Seam module of the probe object, kept separate from src/seam.zig so each
// artifact reaches only its own seam.
pub const ztex_abi_version: u32 = 1;

pub const ztex_context = anyopaque;

pub fn ztex_render_svg(context: *ztex_context) callconv(.c) void {
    _ = context;
}

comptime {
    const probe_root = @import("root");
    if (@hasDecl(probe_root, "ztex_abi_check_marker")) probe_root.checkProbeRoot(.{
        .abi_version = @TypeOf(ztex_abi_version),
        .render = @TypeOf(ztex_render_svg),
    });
}
