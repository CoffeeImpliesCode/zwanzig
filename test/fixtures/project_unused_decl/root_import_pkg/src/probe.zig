// Root of the deliberately failing probe object. Its abi_version comparison
// is wrong on purpose, so `zig build probe` must fail with the unique message
// below and point at the guarded call in src/probe_seam.zig.
pub const ztex_abi_check_marker = @import("ztex_header");
const header = ztex_abi_check_marker;

const seam = @import("abi_probe_seam");

comptime {
    if (!@hasDecl(seam, "ztex_render_svg")) @compileError(
        "probe seam does not export ztex_render_svg",
    );
}

pub fn checkProbeRoot(comptime entries: anytype) void {
    if (entries.abi_version != u8) @compileError(
        "named-module probe reached the root checker",
    );
    if (entries.render != @TypeOf(header.ztex_render_svg)) @compileError(
        "ztex_render_svg signature drifted between the probe seam and the header",
    );
}

/// Nothing reaches this through the probe compilation root either.
pub fn unusedProbeHelper() void {}
