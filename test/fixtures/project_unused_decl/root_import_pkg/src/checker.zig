// The compilation root of the abi-check object. src/seam.zig calls checkSeam
// from top-level comptime through `@import("root")`, so it is live even though
// no analyzed file imports this one by name.
pub const ztex_abi_check_marker = @import("ztex_header");
const header = ztex_abi_check_marker;

const seam = @import("abi_seam");

comptime {
    if (!@hasDecl(seam, "ztex_render_svg")) @compileError(
        "seam does not export ztex_render_svg",
    );
}

pub fn checkSeam(comptime entries: anytype) void {
    if (entries.abi_version != @TypeOf(header.ztex_abi_version)) @compileError(
        "ztex_abi_version width drifted between the seam and the header",
    );
    if (entries.render != @TypeOf(header.ztex_render_svg)) @compileError(
        "ztex_render_svg signature drifted between the seam and the header",
    );
}

/// Nothing reaches this through the compilation root, so it stays diagnosable.
pub fn unusedRootHelper() void {}

/// Same-file unused control: the per-file rule must keep reporting it.
fn unusedControl(comptime n: usize) usize {
    return n + 1;
}
