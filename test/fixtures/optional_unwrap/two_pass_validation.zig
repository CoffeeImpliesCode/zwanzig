// EXPECT: line=11 rule=optional-unwrap
// EXPECT: line=22 rule=optional-unwrap
const Spec = struct { view: ?u32 = null };
pub fn publish(specs: []Spec, out: []u32) void {
    for (specs) |spec| {
        const view = spec.view orelse return;
        _ = view;
    }
    for (specs) |spec| {
        if (out.len == 0) return;
        out[0] = spec.view.?;
    }
}
pub fn mutated(specs: []Spec, out: []u32) void {
    for (specs) |spec| {
        const view = spec.view orelse return;
        _ = view;
    }
    for (specs) |*spec| {
        spec.view = null;
        if (out.len == 0) return;
        out[0] = spec.view.?;
    }
}
