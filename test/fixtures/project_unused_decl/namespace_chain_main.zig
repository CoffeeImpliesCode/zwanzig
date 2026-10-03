const compile_driver = @import("namespace_chain_driver.zig");

pub const compile = struct {
    pub const Driver: type = compile_driver;
};

pub fn main() void {
    compile.Driver.used();
}
