// EXPECT: line=16 rule=unused-decl

const std = @import("std");
const real_testing = std.testing;
const std_alias = std;
const custom = struct {
    pub fn refAllDeclsRecursive(comptime T: type) void { _ = T; }
};
const fake_namespace = struct {
    pub const testing = struct {
        pub fn refAllDecls(_: type) void {}
    };
};

pub const FakeReflected = struct {
    fn trulyUnused() void {}
    pub fn exercise() void {
        custom.refAllDeclsRecursive(@This());
        fake_namespace.testing.refAllDecls(@This());
        const real_testing = struct {
            pub fn refAllDecls(_: type) void {}
        };
        real_testing.refAllDecls(@This());
    }
};

pub const ActuallyReflected = struct {
    fn reachedViaRealReflection() void {}
    test { comptime { real_testing.refAllDeclsRecursive(@This()); } }
    test { comptime { std_alias.testing.refAllDecls(@This()); } }
};
