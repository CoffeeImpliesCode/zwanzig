// EXPECT: none
const namespace_alias = @import("std");
const RootName: type = namespace_alias;
pub const api = struct {
    pub const Name: type = namespace_alias;
};
