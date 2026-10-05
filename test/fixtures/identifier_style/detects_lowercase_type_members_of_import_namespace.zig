// EXPECT: line=8 rule=identifier-style
// EXPECT: line=14 rule=identifier-style
// #76 control: a lowercase exported member of a namespace is a type
// declaration, so it is still reported as needing PascalCase. This file is
// also the namespace whose members `allows_import_namespace_member_type_alias`
// binds, so the import alias and the member declarations are checked together.
pub const kit = struct {
    pub const chord = struct {
        string: u8,
        fret: u8,
        marker: bool = false,
    };

    pub const vertex = struct {
        x: f32,
        y: f32,
    };
};
