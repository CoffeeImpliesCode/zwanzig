// EXPECT: line=4 rule=identifier-style
const Foo = struct { value: i32 };
const Bar = struct {
    const Foo = 1; // `Bar` takes the type name over for a plain value.
};
