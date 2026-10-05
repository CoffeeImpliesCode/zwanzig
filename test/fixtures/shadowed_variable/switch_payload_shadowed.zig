// Test: switch capture payload shadowed by inner declaration
// EXPECT: line=9 col=19 rule=shadowed-variable message=shadows
const Tag = enum { a, b };
const Data = union(Tag) { a: i32, b: void };

fn foo(data: Data) void {
    switch (data) {
        .a => |value| {
            const value = 0;
            _ = value;
        },
        .b => {},
    }
}

// zwanzig: not a standalone program: a switch prong capture shadowed by a local constant of the same name is the intentional invalidity under test, verifying that the shadowed-variable rule reports the inner declaration.
