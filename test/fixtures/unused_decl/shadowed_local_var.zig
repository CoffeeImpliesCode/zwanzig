// EXPECT: line=2 rule=unused-decl message=shadowed
const shadowed = 1;

pub fn run() void {
    const shadowed = 2;
    _ = shadowed;
}

// zwanzig: not a standalone program: local constant shadowing container constant `shadowed` is the intentional invalidity under test, verifying that shadowed container decls are detected as unused.
