// EXPECT: line=2 rule=unused-decl message=config
const config = 1;

pub fn run(config: i32) void {
    _ = config;
}

// zwanzig: not a standalone program: function parameter shadowing container constant `config` is the intentional invalidity under test, verifying that shadowed container decls are detected as unused.
