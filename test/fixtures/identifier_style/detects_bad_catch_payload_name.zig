// EXPECT: line=3 rule=identifier-style
fn foo() void {
    _ = bar() catch |BadErr| {
        _ = BadErr;
    };
}

fn bar() !void {}
