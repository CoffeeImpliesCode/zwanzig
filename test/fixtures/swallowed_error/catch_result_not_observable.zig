// EXPECT: line=21 rule=swallowed-error
// EXPECT: line=29 rule=swallowed-error
// EXPECT: line=38 rule=swallowed-error
// EXPECT: line=48 rule=swallowed-error
// EXPECT: line=56 rule=swallowed-error
// EXPECT: line=65 rule=swallowed-error
// EXPECT: line=73 rule=swallowed-error
// EXPECT: line=82 rule=swallowed-error
// EXPECT: line=90 rule=swallowed-error
// A handler only reports the error through the result when that value really
// reaches the caller and really records the failure. An arbitrary value, a
// later overwrite, a shadowed name, a different returned value, a result
// written on some paths only, and a counter change that adds nothing all keep
// the warning.
fn mayFail() error{BadByte}!u8 {
    return error.BadByte;
}

fn arbitraryValue() i32 {
    var y: i32 = 0;
    _ = mayFail() catch {
        y = 1;
    };
    return y;
}

fn overwrittenTally() u8 {
    var rejected: u8 = 0;
    _ = mayFail() catch {
        rejected += 1;
    };
    rejected = 0;
    return rejected;
}

fn shadowedTally() u8 {
    var rejected: u8 = 0;
    _ = mayFail() catch {
        var rejected: u8 = 9;
        rejected += 1;
        _ = rejected;
    };
    return rejected;
}

fn notReturned() u8 {
    var rejected: u8 = 0;
    _ = mayFail() catch {
        rejected += 1;
    };
    return 0;
}

fn conditionallyReturned(flag: bool) u8 {
    var rejected: u8 = 0;
    _ = mayFail() catch {
        rejected += 1;
    };
    if (flag) return rejected;
    return 0;
}

fn zeroIncrement() u8 {
    var rejected: u8 = 0;
    _ = mayFail() catch {
        rejected += 0;
    };
    return rejected;
}

fn zeroDecrement() i8 {
    var rejected: i8 = 0;
    _ = mayFail() catch {
        rejected -= 0;
    };
    return rejected;
}

fn zeroConstIncrement() u8 {
    var rejected: u8 = 0;
    const bump: u8 = 0;
    _ = mayFail() catch {
        rejected += bump;
    };
    return rejected;
}

fn maybeZeroIncrement(step: u8) u8 {
    var rejected: u8 = 0;
    _ = mayFail() catch {
        rejected += step;
    };
    return rejected;
}

// zwanzig: not a standalone program: shadowing `rejected` inside `shadowedTally` is the intentional invalidity under test, verifying that catch-block shadowing prevents error observation.
