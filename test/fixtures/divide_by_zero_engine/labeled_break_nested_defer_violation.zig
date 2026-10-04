// EXPECT: rule=divide-by-zero-engine severity=error message=division

// Ten deferred bodies, each a labeled block breaking to its own label. Every
// transfer stays inside the body that contains it, so this is ordinary Zig, but
// only the deepest break reaches the write. An analyzer that truncates the
// unwind, or that reads a local break as an escape, loses `denominator = 0` and
// calls the division safe.
pub fn nested_defer_labels() i64 {
    var denominator: i64 = 3;
    outer: {
        defer inner0: {
            defer inner1: {
                defer inner2: {
                    defer inner3: {
                        defer inner4: {
                            defer inner5: {
                                defer inner6: {
                                    defer inner7: {
                                        defer inner8: {
                                            defer inner9: {
                                                denominator = 0;
                                                break :inner9;
                                            }
                                            break :inner8;
                                        }
                                        break :inner7;
                                    }
                                    break :inner6;
                                }
                                break :inner5;
                            }
                            break :inner4;
                        }
                        break :inner3;
                    }
                    break :inner2;
                }
                break :inner1;
            }
            break :inner0;
        }
        break :outer;
    }
    return @divTrunc(1, denominator);
}
