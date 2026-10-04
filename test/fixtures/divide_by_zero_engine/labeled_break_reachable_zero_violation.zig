// EXPECT: rule=divide-by-zero-engine severity=error message=division

pub fn reachable_zero(lhs: i64) i64 {
    var out: i64 = 0;
    var divisor: i64 = 3;
    outer: {
        divisor = 0;
        out = @divTrunc(lhs, divisor);
        break :outer;
    }
    return out;
}
