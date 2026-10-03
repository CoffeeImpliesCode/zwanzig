// EXPECT: line=8 rule=divide-by-zero-engine severity=error message=division
// EXPECT: line=15 rule=divide-by-zero-engine severity=error message=division
// EXPECT: line=21 rule=divide-by-zero-engine severity=warning message=division
// EXPECT: line=27 rule=divide-by-zero-engine severity=error message=division

pub fn equalZero(value: i32) i32 {
    if (value == 0) {
        return @divTrunc(12, value);
    }
    return 0;
}

pub fn falseNotEqual(value: i32) i32 {
    if (0 != value) return 0;
    return @divTrunc(12, value);
}

pub fn maybeZero(value: i32) i32 {
    if (0 > value) return 0;
    if (value > 1) return 0;
    return @divTrunc(12, value);
}

pub fn unsupportedArithmetic(value: i32) i32 {
    const denominator: i32 = 0;
    if (value + 1 == 1) {
        return @divTrunc(12, denominator);
    }
    return 0;
}

pub fn guardedPositive(value: i32) i32 {
    if (0 >= value) return 0;
    return @divTrunc(12, value);
}

pub fn guardedNegative(value: i32) i32 {
    if (-1 >= value) return @divTrunc(12, value);
    return 0;
}

pub fn guardedNotEqual(value: i32) i32 {
    if (value != 0) return @divTrunc(12, value);
    return 0;
}

pub fn falseEqual(value: i32) i32 {
    if (value == 0) return 0;
    return @divTrunc(12, value);
}

pub fn falseLowerBound(value: i32) i32 {
    if (value < 1) return 0;
    return @divTrunc(12, value);
}

pub fn falseUpperBound(value: i32) i32 {
    if (value >= 0) return 0;
    return @divTrunc(12, value);
}

pub fn groupedNegative(value: i32) i32 {
    if ((value) <= -(0b1)) return @divTrunc(12, value);
    return 0;
}
