// EXPECT: line=4 rule=unreachable-code-engine
fn integerGuard(value: i32) i32 {
    if (value > 0) {
        if (value < 0) {
            return 1;
        }
    }
    return 0;
}

// EXPECT: line=16 rule=unreachable-code-engine
fn booleanGuard(flag: bool) u8 {
    if (flag) {
        if (flag) {
            return 0;
        } else {
            return 1;
        }
    }
    return 2;
}
