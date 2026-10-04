// EXPECT: rule=divide-by-zero-engine severity=warning message=possible

// An unlabeled `break` leaves the loop, and loop exits are not modeled here.
// It must not become a jump that prunes the division below it, or the guard
// stops protecting anything and an unknown denominator goes unreported. Every
// path through the body returns, so the loop has no back edge and the finding
// does not depend on how a loop head is widened.
pub fn unlabeled_break_does_not_prune(lhs: i64, rhs: i64) i64 {
    while (rhs != 7) {
        if (rhs == 0) break;
        return @divTrunc(lhs, rhs);
    }
    return 0;
}
