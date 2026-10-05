// EXPECT: none
//
// The `break` names no label, so `processBreak` resolves it against the
// innermost open loop and transfers to that loop's exit node - the node its
// header already reaches on the `loop_exit` edge - rather than falling into
// the statement behind the `if`. The transfer terminates, so the guard's true
// arm contributes no edge to the merge, and the merge's only predecessor is
// the guard's false edge. That edge is read through `extractBranchConstraint`
// as `rhs == 0` and negated for the false side, so every state reaching the
// division carries `rhs != 0`; the header's own `rhs != 7` rides along on the
// body edge but never decides the divisor.
//
// The denominator is therefore excluded from zero on every path that reaches
// it, which `classifyVariableRisk` answers as `definitely_non_zero` and the
// scan reports nothing. The body's last statement is the `return`, so
// `processWhile` adds no `loop_back` edge to the header and the state there is
// never widened: this reads the same whether widening is on or off.
pub fn unlabeled_break_does_not_prune(lhs: i64, rhs: i64) i64 {
    while (rhs != 7) {
        if (rhs == 0) break;
        return @divTrunc(lhs, rhs);
    }
    return 0;
}
