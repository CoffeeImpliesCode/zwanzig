# Task: Zwanzig Correctness Fixes and Analysis Improvements

This plan originally covered missing branch constraints, error-path summaries, unreachable-code proofs, and persistent analysis artifacts. The sections below separate implemented behavior from remaining scope.

## Verification status

For the revision these steps were written against, both frontend CLIs passed smoke checks for guarded integer divides, contradictory guards, conservative floating-point and wide-integer guards, hard call-context limits, and constant warnings under limits. Cold and warm disk-cache runs produced identical diagnostics. Compatible checkers reused one engine run, and one-worker and two-worker runs produced identical diagnostics. Contextual constant references retained the expected unused homonym report.

Use `nix develop` for Zig 0.16.0 and `nix develop .#zig015` for Zig 0.15.2. Only Zig 0.15.2 defines canonical formatting.

Full `just test` and `just lint` runs, including analyzer self-checks, passed for the revision these steps were written against. Later edits are not covered by that result. The verification status of the current revision is recorded in [the migration plan](../ZIG_0_16_MIGRATION_PLAN.md#current-status).

### Performance measurements

The measured runs that motivated the indexing, reuse and import-resolution work
used frozen input snapshots, one analysis worker, nice level 15 and unchanged
default analysis limits, and compared diagnostic multisets, exit status and
analysis-limit warnings before and after each change. `scripts/benchmark.py`
implements that procedure; see
[DEVELOPMENT.md](../DEVELOPMENT.md#performance-measurement).

The workloads themselves, their source-file counts, their timings, their
diagnostic details and their input and binary hashes are private evidence and are
not published here. Nothing below is reproducible from this repository, so the
conclusions are stated qualitatively and no numbers are claimed.

- Profiling identified repeated enclosing-function scans and AST token-range
  walks as the dominant costs. Guards now reuse lexical candidates and cached
  ranges.
- Source-owned declaration parent maps replace per-engine copies.
- Indexed import lookup removes repeated file scans and path normalization while
  preserving the earliest exact, relative, or package match.
- Peak memory stayed close to the baseline; the one workload whose peak rose
  still stayed inside the engine-owned cache admission budget. Shared source
  metadata sits outside that budget.
- Analysis limits and runtime safety checks are unchanged by all of this work.

## Step 1: Extract branch constraints

### Implemented
- The extractor reads condition ASTs and resolves identifiers to canonical VarIds. It no longer depends on placeholder comparison operands.
- Integer comparisons, null checks, boolean checks, and literal conditions can refine branch states.
- Integer guards require a proven safe signed-i64 domain. Floating-point, unknown, and wider values remain conservative.
- Uncertain expressions do not establish path-pruning constraints.

### Remaining scope
Richer numeric domains and additional expression forms remain future work. The current integer domain does not establish general arithmetic soundness for every Zig type.

### Acceptance criteria
- A supported optional comparison applies the correct null constraint on each branch.
- `if (x < 0) {}` refines `x` only when its integer domain supports the proof.
- Unsupported numeric domains do not cause false path pruning or suppress reachable diagnostics.
- The full dual-frontend test and lint gates pass.

## Step 2: Preserve summary error paths

### Implemented
- Summary computation accounts for explicit error returns and available error-union return information.
- Mixed success/error summaries fork caller states into success and error paths.
- Summary application preserves an error already pending in the caller.

### Remaining scope
A full error-union value redesign and cross-file call execution remain roadmap work. Current summary branching does not imply either feature.

### Acceptance criteria
- A summary for `return error.Foo` preserves the possible error outcome.
- A mixed-return callee retains both caller outcomes.
- A successful callee outcome does not erase a pending caller error.
- The full dual-frontend test and lint gates pass.

## Step 3: Prove limited path-based unreachability

### Implemented
- The AST checks retain constant-condition and obvious unreachable-code diagnostics.
- `unreachable-code-engine` also uses path constraints for a limited proof under immutable scalar enclosing guards.
- Path-based proofs require complete function analysis. A missing exploded-graph node alone does not prove unreachable code.
- Hard state caps count all call contexts at each CFG point. A limit stops the incomplete analysis and emits a warning.
- A limit disables incomplete path proofs, not independently established constant-condition warnings.

### Remaining scope
The original plan proposed scanning every CFG node without exploded states. That broad rule is not implemented and is not a sound replacement for the restricted proof. General loop and trailing-code proofs require separate support.

### Acceptance criteria
- Contradictory supported enclosing guards can establish an unreachable path after complete analysis.
- Mutable guards and incomplete analyses do not establish that proof.
- A hard state cap does not exceed its configured count across call contexts.
- Constant warnings remain visible when path analysis reaches a limit.
- The full dual-frontend test and lint gates pass.

## Step 4: Reuse CFG and function-analysis artifacts

### Implemented
- `--cache` persists CFG artifacts, not only metadata. Diagnostics are recomputed on every run.
- Warm CFGs regain live declaration annotations before type-aware analysis. Cache identity and artifact versions guard reuse.
- Within a file, compatible configured function analyses use exclusive mutable leases from `AnalysisCache`. Plain or unstable owned CFGs remain uncached.
- The per-file `TypeContext` outlives its `AnalysisCache`.
- Cache admission occurs after checker lazy queries. Retention is bounded to 64 entries and 16 MiB of live engine-owned allocation payload.
- The payload bound is not an RSS limit. Separately owned artifacts and shared source syntax metadata are outside it. Statistics count actual analysis runs.

### Remaining scope
Full persisted ZIR, typed IR, and summaries remain future work. In-memory function-analysis reuse does not provide cross-run persistence for these artifacts. No performance improvement is claimed without measurements.

### Acceptance criteria
- Repeated analysis with `--cache` reuses compatible CFGs and still computes diagnostics.
- Warm CFG type annotations produce the same diagnostic behavior as cold analysis.
- Incompatible analyses do not share mutable state. Retained engine payload stays within the cache admission limits.
- The full dual-frontend test and lint gates pass. Separate measurements establish any performance claim.

## Step 5: Keep documentation aligned

### Documentation contract
- `docs/IMPLEMENTATION.md` describes diagnostic ownership, constraint extraction, summary branching, limited unreachable proofs, and both cache lifetimes.
- User-facing docs distinguish supported proofs from general CFG reachability.
- Plans distinguish implementation from validation. They do not treat pending gates or performance measurements as passed.
- Persistent typed IR/summaries, additional parity rules, full sentinel-value propagation, the error-union value redesign, and cross-file call execution remain roadmap work.

### Acceptance criteria
- Documentation matches the implemented behavior and states its limits.
- Future rules and richer domains are not listed as shipped features.
- Release and validation claims retain their actual verification status.
