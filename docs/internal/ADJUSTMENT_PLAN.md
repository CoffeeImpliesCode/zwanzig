# Task: Zwanzig Correctness Fixes and Analysis Improvements

This plan originally covered missing branch constraints, error-path summaries, unreachable-code proofs, and persistent analysis artifacts. The sections below separate implemented behavior from remaining scope.

## Verification status

Both frontend CLIs passed smoke checks for guarded integer divides, contradictory guards, conservative floating-point and wide-integer guards, hard call-context limits, and constant warnings under limits. Cold and warm disk-cache runs produced identical diagnostics. Compatible checkers reused one engine run, and one-worker and two-worker runs produced identical diagnostics. Contextual constant references retained the expected unused homonym report.

Full `just test` and `just lint` runs passed under both pinned shells, including analyzer self-checks. Use `nix develop` for Zig 0.16.0 and `nix develop .#zig015` for Zig 0.15.2. Only Zig 0.15.2 defines canonical formatting.

### Performance measurements

Measured on Linux x86-64 with the Zig 0.16.0 ReleaseSafe frontend, one analysis worker, nice level 15, and sequential runs. These are individual measurements, not statistical estimates. CPU columns show user CPU time; RSS is the process peak reported by GNU time.

The baseline is commit `4f3fbce6`, binary SHA-256 `6aab2b0ca68cb4a588445b0153625b71997077a4a1e164ed02ff3ee259886f93`. The measured result binary is `a65f3b03391fa1fc94a388de64cbd50fbd79164d3eb50186a1903aca3962e7fe`. All 343 source files and recorded build/configuration inputs stayed byte-identical, with unchanged source-file membership.

| Workload | Files | Before CPU (s) | After CPU (s) | Speedup | Peak RSS before → after (MiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| mon, default limits | 6 | 4.42 | 0.33 | 13.4× | 22.5 → 21.8 |
| skript, parseable subset | 71 | 115.50 | 19.78 | 5.84× | 32.0 → 49.3 |
| zmath, 1024-state control | 185 | 26.61 | 6.59 | 4.04× | 62.9 → 81.3 |
| nogui, default limits | 79 | 196.97 | 124.44 | 1.58× | 100.3 → 89.7 |
| nogui, `--do todo` | 79 | 0.50 | 0.06 | 8.33× | 20.4 → 5.1 |

Controls and diagnostic checks:

- The skript subset excludes the same two malformed files from both runs: `src/Runtime.zig` and `src/intrinsics/equal.zig`. Both existing diagnostics are unchanged. The new frontend reports two additional errors, independently confirmed by `zig ast-check`: an untyped `@bitCast` in `intrinsics/ffi.zig` and an undeclared `min` in `intrinsics/modules.zig`.
- The zmath control uses `--max-states-per-point 1024` in both runs. Neither run hits an analysis limit, and all 122 diagnostics are unchanged.
- mon, nogui, and the AST-only control retain exactly the same diagnostic multisets and report no analysis-limit warnings.
- Instruction counts fall by 91.9% for mon, 82.4% for the skript control, 79.5% for the zmath control, and 34.4% for nogui. RSS rises in the two controlled workloads; these changes are not a universal memory reduction.
- The complete 73-file skript run takes 22.81 user CPU seconds, versus 126.63 before, but that ratio includes skipping malformed syntax. Its 18 diagnostics are 15 parse errors, two frontend errors, and one unchanged per-file unused declaration. Eleven former diagnostics on malformed `Runtime.zig` are not emitted. Project-wide non-use claims wait for complete syntax.
- The default-limit zmath run takes 3.84 user CPU seconds, versus 31.01 before, and retains 122 diagnostics. It emits 18 state-limit warnings. That ratio includes incomplete analyses, so the table uses the non-binding 1024-state control instead.

Raw timings, hardware counters, input hashes, diagnostics, and comparison records remain in `.tmp/perf2-*`. The performance controls do not change production defaults or exclude files from the full-corpus checks.

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
- The payload bound is not an RSS limit. Separately owned artifact allocations are outside it. Statistics count actual analysis runs.

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
