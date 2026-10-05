# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog 1.1.0](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Fixed

- Captured-error storage now suppresses `swallowed-error` only when every continuing handler path records the caught payload outside the handler. Partial, unreachable, local-only, and shadowed-payload stores no longer hide warnings.
- Fake or mutable `std.testing` namespace aliases no longer hide unused declarations through `refAllDecls` or `refAllDeclsRecursive`. Genuine immutable import and namespace aliases remain supported.
- Initialization methods now suppress `optional-unwrap` when the field is non-null at every successful exit, after their deferred writes run. A successful exit that carries no assignment, as in `self.value = load() catch return`, keeps the warning. A null-check-guarded conditional assignment proves the field; an assignment under a condition the analysis does not connect to it, a later reset, and a reset still pending in a `defer` do not.
- Deferred Zig 0.16 `close(io)` calls and pre-0.16 `close()` calls now release successful opens, including aliased APIs and catch-based acquisition. A handle from a nested `catch` fallback belongs to the arm that opened it, not to the primary call. Borrowed standard handles remain distinct from owned opens. (#60, #61, #62, #63, #84, #85)
- Returning arena-backed objects or pointer-preserving opaque casts no longer reports transferred allocations as leaked. A returned method parameter or receiver names the block the call site writes, so only a block that leaves the function carries the payload. (#59, #64)
- Optional field proofs now preserve executed lifecycle initialization and invalidation, generic constructor assignments, helper postconditions, and independent value copies. A pointer member a by-value copy carries still reaches the field it designates, and a call a helper makes on a foreign pointer can still clear what its callers proved. Unsafe sibling-field, reset, and mutation controls remain reported. (#66, #67, #68, #70)
- A forced unwrap inside a private helper or a private generic callback now uses the guards its callers establish. Every caller the analysis can attribute must establish the same field on the object it passes - resolved through the actual field captures and argument positions of a generic body - and a fallible initializer must succeed before the call. Every operand evaluated before the callee is entered counts, so an argument that clears the field still defeats the proof. A public, recursive, escaping, or rebound context keeps the warning. (#69)
- Verified error-tag whitelists now narrow their payload's optional field without accepting alternate tags or a payload that escapes to a call, an address, or a cast. (#74)
- Compile-time assertion guards no longer produce runtime dead-code warnings. Runtime constant and contradictory branches remain checked. (#80)
- Project-wide unused-declaration analysis now follows guarded root imports from reachable build modules without hiding unrelated unused declarations. (#65)
- Successful constructor values now retain optional field facts through nested owner wrappers without borrowing facts from unrelated initialized locals. (#71)
- Allocations through a caller's context field now share a verified caller arena lifetime. Every successful exit must release the arena or return its state by value. Late cleanup registration, local-arena pointers, and replaced allocator fields no longer hide leaks. Read-only calls and sibling-field writes keep the lifetime proof. (#82)
- Benchmark documentation now lists all matching workload, analyzer, execution, and completion checks required before comparing results. (#1)
- Type and import resolution now log the search and frame limit when a bounded walk stops early, instead of silently treating the result as unresolved. (#2)
- Recursive file discovery now skips current Zig cache layouts, dependency directories, and Git/Jujutsu metadata. Other hidden directories remain included, and explicit file or directory selections override exclusions. (#3)
- Repeated deterministic lookups over verified retained rows now keep their non-null proof. Buffer, count, and input mutations remain reported, and a shape this proof does not model keeps the plain unwrap warning. (#4, #73)
- Field assertions now survive writes to independent local values and slice headers without treating writes through elements or pointer fields as disjoint. A write through a pointer or an optional pointer field still reaches the field it names, while a write to an independent by-value sibling field stays quiet. (#44)
- Allocation failures during frontend generation, metadata extraction, and duplicate-import reporting now propagate without leaking partial results or silently dropping findings. (#57)
- Default dataflow analysis now preserves resource ownership and possible-zero values across acyclic branch joins. Loop widening remains enabled; joins no longer hide leaks or possible division by zero. (#21, #25)
- Assigning a variable now retires the branch facts that named it, so a guard read before the write no longer pins the path to a value it can no longer take, and branches the assignment reopens are explored again. Interval widening keeps a bound that did not move and throws only a bound that moved, so a growing counter keeps its starting value as a lower bound and bounded-loop conditions stay decidable.
- Labeled block exits now retain their branch constraints and execute reached scope defers before the jump. Guarded division stays quiet; break operands and deferred zero assignments remain checked. (#25)
- Syntax errors now produce `parse-error` diagnostics without stopping analysis of valid sibling files. Failed type preflight reports `frontend-error`, skips required typed checks, and preserves optional AST fallback.
- A file with a syntax error now reports that Zwanzig skipped all other checks on it. The parse errors alone no longer leave the user reading the file as clean. Valid sibling files keep their findings.
- An analysis that stops at a configured worklist or state budget now reports `analysis-limit-exceeded` for the affected function, naming the limit and the value reached, instead of only logging a warning. Findings that need a complete dataflow analysis of that function are missing rather than absent, so the run can no longer exit 0 with suppressed results.
- Optional-unwrap proofs now inspect every block statement. Assignments and mutations after statement 64 no longer cause false warnings or hide unsafe unwraps. Ordinary blocks borrow the AST statement slice without allocation or copying.
- Verified standard-library ArrayList length guards now cover declared local, parameter and struct-field receivers. Mutation checks preserve independent value-copy headers but follow pointer-field, transitive and rebound aliases at each mutation site. A nested loop that drains the guarded list still reports at the unwrap, however large the enclosing condition proved the bound, and the guarded pop does not invalidate its own proof. (#72)
- Optional-unwrap proofs distinguish writes deferred until the current scope exits from writes that already ran in nested scopes. Receiver calls invalidate guards only after their receiver and arguments are evaluated; reassigning an alias slot does not count as a write through the old alias.
- Lazy-init optional guards now account for writes deferred until the branch exits, including aliased and callee writes. A later assignment cannot restore a non-null proof that a pending defer will invalidate. Normal-exit errdefers and unrelated writes remain safe.
- Budget-exhaustion diagnostics transfer ownership of their formatted messages without leaking or making a second allocation.
- A selection that resolves to no `.zig` files now exits 1 and reports `Error: No .zig files found. Nothing was analyzed.` instead of exiting 0 with no report.
- Unknown `--` options are now rejected. A mistyped flag previously ran a different analysis than the one requested, and the `--flag=value` form was silently dropped and then treated as a path.
- Rule names that no rule or checker is registered under are now rejected, whether they came from `--do`, `--skip`, or a config file's `enabled_rules`/`disabled_rules`. A mistyped name previously selected nothing and the run then printed `No issues found.` and exited 0 for an analysis that never happened; the name is now named in the error. Allowlist and denylist semantics for names that resolve are unchanged, as is the default filter.
- An unparsable build script now reports its own `parse-error` diagnostics. Project-wide `unused-decl` analysis cannot prove the absence of cross-file references without complete syntax, so it still skips, but the reason is now visible instead of silently removing project-wide dead-code detection.
- Fixed missed divide-by-zero and unreachable-branch diagnostics under supported integer and immutable scalar guards. Floating-point and wider integer domains remain conservative. Function summaries now preserve both success and error paths, including pending caller errors.
- Fixed state limits across call contexts. Analysis now stops an incomplete function run instead of exceeding the cap. Independent constant-condition checks still report.
- Fixed thread-limit and shutdown behavior on both frontends. `--threads` includes the calling thread, and executor shutdown waits for submitted work.
- Fixed analysis ownership and allocation-failure handling, warm-cache declaration annotations, and reference lookup through valid alias cycles. Malformed source no longer enters semantic indexes.
- Fixed false `unused-decl` reports for contextual constants such as `.empty` in typed initializers, assignments, and returns, without hiding unused constants in unrelated containers.
- Fixed false project-wide `unused-decl` reports caused by missing references in malformed source or build files. Per-file checks still run on valid sibling files.
- The default macOS development shell now uses Zig 0.16.0, avoiding the Zig 0.15.2 toolchain failure with current SDKs while retaining an explicit compatibility shell for the older frontend.
- Fixed false positives for imported namespace and file-struct aliases, private file-as-struct methods, parameter uses in nested expressions, and allocator cleanup identity. Explicit `const Name: type = ...` aliases and functions declared to return `type` use PascalCase. Comptime parameters referenced from fields or methods of returned anonymous containers count as used.
- Fixed identifier-style false positives for type-valued expressions, standard-library type factories with literal arguments, and optional type-information payloads. `@typeInfo` result values still require snake_case.
- Type-valued labeled blocks keep PascalCase only when every reachable exit yields a type and each break targets that block. Value, mixed, fall-through, and cyclic cases remain conservative. (#78)
- Namespace member type aliases and `@typeInfo(T).pointer.child` keep their type naming rules. Member values, including base64 encoder/decoder objects and flag fields, keep snake_case. (#76, #77, #79)
- Fixed false positives for intentional catch fallback expressions and captured-error storage, while unrelated catch assignments remain reported as swallowed errors.
- Catch handlers that return a boolean rejection or an updated failure count no longer warn as swallowed errors. Resets, shadowed or escaped result bindings, and zero or unknown counter updates remain reported. (#81)
- Fixed `sentinel-alloc` false positives when an untyped local directly infers the sentinel slice returned by the allocation.
- Fixed project `unused-decl` false positives for method references through inline namespaces and nested type aliases.
- Fixed stack overflows when the Zig 0.16.0 frontend analyzes generic container parameters or `unused-decl` follows cyclic aliases and namespace imports.
- Fixed excess analysis concurrency with `--threads 1` on Zig 0.16.0 and double-free failures when the analysis graph runs out of memory.
- Fixed optional-unwrap false positives after field assertions and calls that write a different struct field. Self-lint now reports failures in CI.
- A release wrapper is now recognized when the callee leaves a leading parameter unnamed, as `closeDir(_: *Context, directory: *Directory)` does. A `compat`-style directory handle closed that way is no longer reported as leaked, while a wrapper that closes behind a branch, closes a second resource field, or is only named like a close still is.
- Returning a member of a declared error set (`return ConfigError.InvalidConfigFormat;`) now takes the error path, so the `errdefer` cleanup for that path runs and resources still live on it are no longer reported as leaked. Modeling that path also exposed a real double free in this project's own escape-model parser, where an error return freed a slice its `errdefer` frees again; the redundant frees are gone.
- Storing a value into an aggregate no longer lets that value escape. A returned aggregate keeps the payload resources handed to it, and a store that cannot be proven to land in a fresh slot - a cursor that advances by zero, a constant index, a later write through the aggregate, or an aggregate that is replaced - keeps reporting the dropped payload.
- Returning or assigning a successful `realloc` result now preserves ownership of the replacement. Each arm of a `catch` chain around a resize names its own producer, so a fallback that is not a resize leaves the block handed to the primary resize live. Discarded and unreleased replacements still report leaks; a failed resize leaves the original allocation owned by the registered error cleanup, or by the caller it is handed to. (#83)
- A `type` annotation on an alias now describes the type value the alias holds instead of the instances that value names, so `const Height: type = ?u32` and every alias chain ending in one stay optional. Writing such a value into a field, or dereferencing a pointer to that alias, no longer counts as a non-null installation, while a real `u32`, `*u32` or struct installer still does. Literal types are matched through the container-declaration nodes they are actually spelled with, so a `.{ ... }` value literal is no longer mistaken for a type declaration.
- Storing through a cast or helper-returned pointer no longer reports the returned payload as leaked, and neither does storing through a field the destination's own declaration filled with a pointer. Dropped destinations and stores into a slot whose pointee type cannot be read still report. A store into a bare binding to a scalar pointee hands that block nothing to own, and that holds when the slot leaves its pointee type to be read from the `create` allocation. A store through a parenthesised pointer expression no longer aborts the analysis.
- Returning a failed `realloc` through a `catch` fallback no longer hides the original allocation, and a caught error returned to the caller now runs the cleanup registered for that error path. (#83)
- A payload captured by a `while` header now counts as a null check on the condition it reads, so a handle caught that way and released inside the body no longer reports as leaked where the function returns. The same capture on an `if` is unchanged.
- A store written as a loop continuation step or as a compound assignment now moves what it writes. A payload such a store hands to a block the function returns no longer reports as leaked, and its own operands no longer report a use-after-free against blocks the store has already handed over.
- A null check in the same function no longer proves a forced unwrap past a mutation written ahead of it in the same statement. A tuple element or a call argument that clears the field before the `.?` reads it now reports `optional-unwrap`; a mutation written behind the unwrap and a deferred clear still stay quiet.
- Replacing a whole aggregate now reports one loss instead of two. When nothing names the aggregate after the assignment, the replacement is what `store-violations-engine` reports and the payload it carried goes with that block, rather than the payload also being claimed as dropped.
- `_ = x;` now keeps no name for the resource it discards. A binding that a loop re-declares on its next pass no longer hands its still-held block to the discard, so a handle the same pass releases is no longer reported as leaked at the discard.
- A labeled break is now matched to its block by name rather than by where the label was written, so a `break :label` above a cleanup registration ends the scope the cleanup was written in. A handle that cleanup releases no longer reports as leaked.
- A loop whose condition a counter proves on entry now closes its exit edge, so the pass that never runs no longer reaches the code below it. A comparison between two counters, or a bound not spelled as a literal, still leaves both edges open.
- An unlabeled `break` now leaves the loop the same way a labeled one does, unwinding the defers its path reached on the way out. A division behind such a break that the loop guard proves safe is no longer reported; break operands and deferred zero assignments remain checked.
- A `zwanzig-disable*` comment now suppresses the line it was written for even when an empty `//` comment appears earlier in the file.

### Changed

- Enabled checks now control type preflight and project preparation. Compatible checkers reuse per-file analysis, while `empty-catch-engine` runs only structural checks unless state visualizations are requested. Analysis statistics count actual engine runs.
- `just build`, `just run`, and `just lint` now use ReleaseSafe to avoid Debug analysis overhead while retaining safety checks. Self-lint uses one worker.
- Reduced repeated type resolution and import-path normalization during path-sensitive analysis, without lowering analysis limits or disabling runtime safety checks.
- Reduced optional-unwrap guard and engine setup costs by sharing syntax indexes and parent maps. Import lookup now uses the project index while preserving first-match behavior.
- Reduced single-file type and resource lookup costs and memory used by path-sensitive snapshots. Analysis reuses syntax indexes and copies only live constraints and call sites, without changing analysis limits or runtime safety checks.

### Added

- A reproducible benchmark runner freezes the source trees you name, defaults to Zwanzig's own sources, and compares diagnostic multisets, exit status and analysis-limit warnings exactly between two runs.
- Conditional constructor field proofs now support private factories without rejecting unrelated public functions or function addresses. Nullable alternatives, public factories, guarded-field resets, and container escapes remain reported. (#70)
- Added `optional_unwrap_test_severity` to select hint, warning, or error severity for forced unwraps in test bodies. Production and nested helper warnings, other rule severities, and diagnostic exit status are unchanged. (#75)

## [0.15.1]

### Fixed

- macOS ARM64 release builds embedding Zig 0.15.2 now use a compatible SDK. ([ziglang/zig#31756](https://codeberg.org/ziglang/zig/issues/31756))

## [0.15.0]

### Added

- `--version` now reports the embedded Zig frontend version. (PR #109)
- A reproducible Zig 0.16.0 development shell and migration compatibility inventory are now available. (PR #110)
- Source builds now support both Zig 0.15.2 and Zig 0.16.0 frontends, with the selected frontend reported by `--version`. (PR #111; follow-up to PR #110)
- Release archives are now published for both Zig 0.15.2 and Zig 0.16.0 frontends, with the frontend version included in each asset name. (PR #115)

### Changed

- README installation instructions now cover release binaries, Zig build dependencies, and GitHub Actions usage. (PR #103)
- Dual-frontend release artifacts are maintained through v0.17.x; v0.18.0 is planned as the first release without a Zig 0.15.2 artifact. (PR #116)

### Fixed

- `--target` no longer crashes after successful analysis when the target triple contains an ABI. (PR #103)
- Typed (ZIR-based) analysis is now explicitly disabled for files the embedded Zig frontend cannot compile, instead of silently producing incomplete type information. (PR #109)
- Analysis cache entries are no longer shared between zwanzig binaries embedding different Zig frontend versions. (PR #109)

## [0.14.0] - 2026-06-01

### Changed

- Shared project-aware import and call resolution across resource, stack-escape, sentinel allocation, and cleanup lifecycle checks, improving precision for identifier calls, typed receivers, FQNs, field-chain receivers, and result-location contexts (#92).

## [0.13.1] - 2026-06-01

### Added

- `unused-decl` now runs a project-wide pass by default when more than one file is analyzed, reporting public top-level declarations unreferenced by any other analyzed file. Package entrypoints, alias-style public API exports, and declarations exposed through a used declaration's type, signature, field, or initializer are excluded to reduce false positives. Package roots are auto-discovered from `build.zig` `root_source_file` entries, and typed receiver and result-location method calls are recognized across files (#91).

## [0.12.2] - 2026-05-27

### Changed

- Per-file scratch now uses libc's allocator instead of an arena over the page allocator. The engine eagerly frees its temporaries, so the arena was retaining roughly an order of magnitude more memory than the analyzer's actual working set. On engine-heavy inputs (notably `0.12.x` after `defer-frees-escapee` landed) this could push peak RSS into multi-GB territory and OOM on CI runners with limited memory (#89).

## [0.12.1] - 2026-05-26

### Fixed

- `store-violations` no longer flags slices returned directly from `appendSlice` as escapes — they are treated as copies (#86).

## [0.12.0] - 2026-05-26

### Added

- New `defer-frees-escapee` rule that detects allocations freed by `defer` while still escaping the function (#79).
- CFG construction now visits `switch` arms, improving coverage for engine-based checkers (#79).

### Changed

- Skip inlining of recursive calls during engine analysis for faster runs on recursive code (#79).
- Build script auto-detects the active macOS SDK via `xcrun` when applying the Zig 0.15.2 macOS link workaround (#82).

### Fixed

- `ExplodedGraph.addEdge` deduplicates edges and remains atomic under allocation failure (#83).

## [0.11.0] - 2026-02-24

### Added

- New `deinit-lifecycle` rule that detects misuse of `deinit` and other cleanup methods, including missing or duplicate calls and reinitialization after cleanup (#72).

## [0.10.0] - 2026-02-20

### Added

- New `slice-bounds-engine` checker for path-sensitive array and slice out-of-bounds detection, including definite and possible OOB access, negative indices, and tracking of array/string literal lengths (#70).

## [0.9.0] - 2026-02-16

### Added

- New `divide-by-zero` engine checker (#67).

### Fixed

- Deduplicate diagnostics that previously appeared multiple times across inlined functions in the store-violations engine (#63).
- Recognize `.call_comma` in `resolveFunctionCall`, fixing missed call sites.

## [0.8.1] - 2026-02-04

### Fixed

- Four engine correctness bugs in the analysis engine (#60).
- `unreachable-code` no longer treats float literals as parseable const ints.
- `optional-unwrap` now treats `debug.assert` as a null-guard.

## [0.8.0] - 2026-02-04

### Added

- New `return-local-ptr` rule that detects functions returning pointers to local stack values (#58).

## [0.7.0] - 2026-02-03

### Added

- `free_owned` ownership model with sentinel-aware typing, improving store-violation precision on owned/freed allocations (#56).

## [0.6.0] - 2026-02-03

### Added

- New `stack-escape-engine` checker that detects stack escapes through spawned threads (#54).

### Changed

- Diagnostic JSON output now uses `std.json` for serialization.

### Fixed

- Cached CFG artifacts are correctly wired through the analysis pipeline (#53).

## [0.5.1] - 2026-02-02

### Changed

- Avoid ZIR lookup for local identifiers, reducing analysis overhead (#51).

### Fixed

- Improved fallback handling for local error-union types (#51).

## [0.5.0] - 2026-02-02

### Changed

- Typed IR is now always on; the previous toggle has been removed (#47).
- Core modules and `optional-unwrap` helpers were split for clearer module boundaries (#48).

### Fixed

- `optional-unwrap` now traverses callee unwraps and applies improved guard recognition (#48).

## [0.4.0] - 2026-02-02

### Added

- New `optional-unwrap` rule that flags forced `.?` unwrapping, with guard-aware analysis to reduce false positives — covers `if`/`if_simple`, `orelse`, early-exit, labeled-block, `try`, `catch`, and `debug.assert` patterns (#44, #45, #46).

## [0.3.0] - 2026-02-01

### Added

- Parallel file analysis with a new `--threads` CLI option and deterministic diagnostic ordering across threads.
- New `unused-parameter` rule.
- New `sentinel-alloc` rule (disabled by default) for sentinel-terminated allocation bugs.
- New `unreachable-code-engine` checker for path-sensitive dead-code detection.
- New `store-violations` engine and checker with ownership and store modeling.
- Type-aware checks added to `identifier-style` and `unused-decl` rules.
- SARIF output format and richer text output with source pointers.
- CFG and lattice-flow visualization via DOT output, with boolean value tracking and const flag detection.

### Changed

- Widening is now enabled by default for engine convergence.
- Default rule filtering: when no config or `--do`/`--skip` flag is present, `sentinel-alloc` is blocklisted.

### Fixed

- No more false-positive leak diagnostics at inlined function exits (#41).
- `unused-parameter` correctly handles generic parameters (#39).
- Cache keys use a deterministic rule order.

## [0.2.4] - 2026-01-25

### Fixed

- `release-check.sh` uses `grep` instead of `rg` for portability in CI environments.

## [0.2.3] - 2026-01-25

### Fixed

- Enforce `release-check` validation in the release workflow.

## [0.2.2] - 2026-01-25

### Changed

- `identifier-style` rule aligned with Zig naming guidance: types vs. values vs. external conventions clarified; `SCREAMING_SNAKE_CASE` restricted to external-convention aliases (#22).

### Fixed

- `identifier-style` treats `if`-expressions yielding types as type aliases and no longer misclassifies call-result types.

## [0.2.1] - 2026-01-24

### Fixed

- Refined `@typeInfo` alias checks and identifier-style type-alias detection.

## [0.2.0] - 2026-01-24

### Added

- Inline comment-based suppression of diagnostics (#16).

## [0.1.1] - 2026-01-24

### Fixed

- Updated `setup-zig` action to v2 in the release workflow (#15).

## [0.1.0] - 2026-01-24

### Added

- Initial release: Zig static analyzer MVP with the `empty-catch` rule, rule-selection flags, and source parsing cache.

[Unreleased]: https://github.com/forketyfork/zwanzig/compare/v0.14.0...HEAD
[0.14.0]: https://github.com/forketyfork/zwanzig/compare/v0.13.1...v0.14.0
[0.13.1]: https://github.com/forketyfork/zwanzig/compare/v0.12.2...v0.13.1
[0.12.2]: https://github.com/forketyfork/zwanzig/compare/v0.12.1...v0.12.2
[0.12.1]: https://github.com/forketyfork/zwanzig/compare/v0.12.0...v0.12.1
[0.12.0]: https://github.com/forketyfork/zwanzig/compare/v0.11.0...v0.12.0
[0.11.0]: https://github.com/forketyfork/zwanzig/compare/v0.10.0...v0.11.0
[0.10.0]: https://github.com/forketyfork/zwanzig/compare/v0.9.0...v0.10.0
[0.9.0]: https://github.com/forketyfork/zwanzig/compare/v0.8.1...v0.9.0
[0.8.1]: https://github.com/forketyfork/zwanzig/compare/v0.8.0...v0.8.1
[0.8.0]: https://github.com/forketyfork/zwanzig/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/forketyfork/zwanzig/compare/v0.6.0...v0.7.0
[0.6.0]: https://github.com/forketyfork/zwanzig/compare/v0.5.1...v0.6.0
[0.5.1]: https://github.com/forketyfork/zwanzig/compare/v0.5.0...v0.5.1
[0.5.0]: https://github.com/forketyfork/zwanzig/compare/v0.4.0...v0.5.0
[0.4.0]: https://github.com/forketyfork/zwanzig/compare/v0.3.0...v0.4.0
[0.3.0]: https://github.com/forketyfork/zwanzig/compare/v0.2.4...v0.3.0
[0.2.4]: https://github.com/forketyfork/zwanzig/compare/v0.2.3...v0.2.4
[0.2.3]: https://github.com/forketyfork/zwanzig/compare/v0.2.2...v0.2.3
[0.2.2]: https://github.com/forketyfork/zwanzig/compare/v0.2.1...v0.2.2
[0.2.1]: https://github.com/forketyfork/zwanzig/compare/v0.2.0...v0.2.1
[0.2.0]: https://github.com/forketyfork/zwanzig/compare/v0.1.1...v0.2.0
[0.1.1]: https://github.com/forketyfork/zwanzig/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/forketyfork/zwanzig/releases/tag/v0.1.0
