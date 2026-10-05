# Development notes

## Zig toolchains

The default development shell uses Zig 0.16.0:

```bash
nix develop
```

The compatibility shell uses Zig 0.15.2:

```bash
nix develop .#zig015
```

Run `just test` and `just lint` in both shells when changing code that touches the embedded frontend or its compatibility adapters.

`just build` and `just run` use `ReleaseSafe`. `just test` retains Debug checks.
`just lint` uses a ReleaseSafe analyzer and one analysis worker to limit CPU load.
Use `zig build` directly when you need a Debug executable.

## Fixture compilation

`just ci` runs `check-fixtures`, which compiles every fixture named in the
directory list in `build.zig`. The fixture tests read fixtures as text and
compare diagnostic rows, so they pass on code the frontends reject. This step
is the only gate that compiles the fixtures, and a fixture that stops
compiling fails it. Run it in both shells while you work:

```bash
nix develop -c zig build check-fixtures
nix develop .#zig015 -c zig build check-fixtures
```

Add every new fixture directory to the list in `build.zig`. A directory the
list omits is never compiled.

A fixture compiles on both frontends unless it names the one it targets:

```zig
// EXPECT: none
// Zig 0.16.0 fixture: the `Io` spellings below do not exist in Zig 0.15.2.
```

The marker line goes directly under the `EXPECT` row and names the only
frontend whose standard library the fixture builds against. The check compiles
the fixture on that frontend and skips it on the other one.
`// Zig 0.15.2 fixture:` is the same marker for the compatibility shell. A file
that carries both markers stops the build, because the two lines contradict
each other.

A fixture that cannot compile on either frontend is not broken. It carries the
not-a-program marker instead:

```zig
// EXPECT: none
// zwanzig: not a standalone program: Zig rejects these underscore-prefixed
// shadows as compile errors regardless of the analyzer's opinion.
```

The marker line goes under the `EXPECT` row, like the per-frontend markers. It
tells the gate to skip the file on every frontend, because the invalidity is
the thing the rule exists to detect: an import of a module that does not exist
on disk, a shadowed declaration, an unreachable statement. 40 fixtures carry
the marker today, against 8 that carry a per-frontend one.

The reason is part of the marker, not a comment. An empty reason stops the
build, and the reason has to say the same thing the fixture asserts. A fixture
whose `EXPECT` row pins a diagnostic describes the invalidity as the
intentional subject under test. A fixture whose row reads `EXPECT: none`
describes a construct the frontend rejects regardless of the analyzer's
opinion; a reason that claims the rule fires on such a fixture contradicts the
row it sits next to.

A per-frontend marker and the not-a-program marker on one file is the third
build error, after two per-frontend markers and an empty reason. The two say
contradictory things: one asks the gate to compile the file on exactly one
frontend, the other asks it never to compile it. Each fixture states exactly
one of the three.

Fixtures may also declare analyzer settings inline:

```zig
// CONFIG: {"resource_models":[{"kind":"open","method_name":"acquire"}]}
// EXPECT: rule=store-violations-engine severity=error message=resource leak
```

Only the fixture test harness reads that line. The CLI configures itself from a
config file and never parses `// CONFIG:` out of the sources it analyzes, so a
fixture that declares its resource models or escape models inline reports
nothing under a bare CLI run. Pass the same models through `--config` to
reproduce what the harness sees:

```bash
zwanzig --config models.json test/fixtures/store_violations_engine
```

That is the contract. The inline line configures the harness, and a CLI run
gets the same models from a file.

## Performance measurement

The benchmark runner measures whatever source trees you name, and this checkout
is the only workload when you name none. Each extra workload is a `NAME=PATH`
pair. It requires Python 3, Linux `perf`, and GNU `time`. Runs are sequential,
use one worker and nice level 15, and leave analysis limits unchanged.

Set `BENCH_ROOT` to a new directory on local storage outside the checkout.
Keep toolchain caches, temporary files, snapshots, and results there.
Freeze the inputs and retain the baseline executable before editing:

```bash
mkdir -p "$BENCH_ROOT/tmp"
export TMPDIR="$BENCH_ROOT/tmp" TMP="$BENCH_ROOT/tmp" TEMP="$BENCH_ROOT/tmp"
export ZIG_LOCAL_CACHE_DIR="$BENCH_ROOT/cache/local"
export ZIG_GLOBAL_CACHE_DIR="$BENCH_ROOT/cache/global"
zig build -Doptimize=ReleaseSafe --prefix "$BENCH_ROOT/before" -j1
python3 scripts/benchmark.py snapshot "$BENCH_ROOT/inputs" other=/path/to/project
python3 scripts/benchmark.py run "$BENCH_ROOT/inputs" "$BENCH_ROOT/before/bin/zwanzig" "$BENCH_ROOT/baseline"
```

The snapshot includes Zig sources and root build/configuration files. Its manifest
records SHA-256 hashes. Zwanzig's own workload stays frozen while its implementation
changes. Existing snapshot and result directories are never overwritten. The runner
also rejects changes to the checkout configuration used for both executions.
Snapshots, manifests and result directories are measurement artifacts: keep them
out of version control, and publish only results whose workloads may be public.

Build the candidate with the same frontend and optimization mode, then compare:

```bash
zig build -Doptimize=ReleaseSafe --prefix "$BENCH_ROOT/after" -j1
python3 scripts/benchmark.py run "$BENCH_ROOT/inputs" "$BENCH_ROOT/after/bin/zwanzig" "$BENCH_ROOT/candidate"
python3 scripts/benchmark.py compare "$BENCH_ROOT/baseline" "$BENCH_ROOT/candidate"
```

Results include user and elapsed time, peak RSS, hardware counters, executable hash,
and JSON diagnostics, which now include `analysis-limit-exceeded` entries.
Comparison requires matching input paths and manifests, workload sets, analyzer
version, profiling mode, thread count, and scheduling priority. Diagnostic
multisets, exit status, and analysis-limit-warning multisets must also match.
Exit status 1 means diagnostics were reported or the run could not be trusted
as a complete analysis.

Profile long runs separately so sampling overhead does not affect the timing comparison:

```bash
python3 scripts/benchmark.py run "$BENCH_ROOT/inputs" "$BENCH_ROOT/before/bin/zwanzig" "$BENCH_ROOT/profile" \
  --profile --workloads other
perf report --stdio --no-children --max-stack 8 --call-graph none \
  -i "$BENCH_ROOT/profile/other/perf.data"
```

Profiles use frame-pointer call chains. Self samples locate expensive functions;
inclusive samples (`--children`) trace their callers. Bound the displayed stack
depth when symbolization is slow. Do not add inclusive percentages from nested
functions. Repeat timings when needed; system load and CPU frequency can affect
a single measurement.

The comparison procedure and its caveats are in the
[performance measurements](internal/ADJUSTMENT_PLAN.md#performance-measurements).

Alternate baseline and candidate runs when you repeat the comparison.
Keep the frontend, target, build mode, CPU affinity, and inputs fixed.
Report medians and instruction counts, not only one elapsed-time result.
Use a separate local Zig cache for each source checkout.
Verify the executable's debug source paths before measuring checkout variants.
Measure allocation behavior separately because profilers add overhead.
Valgrind Massif with `--pages-as-heap=yes` measures mapped pages, not requested allocation bytes.

Single-file type, resource, and reference queries reuse source-owned syntax indexes.
Indexed `@This` queries follow container parents instead of scanning every AST node.
Queries retain the unindexed path when an index is unavailable.

Engine snapshots copy only live constraints and call sites, not unused list capacity.
Exact-size copies can need another allocation when a branch appends an item.
Measure the full analysis to include this cost.
These changes retain analysis limits and runtime safety checks.

## Formatting

Zig 0.15.2 is the sole canonical formatter. Format and check source files
from the compatibility shell:

```bash
nix develop .#zig015 -c zig fmt src
nix develop .#zig015 -c zig fmt --check src/
```

The default Zig 0.16.0 shell validates the current frontend. It does not
establish a competing formatting baseline; `just lint` checks formatting only
when run in the Zig 0.15.2 compatibility shell.

## macOS SDK workaround

On current macOS hosts the active `MacOSX.sdk/usr/lib/libSystem.tbd` can advertise only `arm64e-macos`, so Zig 0.15.2 cannot link the build runner and emits a long list of undefined libSystem symbols (`__availability_version_check`, `_realpath$DARWIN_EXTSN`, etc.). Upstream tracker: <https://codeberg.org/ziglang/zig/issues/31756>.

`flake.nix`'s Darwin shell hooks source `scripts/setup-macos-sdk-workaround.sh`, which checks the SDK stub directly and, when the compatible `MacOSX15.4.sdk` is installed, materializes a fake `DEVELOPER_DIR` under `.tmp/macos-sdk-workaround` that points at it. A narrow `xcrun --sdk macosx --show-sdk-path` shim is prepended to `PATH` so Zig's internal SDK lookup picks up the same path. The helper is a no-op when the active stub is compatible, when the legacy SDK is missing, or on non-Darwin systems. The default shell uses Zig 0.16.0, while the `zig015` shell retains the legacy frontend.

Remove the script and the corresponding `flake.nix` lines once upstream resolves the arm64e-only stub regression.

## Architecture

Main components:

- `cli/` - CLI parsing, config merge, default registry, and run loop
- `main.zig` - CLI entrypoint that delegates to `cli/run.zig`
- `analyzer.zig` - File reading, rule/checker execution, and result collection
- `formatters/` - Output formatters (console, SARIF)
- `source.zig` - Lazy AST/token parsing with caching
- `diagnostic.zig` - Diagnostic model with severity and locations
- `rule.zig` - Rule interface for AST-based checks
- `checker.zig` - Checker interface for AST/CFG-based analysis
- `rules/` - Individual rule implementations
- `checkers/` - Checker implementations (AST and engine-backed)
- `cfg.zig` / `cfg/` - CFG facade and modular CFG builder/graph/dot code
- `engine.zig` / `engine/` - Engine facade and modular analysis/state/value code
- `zir_bridge.zig` / `zir/` / `types/` - ZIR bridge and type info plumbing
- `file_discovery.zig` - Recursive file discovery
- `lib.zig` - Public library exports for embedding

## Parsing cache

Parsing is lazy and cached. Each file is parsed at most once, regardless of how many rules inspect it.

## Diagnostics

Each diagnostic includes severity (`hint`, `warning`, `err`), precise location, and the rule that found it:

```
file.zig:5:10: warning: [empty-catch-engine] Empty catch block
```

## Adding new rules

1. Create `src/rules/my_rule.zig`
2. Implement the `Rule` interface
3. Register in `src/cli/registry.zig` (for the CLI)

Example:

```zig
const std = @import("std");
const Rule = @import("../rule.zig").Rule;
const RuleError = @import("../rule.zig").RuleError;
const Diagnostic = @import("../rule.zig").Diagnostic;
const Source = @import("../source.zig").Source;

pub const MyRule = struct {
    pub const rule: Rule = .{
        .name = "my-rule",
        .checkFn = check,
    };

    fn check(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
    ) RuleError!void {
        const ast = try src.ast();
        // Analyze the AST and append to diagnostics...
        _ = allocator;
        _ = ast;
    }
};
```

For CFG-based checkers, see `src/checkers/` for examples.

For more detail, see docs/IMPLEMENTATION.md.
