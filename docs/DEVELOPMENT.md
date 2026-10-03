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

## Performance measurement

The benchmark runner measures whatever source trees you name, and this checkout
is the only workload when you name none. Each extra workload is a `NAME=PATH`
pair. It requires Python 3, Linux `perf`, and GNU `time`. Runs are sequential,
use one worker and nice level 15, and leave analysis limits unchanged.

Freeze the inputs and retain the baseline executable before editing:

```bash
zig build -Doptimize=ReleaseSafe -j1
python3 scripts/benchmark.py snapshot .tmp/bench-inputs other=/path/to/project
cp zig-out/bin/zwanzig .tmp/bench-before
python3 scripts/benchmark.py run .tmp/bench-inputs .tmp/bench-before .tmp/bench-baseline
```

The snapshot includes Zig sources and root build/configuration files. Its manifest
records SHA-256 hashes. Zwanzig's own workload stays frozen while its implementation
changes. Existing snapshot and result directories are never overwritten. The runner
also rejects changes to the checkout configuration used for both executions.
Snapshots, manifests and result directories are measurement artifacts: keep them
out of version control, and publish only results whose workloads may be public.

Build the candidate with the same frontend and optimization mode, then compare:

```bash
zig build -Doptimize=ReleaseSafe -j1
python3 scripts/benchmark.py run .tmp/bench-inputs zig-out/bin/zwanzig .tmp/bench-candidate
python3 scripts/benchmark.py compare .tmp/bench-baseline .tmp/bench-candidate
```

Results include user and elapsed time, peak RSS, hardware counters, executable hash,
and JSON diagnostics, which now include `analysis-limit-exceeded` entries.
Comparison requires matching inputs, diagnostic multisets, and exit status.
Exit status 1 means diagnostics were reported or the run could not be trusted
as a complete analysis.

Profile long runs separately so sampling overhead does not affect the timing comparison:

```bash
python3 scripts/benchmark.py run .tmp/bench-inputs .tmp/bench-before .tmp/bench-profile \
  --profile --workloads other
perf report --stdio --no-children --max-stack 8 --call-graph none \
  -i .tmp/bench-profile/other/perf.data
```

Profiles use frame-pointer call chains. Self samples locate expensive functions;
inclusive samples (`--children`) trace their callers. Bound the displayed stack
depth when symbolization is slow. Do not add inclusive percentages from nested
functions. Repeat timings when needed; system load and CPU frequency can affect
a single measurement.

The comparison procedure and its caveats are in the
[performance measurements](internal/ADJUSTMENT_PLAN.md#performance-measurements).

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
