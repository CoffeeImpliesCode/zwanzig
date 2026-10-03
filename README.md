# zwanzig

[![Build status](https://github.com/forketyfork/zwanzig/actions/workflows/build.yml/badge.svg)](https://github.com/forketyfork/zwanzig/actions/workflows/build.yml)
[![MIT License](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)
[![Zig](https://img.shields.io/badge/language-Zig-f7a41d.svg)](https://ziglang.org/)

Zwanzig is a static analyzer and linter for Zig code, combining fast AST/token rules with CFG-driven analysis built on ZIR output.

## Installation and usage

### Release binary

Download the archive for your platform from the [latest release](https://github.com/forketyfork/zwanzig/releases/latest):

| Platform | Embedded frontend | Archive |
| --- | --- | --- |
| Linux x86_64 | Zig 0.15.2 | `zwanzig-vX.Y.Z-zig-0.15.2-linux-x86_64.tar.gz` |
| Linux x86_64 | Zig 0.16.0 | `zwanzig-vX.Y.Z-zig-0.16.0-linux-x86_64.tar.gz` |
| macOS ARM64 | Zig 0.15.2 | `zwanzig-vX.Y.Z-zig-0.15.2-macos-aarch64.tar.gz` |
| macOS ARM64 | Zig 0.16.0 | `zwanzig-vX.Y.Z-zig-0.16.0-macos-aarch64.tar.gz` |
| Windows x86_64 | Zig 0.15.2 | `zwanzig-vX.Y.Z-zig-0.15.2-windows-x86_64.zip` |
| Windows x86_64 | Zig 0.16.0 | `zwanzig-vX.Y.Z-zig-0.16.0-windows-x86_64.zip` |

Extract the archive and either add its directory to `PATH` or invoke the executable directly:

```bash
./zwanzig src/
```

On Windows, run `.\zwanzig.exe src\` instead.

### Zig frontend compatibility

Zwanzig embeds the Zig frontend used to build it. Source builds support Zig 0.15.2 and Zig 0.16.0, and select the matching compatibility layer automatically. Release archive names include the embedded frontend version, so choose the `zig-0.15.2` archive for a Zig 0.15.2 project and the `zig-0.16.0` archive for a Zig 0.16.0 project. Run `zwanzig --version` to verify which frontend a binary contains.

The two frontend artifacts are maintained through the v0.17.x release line.
v0.18.0 is the first planned release without a Zig 0.15.2 artifact; users on
Zig 0.15.2 should stay on the latest v0.17.x release.

To build from source with the 0.16.0 frontend, use the default shell:

```bash
nix develop -c just build
```

To build with the 0.15.2 frontend, select the compatibility shell:

```bash
nix develop .#zig015 -c just build
```

### Zig build dependency

Pin Zwanzig as a dependency in your Zig project. This command adds the dependency URL and content hash to `build.zig.zon`:

```bash
zig fetch --save=zwanzig https://github.com/forketyfork/zwanzig/archive/refs/tags/v0.15.1.tar.gz
```

Add a lint step to `build.zig`:

```zig
const zwanzig = b.dependency("zwanzig", .{
    .target = b.graph.host,
    .optimize = .ReleaseFast,
});
const run_zwanzig = b.addRunArtifact(zwanzig.artifact("zwanzig"));
run_zwanzig.addArgs(&.{"src"});

const lint_step = b.step("lint", "Run Zwanzig");
lint_step.dependOn(&run_zwanzig.step);
```

`b.graph.host` builds Zwanzig for the machine running the build, including when your project targets another platform. `ReleaseFast` avoids the substantial overhead of running the analyzer in Debug mode.

Run the new step with:

```bash
zig build lint
```

### GitHub Actions (SARIF)

Download a pinned release binary before running Zwanzig. The example selects the Zig 0.15.2 frontend; set `ZWANZIG_ZIG_FRONTEND` to `0.16.0` for a Zig 0.16.0 project. The Linux runner is x86_64, so it uses the Linux x86_64 archive:

```yaml
name: Zwanzig

on:
  push:
  pull_request:

permissions:
  contents: read
  security-events: write

env:
  ZWANZIG_VERSION: v0.15.1
  ZWANZIG_ZIG_FRONTEND: 0.15.2

jobs:
  analyze:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v7

      - name: Install Zwanzig
        run: |
          archive="zwanzig-${ZWANZIG_VERSION}-zig-${ZWANZIG_ZIG_FRONTEND}-linux-x86_64.tar.gz"
          curl --fail --location --silent --show-error \
            "https://github.com/forketyfork/zwanzig/releases/download/${ZWANZIG_VERSION}/${archive}" \
            --output "${RUNNER_TEMP}/${archive}"
          mkdir -p "${RUNNER_TEMP}/zwanzig"
          tar -xzf "${RUNNER_TEMP}/${archive}" -C "${RUNNER_TEMP}/zwanzig"
          echo "${RUNNER_TEMP}/zwanzig" >> "${GITHUB_PATH}"

      - name: Run Zwanzig analysis
        run: zwanzig --format sarif src/ > results.sarif || true

      - name: Upload SARIF results
        uses: github/codeql-action/upload-sarif@v4
        with:
          sarif_file: results.sarif
```

Pinning the version keeps CI reproducible. Update `ZWANZIG_VERSION` when you want to adopt a newer release. The `|| true` lets the SARIF upload run when Zwanzig reports diagnostics.

## Features

- Rule/checker registration with shared `--do`/`--skip` filtering
- Cached AST/tokens with syntax validation before checks
- Best-effort type-aware analysis via ZIR and project sources
- CFG-based, path-sensitive checkers with shared compatible analyses
- Graphviz DOT dumps for CFGs, exploded graphs, and path traces
- Parallel analysis across files

## Rules

AST/token rules:

- dupe-import: duplicate `@import` statements
- todo: `// TODO` comments
- file-as-struct: file naming based on struct-like top-level fields
- unused-decl: unused container-level declarations
- unused-parameter: unused function parameters
- unreachable-code: code after unconditional terminators or fully terminating branches
- empty-defer: empty `defer {}` blocks
- empty-errdefer: empty `errdefer {}` blocks
- shadowed-variable: name reuse across scopes
- sentinel-alloc: sentinel-terminated allocations losing sentinel type
- identifier-style: naming conventions for types/functions/values
- deinit-lifecycle: risky cleanup/reinit lifecycle patterns around `defer`/`errdefer`

Engine-backed checkers:

- unreachable-code-engine: constant-condition branches and proven contradictions under immutable scalar guards
- optional-unwrap: forced optional unwraps with `.?`
- empty-catch-engine: empty `catch {}` blocks
- swallowed-error: catch blocks that ignore errors without rethrowing or logging
- store-violations-engine: allocator/resource misuse (double-free, leaks, use-after-free/close)
- stack-escape-engine: stack-backed values escaping via return or async/thread capture
- divide-by-zero-engine: path-sensitive divide/modulo-by-zero detection
- slice-bounds-engine: array/slice out-of-bounds access detection

## Analysis behavior

Syntax errors produce `parse-error` diagnostics. Zwanzig skips checks for malformed files and continues with valid sibling files. Enabled native checkers control type preflight. If the embedded frontend rejects a file during that preflight, Zwanzig emits `frontend-error`. Required typed checks skip the file, while optional checks use AST fallback. AST-only selections avoid ZIR preflight.

`--threads` includes the calling thread on both frontends. Engine state caps include all call contexts at each program point. If analysis cannot continue within a cap, Zwanzig stops that function analysis and reports `analysis-limit-exceeded` for it. Independent constant-condition and structural checks can still report diagnostics.

An unknown option is an error rather than an ignored argument, and a selection that resolves to no `.zig` files exits 1 instead of reporting a clean run. Exit status 1 means diagnostics were reported or the run could not be trusted as a complete analysis; see [docs/USAGE.md](docs/USAGE.md) for the full table.

## Limitations

- Type queries are best-effort for module declarations, locals, parameters, nested scopes, and available project sources. Zwanzig does not perform complete compiler type resolution.
- Interprocedural execution supports simple direct calls within one file. Project-aware type and reference lookup does not execute cross-file calls.
- Path-sensitive unreachable reports require complete analysis and proof from immutable scalar enclosing guards. An absent graph node alone does not prove unreachable code.
- Integer guard refinement requires a proven domain that fits signed 64-bit values. Floating-point, unknown, and wider domains remain conservative.
- The disk cache reuses CFGs, not complete ZIR, typed metadata, function summaries, or diagnostics. Each run recomputes diagnostics.

## Docs

- Usage and CLI: [docs/USAGE.md](docs/USAGE.md)
- Configuration: [docs/CONFIG.md](docs/CONFIG.md)
- Output formats: [docs/OUTPUT.md](docs/OUTPUT.md)
- CI integration: [docs/CI.md](docs/CI.md)
- Inline suppressions: [docs/SUPPRESSIONS.md](docs/SUPPRESSIONS.md)
- Development notes: [docs/DEVELOPMENT.md](docs/DEVELOPMENT.md)
- Rules and checker details: [docs/RULES.md](docs/RULES.md)
- Implementation notes: [docs/IMPLEMENTATION.md](docs/IMPLEMENTATION.md)
- CFG/analysis visualization: [docs/VISUALIZATION.md](docs/VISUALIZATION.md)
- Release process: [docs/RELEASE.md](docs/RELEASE.md)
- Sample config: [docs/zwanzig.sample.json](docs/zwanzig.sample.json)

## License

MIT
