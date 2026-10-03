# Usage

## Build

```bash
zig build -Doptimize=ReleaseSafe
```

For a reproducible source build with the Zig 0.16.0 frontend, use the default development shell:

```bash
nix develop -c just build
```

To build with the Zig 0.15.2 frontend, select the dedicated compatibility shell:

```bash
nix develop .#zig015 -c just build
```

`just build` also uses `ReleaseSafe`. This mode keeps runtime safety checks without the analysis overhead of Debug builds.
Use plain `zig build` when you need a Debug binary.

## Run the CLI

If `zwanzig` is on your PATH:

```bash
zwanzig
```

From the repository (without installing):

```bash
zig build run -Doptimize=ReleaseSafe -- src/
```

Show the version:

```bash
zwanzig --version
```

### Zig frontend compatibility

Zwanzig embeds the Zig frontend used to build it, so frontend-specific syntax is interpreted according to that embedded version. Source builds support exactly Zig 0.15.2 and Zig 0.16.0. Release archive names include the selected frontend: use an archive containing `zig-0.15.2` for a Zig 0.15.2 project and one containing `zig-0.16.0` for a Zig 0.16.0 project. The selected frontend is also included in `--version`; when analyzing code that uses version-specific language features, use a Zwanzig binary built with the matching frontend.

Both frontend artifacts are maintained through the v0.17.x release line.
v0.18.0 is the first planned release without a Zig 0.15.2 artifact; users on
Zig 0.15.2 should stay on the latest v0.17.x release.

### Parse and frontend diagnostics

Zwanzig validates syntax before it runs checks, including AST-only selections. Syntax errors produce `parse-error` diagnostics at the parser's reported locations. Zwanzig skips the malformed file and continues with valid sibling files. Both supported frontends reject `usingnamespace`.

Enabled native checkers determine whether Zwanzig requests ZIR/type information. If that preflight fails, `frontend-error` identifies the embedded frontend and reports the loss of typed analysis. Required typed checks skip the file. Optional checks continue with AST fallback, which can reduce precision. This frontend check is not a complete compiler build.

An AST-only selection does not request ZIR preflight. It can therefore report no `frontend-error` for syntax that parses but would fail ZIR generation. For example, select `--do todo` to check comments without typed analysis.

### Files and directories

```bash
# Single file
zwanzig path/to/file.zig

# Multiple files
zwanzig file1.zig file2.zig file3.zig

# Directory (recursively scans for .zig files)
zwanzig src/

# Mix of files and directories
zwanzig src/ tests/ main.zig

# Using --file flag (can be repeated)
zwanzig --file src --file tests
```

### File discovery

Without arguments, zwanzig scans the current directory for `.zig` files. It skips:

- `zig-cache/`
- `zig-out/`
- `.zigmod/`
- `.gyro/`

If the selection resolves to no `.zig` files at all, zwanzig reports
`Error: No .zig files found. Nothing was analyzed.` on stderr and exits 1
without producing a report. An empty selection is a failed run, not a clean
one.

### Options

Every option takes its value as a separate argument (`--format json`, not
`--format=json`). An option zwanzig does not define is an error rather than a
silently ignored argument, so a mistyped flag cannot change what gets analyzed
without saying so.

### Exit status

| Status | Meaning |
| ---: | --- |
| 0 | The selection was analyzed and produced no diagnostics |
| 1 | Diagnostics were reported, or the run could not be trusted as a complete analysis |

Exit status 1 covers CLI errors, a selection with no `.zig` files, and any
diagnostic at any severity, including `parse-error`, `frontend-error`, and
`analysis-limit-exceeded`. A report is written to stdout for every run that
reaches the analysis stage; runs that fail before it write only to stderr.

## Using as a dependency

Add zwanzig to your project:

```bash
zig fetch --save https://github.com/forketyfork/zwanzig/archive/refs/tags/v0.15.1.tar.gz
```

Then wire a lint step in your `build.zig`:

```zig
const target = b.standardTargetOptions(.{});
const optimize = b.standardOptimizeOption(.{});

const zw = b.dependency("zwanzig", .{
    .target = target,
    .optimize = optimize,
});
const zw_exe = zw.artifact("zwanzig");

const run = b.addRunArtifact(zw_exe);
run.addArgs(&.{ "--format", "sarif", "src" });

const lint_step = b.step("lint", "Run zwanzig");
lint_step.dependOn(&run.step);
```

## Rule selection

With no config file and no `--do`/`--skip` flags, zwanzig runs all rules and checkers except `sentinel-alloc` (blocklisted by default). Config files or `--do`/`--skip` flags replace that default. Rule and checker names share the same namespace.

**Run only specific rules (allowlist):**

```bash
# Run only the empty-catch-engine checker
zwanzig --do empty-catch-engine file.zig

# Run multiple specific rules
zwanzig --do dupe-import --do unused-decl file.zig
```

**Skip specific rules (blocklist):**

```bash
# Run all rules except todo
zwanzig --skip todo file.zig

# Skip multiple rules
zwanzig --skip todo --skip unused-decl file.zig
```

`--do` and `--skip` are mutually exclusive.

The default `sentinel-alloc` blocklist only applies when you don't pass a config file or `--do`/`--skip`. To enable it, provide a config file (even one without rule filters) or define your own allowlist/blocklist.

Rule selection also controls preparation work. Disabled native checkers do not request type preflight. Zwanzig prepares project sources only for enabled type-aware native checkers or the project `unused-decl` pass. Legacy rules can still request source types lazily.

If a prepared source or build file has syntax errors, the project `unused-decl` pass cannot prove that public declarations are unused. It defers those reports until the project parses successfully. Per-file checks still run on valid files.

`empty-catch-engine` uses structural CFG checks without an exploded-graph run by default. It runs the engine only for exploded-graph, annotated-CFG, or path-trace dumps. A plain CFG dump does not require that run.

For persistent settings, see [docs/CONFIG.md](CONFIG.md).

## Target configuration

Specify a target platform with `--target`:

```bash
# Analyze for Linux x86_64
zwanzig --target x86_64-linux-gnu src/

# Analyze for macOS ARM64
zwanzig --target aarch64-macos src/

# Analyze for WebAssembly
zwanzig --target wasm32-wasi src/

# Analyze for freestanding (embedded/kernel)
zwanzig --target aarch64-freestanding src/
```

Without `--target`, the native host configuration is used.

## Parallel analysis

Zwanzig analyzes files in parallel. The default thread limit is the CPU count. On both frontends, `--threads` includes the calling thread, not just background workers:

```bash
zwanzig --threads 4 src/
```

On a busy machine, use one analysis thread with no background analysis workers:

```bash
zwanzig --threads 1 ~/projects/example/src/
```

Do not pass the project root unless you also want to analyze its dependency and generated-source directories.

## Analysis limits

Use positive values to set the worklist and state limits:

```bash
zwanzig --max-steps 200000 --max-states-per-point 50 src/
```

These are the engine defaults. `--max-steps` limits worklist steps per engine run. `--max-states-per-point` caps retained states at each CFG program point across all call contexts. Widening can combine states within a compatible call context, but cannot increase the cap. Widening is enabled by default. See [docs/CONFIG.md](CONFIG.md) to disable it.

If the engine cannot continue within either limit, it stops that function's
analysis and reports `analysis-limit-exceeded` at the function, naming the limit
that was reached and the value configured. It does not exceed the state cap to
admit another call context. Path proofs that require complete analysis then
stop, so the diagnostic says the findings for that function are missing rather
than absent. Constant-condition and structural diagnostics can still appear.
Raising the matching limit removes the diagnostic; these limits do not bound
total process memory.

## Incremental caching

Reuse CFGs across runs with `--cache`:

```bash
zwanzig --cache src/
```

The cache lives in `.zwanzig-cache/`. Its key includes file content, target, tool and frontend versions, type-info availability, and enabled rules. When project sources are prepared, their fingerprint also contributes to the key. Changes to these inputs invalidate the entry.

The cache stores CFGs and limited type flags, not complete ZIR, typed metadata, function summaries, or diagnostics. Zwanzig restores source-backed declaration annotations from the current type context and recomputes diagnostics on every run. A cache hit does not bypass syntax validation or enabled checks.

Within one file, compatible checkers can also reuse an engine analysis without `--cache`. This in-memory cache is separate from disk storage. Its retention budget is not a process-memory limit.

Add `.zwanzig-cache/` to `.gitignore`.

## Debug output

Enable debug logging at build time with `-Dlog-level`:

```bash
zig build run -Doptimize=ReleaseSafe -Dlog-level=debug -- src/
```

Available log levels: `err`, `warn`, `info` (default), `debug`.

Debug output includes file discovery counts, rule counts, and analysis statistics. Engine-run statistics count actual runs, not each checker that reuses a result.

## Output formats

See [docs/OUTPUT.md](OUTPUT.md) for text, JSON, and SARIF output examples.

## Inline suppressions

See [docs/SUPPRESSIONS.md](SUPPRESSIONS.md) for suppression comment formats.

## CI integration

See [docs/CI.md](CI.md) for GitHub Actions setup and SARIF upload.

## Examples

See the `examples/` directory for sample code demonstrating both violations and proper error handling patterns.

## Testing

Run the test suite:

```bash
zig build test
```
