# Implementation details

Internal architecture and implementation of the Zwanzig static analyzer.

## Architecture

Zwanzig is a modular static analysis framework for Zig. The architecture has several components that work together to analyze source files and detect issues.

### Module layout

Larger subsystems are split into focused submodules with thin facades:

- `src/cli/` - CLI parsing (`args.zig`), config merge (`config_merge.zig`), default rule/checker registry (`registry.zig`), and the run loop (`run.zig`)
- `src/formatters/` - Output formatters (console text and SARIF)
- `src/cfg/` - CFG graph types, builder, and DOT output (facade: `src/cfg.zig`)
- `src/engine/` - Analysis engine internals (analysis, state, values, constraints, summaries, store) (facade: `src/engine.zig`)
- `src/analysis/` + `src/project_sources.zig` - Immutable syntax snapshots, lexical/path indexes, project references, and best-effort import/call type resolution
- `src/analysis_cache.zig` - Per-file reuse of compatible engine analyses through exclusive leases
- `src/zir/` + `src/types/` - ZIR bridge implementation and shared type info (facade: `src/zir_bridge.zig`)
- `src/lib.zig` - Public library exports for embedding

#### Zig frontend compatibility

Zwanzig supports the exact Zig 0.15.2 and 0.16.0 toolchains. `src/compat.zig`
enforces that support boundary and selects the matching adapter at compile time.
The I/O adapter carries the application context through file discovery,
analysis, caching, formatting, and DOT output, while the executor and mutex
adapters preserve parallel-analysis behavior across the two standard-library
concurrency APIs. ZIR declaration and switch decoding is isolated in the
version-specific adapters under `src/compat/`, so the analyzer and checkers
operate on the shared type-information model.

### Core components

#### Source parsing cache

The `Source` abstraction (`src/source.zig`) provides cached access to Zig syntax. Its API parses lazily, but the analyzer always requests and validates the AST before checks. A source can also borrow an existing project AST.

**Behavior:**
- Lazy API: `ast()` and `tokens()` parse on first access unless the source borrows a project AST
- Caching: All checks for a file reuse the same syntax, lexical index, and declaration parent map
- Validation: Parser errors remain in the AST. Callers must reject malformed syntax before semantic traversal
- Memory management: `deinit()` frees local caches, not borrowed project syntax, lexical indexes, or source bytes

**API:**
- `init(allocator, file_path, content)`: Creates a source over caller-owned source bytes
- `initParsed(allocator, file_path, parsed_ast)`: Borrows a project-owned AST and its source bytes
- `ast()`: Returns the cached AST, parsing if necessary
- `tokens()`: Returns the cached token list, parsing if necessary
- `lexicalIndex()`: Borrows the attached project index or builds a local index on first access
- `engineParentMap()`: Builds and caches parent links within executable declarations
- `getContent()`: Returns the raw source text
- `getFilePath()`: Returns the file path
- `locationMapper()`: Returns the cached location mapper for byte-to-line/column conversion
- `byteToLocation(byte_offset)`: Converts a byte offset to a `Location` (line, column)
- `byteRangeToSourceRange(start, end)`: Converts a byte range to a `SourceRange`
- `tokenLocation(token_index)`: Gets the location of a token by its index
- `deinit()`: Releases cached resources

The analyzer attaches the project index through `borrowed_lexical_index` before
checks start. It must describe the same AST and outlive the `Source`. Standalone
sources own their lazily built indexes. Engines borrow source parent maps; they
own a separate fallback only for standalone or foreign-AST queries.

**Usage Pattern:**
```zig
var source = Source.init(allocator, file_path, content);
defer source.deinit();

// First call parses and caches
const ast1 = try source.ast();

// Second call returns cached result (no re-parsing)
const ast2 = try source.ast();

// Same for tokens
const tokens = try source.tokens();
```

#### Analyzer

The `Analyzer` (`src/analyzer.zig`) coordinates the analysis process:

1. Applies rule filters to determine native checker type demand and project `unused-decl` demand
2. Prepares project source snapshots only when either demand requires them
3. Creates a `Source` over project-owned syntax or file content
4. Reports `parse-error` diagnostics and skips checks for malformed files, without stopping valid sibling files
5. Requests ZIR/type information only for enabled native checkers whose requirement is not `.none`
6. Reports `frontend-error` when type preflight fails, skips required typed checks, and lets optional checks use AST fallback
7. Runs enabled native checkers, then enabled legacy rules, and collects diagnostics and actual engine-run statistics

`CheckerContext` carries build metadata, the per-file type context, CFG artifacts, shared analysis, limits, statistics, configuration, and dump directories. Disabled native checkers do not cause type preflight. Legacy rules retain lazy access to `Source` type queries. Allocation failures propagate instead of becoming successful analysis with missing results.
`CheckerContext` also carries the diagnostics list for the file under analysis
so that analysis infrastructure, not only individual checkers, can report what
it could not complete.

#### Rule interface (legacy)

The `Rule` interface (`src/rule.zig`) defines the contract for legacy analysis rules:

```zig
pub const Rule = struct {
    name: []const u8,
    default_severity: Severity = .err,
    checkFn: *const fn (
        source: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
    ) RuleError!void,
};
```

Rules receive a `Source` pointer, allowing them to:
- Access raw source text via `getContent()`
- Parse and traverse the AST via `ast()`
- Examine tokens via `tokens()`
- Avoid redundant parsing when multiple rules access the same representations

#### Checker interface

The `Checker` interface (`src/checker.zig`) exposes the AST hook used by native analysis passes. Checkers can build CFGs and run the engine from that hook. Separate CFG and IR hooks remain future work.

```zig
pub const TypeRequirement = enum { none, optional, required };

pub const Checker = struct {
    name: []const u8,
    default_severity: Severity = .err,
    type_requirement: TypeRequirement = .optional,
    checkAstFn: ?*const fn (
        source: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        context: CheckerContext,
    ) CheckerError!void = null,

    pub fn checkAst(...) CheckerError!void { ... }
    pub fn hasHooks(self: *const Checker) bool { ... }
};
```

**Behavior:**
- Hook-based design: Checkers implement specific hooks (currently `checkAstFn`) rather than a single check function
- Multiple analysis stages: Future versions will add CFG and IR hooks for control-flow and dataflow analysis
- Backward compatibility: `CheckerManagerWithRules` supports both new checkers and legacy rules
- Context-aware analysis: `CheckerContext` exposes build metadata, type information, analysis limits/stats, config, shared analyses, and visualization outputs

`type_requirement` controls frontend preflight and dispatch:

| Requirement | Behavior |
| --- | --- |
| `.none` | Does not request ZIR preflight. The checker can run with AST/CFG data alone |
| `.optional` | Requests type information, but runs with AST fallback after frontend failure. This is the default |
| `.required` | Requests type information and skips the hook when that information is unavailable |

A `.none` checker can receive a type context when another enabled checker requested it. Required dispatch preserves allocation failures rather than treating them as unsupported source. Legacy `Rule` values do not declare this requirement.

#### Shared analyses and ownership

`CheckerContext.getOrBuildCfg()` returns a `CfgHandle`. `CachedArtifacts` owns shared CFGs, while an owned handle frees its private CFG. Artifact allocations use the artifact owner's allocator, not an engine lease's counting allocator.

`CheckerContext.getOrAnalyze()` returns an exclusive `AnalysisHandle`. Compatible `.configured` requests can reuse an engine when their source, stable CFG, type context, configuration, metadata, artifacts, and limits match. `.plain` analyses and analyses over unstable or privately owned CFGs remain uncached.

Both budgets abort the engine run with one error, so `AnalysisEngine.limit_kind`
records which one fired. `getOrAnalyze()` turns that into
`analysis-limit-exceeded` in the diagnostics list carried by the
`CheckerContext`, naming the limit and the value that was reached. The report is
emitted where the entry is created, so checkers that later lease the same cached
engine do not repeat it. Checkers still test `analysis.complete` and drop their
own results for an incomplete run; the diagnostic is what makes that drop
visible instead of silent.

```zig
var cfg_handle = (try context.getOrBuildCfg(allocator, source, fn_node)) orelse return;
defer cfg_handle.deinit();

var analysis = try context.getOrAnalyze(allocator, source, &cfg_handle, checker.name, .configured);
defer analysis.deinit();
if (!analysis.complete) return; // already reported as analysis-limit-exceeded

const graph = analysis.engine.getGraph();
```

Do not copy the analysis handle or retain engine pointers after its `deinit()`. Graph results are read-only, but lazy engine queries can grow internal caches during a lease. The cache admits an engine only after the checker releases it, so the retained size includes those queries.

The per-file cache retains at most 64 entries and 16 MiB of live engine-owned allocation payload. It uses first-fit admission without eviction. Active leases, separately owned CFG artifacts, and source-owned syntax metadata are outside that retention budget. Allocator overhead and retained physical pages are also outside it. This is not an RSS limit or a constant-memory guarantee.

Destroy all leases before `AnalysisCache`, then destroy the borrowed CFG artifacts, `TypeContext`, and `Source`. The analyzer keeps one `TypeContext` alive for the entire per-file cache lifetime. Configuration and other borrowed inputs must remain unchanged while cached results exist. Statistics record actual engine runs, not cache hits.

#### CheckerManager

The `CheckerManager` (`src/checker.zig`) handles checker registration and coordinates running checks:

```zig
pub const CheckerManager = struct {
    pub fn init(allocator: std.mem.Allocator) CheckerManager { ... }
    pub fn deinit(self: *CheckerManager) void { ... }
    pub fn registerChecker(self: *CheckerManager, checker: *const Checker) !void { ... }
    pub fn runAstChecks(self: *const CheckerManager, source: *Source, diagnostics: *std.ArrayList(Diagnostic), filter_fn: ?*const fn ([]const u8) bool, context: CheckerContext) CheckerError!void { ... }
};
```

#### CheckerManagerWithRules

For backward compatibility, `CheckerManagerWithRules` supports both checkers and legacy rules. Checkers run first, then adapted rules.

```zig
pub const CheckerManagerWithRules = struct {
    pub fn registerChecker(self: *CheckerManagerWithRules, checker: *const Checker) !void { ... }
    pub fn registerRule(self: *CheckerManagerWithRules, rule: *const Rule) !void { ... }
    pub fn runAstChecks(...) CheckerError!void { ... }
};
```

**Usage:**
```zig
var manager = CheckerManagerWithRules.init(allocator);
defer manager.deinit();

// Register a new-style checker
try manager.registerChecker(&MyChecker.checker);

// Register a legacy rule
try manager.registerRule(&MyRule.rule);

// Run all checks
const context = CheckerContext{ .build_metadata = null };
try manager.runAstChecks(&source, &diagnostics, null, context);
```

#### Diagnostics

Diagnostics represent issues found by rules and checkers. Each includes:
- File path
- Source range (start and end locations)
- Rule ID
- Severity (`hint`, `warning`, or `err`)
- Message

The `Diagnostic` type (`src/diagnostic.zig`) provides:
- `Severity` enum with `hint`, `warning`, and `err` levels
- `Location` struct for line/column positions (1-based)
- `SourceRange` struct for start/end location pairs
- `LocationMapper` for converting byte offsets to line/column positions

**Message ownership:**

Diagnostics own their message strings. When creating via `Diagnostic.init()` or `Diagnostic.initAtLocation()`, the message is duplicated. `Analyzer.deinit()` frees all diagnostic messages. Rules and checkers should never manually free diagnostic messages.

**Output formats:**

The analyzer supports multiple output formats via `Analyzer.OutputFormat`:

- **Text format**: Human-readable output with one diagnostic per line
  ```
  file.zig:10:5: error: [rule-name] Message
  ```

- **JSON format**: Machine-readable structured output for tool integration
  ```json
  {
    "diagnostics": [
      {
        "file": "file.zig",
        "rule": "rule-name",
        "severity": "error",
        "message": "Message",
        "location": {
          "start": {"line": 10, "column": 5},
          "end": {"line": 10, "column": 20}
        }
      }
    ],
    "total": 1
  }
  ```

- **SARIF format**: Code scanning format for GitHub and other tooling (SARIF 2.1.0)

The `--format` CLI flag controls output format (defaults to text). Formatter implementations are in `src/formatters/` (`console.zig`, `sarif.zig`).

## Parsing strategy

Zwanzig uses Zig's standard library parser (`std.zig.Ast.parse`). The `Source` API remains lazy, but analyzer validation is unconditional:

1. Reuse a prepared project AST, or parse the file through `source.ast()`
2. Inspect parser errors before rules, CFG construction, or semantic traversal
3. Emit `parse-error` diagnostics and skip malformed files
4. Reuse valid syntax for all enabled checks
5. Free owned syntax after checks, or leave borrowed syntax for the project registry to free

AST-only selections still receive syntax diagnostics. They do not require ZIR generation. Both Zig 0.15.2 and Zig 0.16.0 reject `usingnamespace`.

### Project syntax and reference indexes

`ProjectSources` owns an immutable snapshot of selected sources and discovered build context. Each entry owns its source bytes, AST, and lexical index. Workers borrow that syntax while keeping type and engine caches local.

- `LexicalIndex` records declaration candidates, token ranges, scopes, parent links, and enclosing functions. Optional-unwrap guards use these facts to resolve bindings and method candidates without repeated whole-file scans. Payload queries reconnect container members through token scopes, so nested methods retain enclosing top-level captures.
- The source's declaration parent map preserves engine ancestry: it includes container members but excludes detached function-signature subtrees. It is not interchangeable with lexical parent links or function-root checker maps.
- `PathIndex` indexes exact paths, normalized paths, and package stems. Import lookup preserves the first matching file across exact, relative, and package-name matches. Subset and foreign file slices use the unindexed fallback.
- `ProjectReferenceIndex` computes namespace and alias targets for project `unused-decl` analysis. Its dependency worklist preserves reachable targets through valid alias cycles.

Malformed ASTs contribute no semantic facts. They can remain addressable by path without exposing parser-recovery nodes to resolvers. Project lookup can resolve types and references across available files, but does not execute cross-file calls.

## Parallel analysis

File-level analysis runs in parallel by default. On both frontends, `--threads` limits analysis concurrency including the calling thread. A limit of one uses no background analysis workers. The adapters normalize a zero count to one, although the CLI requires a positive value. Both executors drain submitted work during `deinit()`. The Zig 0.16 adapter rejects mismatched context and executor counts.

Workers use libc's allocator for per-file scratch so engine allocations can be freed during analysis. The project registry owns shared immutable syntax. Each worker returns an isolated result, then the caller merges and sorts diagnostics for deterministic output.

## Adding checkers

Implement analysis passes using the `Checker` interface.

### Creating a checker

1. Create a file in `src/checkers/` (e.g., `my_checker.zig`)
2. Define a checker constant of type `Checker` and select its `type_requirement`
3. Implement the hook functions you need

Example:
```zig
const std = @import("std");
const checker_mod = @import("../checker.zig");
const Checker = checker_mod.Checker;
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const Source = @import("../source.zig").Source;

pub const MyChecker = struct {
    pub const checker: Checker = .{
        .name = "my-checker",
        .default_severity = .warning,
        .type_requirement = .none,
        .checkAstFn = checkAst,
    };

    fn checkAst(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        context: checker_mod.CheckerContext,
    ) CheckerError!void {
        _ = context;
        const tree = try src.ast();

        // Analyze the AST...

        // Report issues
        try diagnostics.append(allocator, Diagnostic.initAtLocation(
            allocator,
            src.getFilePath(),
            "my-checker",
            .warning,
            "Issue description",
            line,
            column,
        ));
    }
};
```

4. Register the checker in `src/cli/registry.zig` (for the CLI):
```zig
try analyzer.registerChecker(&MyChecker.checker);
```

### Legacy rules (backward compatibility)

Rules using the `Rule` interface continue to work via `CheckerManagerWithRules`.

To add a legacy rule:

1. Create a file in `src/rules/` (e.g., `my_rule.zig`)
2. Define a struct with a `rule` constant of type `Rule`
3. Implement the check function with signature:
   ```zig
   fn check(
       source: *Source,
       allocator: std.mem.Allocator,
       diagnostics: *std.ArrayList(Diagnostic),
   ) RuleError!void
   ```
4. Register the rule in `src/cli/registry.zig` (for the CLI)

Example:
```zig
const Diagnostic = @import("../rule.zig").Diagnostic;
const Severity = @import("../rule.zig").Severity;

pub const MyRule = struct {
    pub const rule: Rule = Rule{
        .name = "my-rule",
        .default_severity = .warning,
        .checkFn = check,
    };

    fn check(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
    ) RuleError!void {
        // Access the AST
        const ast = try src.ast();

        // Traverse nodes and detect issues
        // ...

        // Report diagnostics with location
        try diagnostics.append(allocator, Diagnostic.initAtLocation(
            allocator,
            src.getFilePath(),
            "my-rule",
            .warning,
            "Issue description",
            line,
            column,
        ));

        // Or with a source range for better highlighting
        const range = try src.byteRangeToSourceRange(start_byte, end_byte);
        try diagnostics.append(allocator, Diagnostic.init(
            allocator,
            src.getFilePath(),
            "my-rule",
            .warning,
            "Issue description",
            range,
        ));
    }
};
```

## AST-based rule implementation

Rules use AST traversal to analyze code structure. Benefits over text-based scanning:

1. **Accuracy**: AST nodes precisely represent language constructs, avoiding false positives from string matching
2. **Context awareness**: The AST provides structural context (e.g., distinguishing a `catch` keyword in a comment vs actual code)
3. **Token information**: Access to token positions enables accurate source location reporting

### Example: empty-catch-engine syntax scan

`empty-catch-engine` uses structural CFG checks inside functions and an AST/token scan for top-level catch expressions. The top-level scan excludes function bodies, finds catch handlers, and uses token locations for diagnostics. Neither path requires type information. See [EmptyCatchEngineChecker](#emptycatchenginechecker) for the visualization-only engine run.

### Example: dupe-import rule

The `dupe-import` rule uses token-based analysis to detect duplicate imports:

```zig
fn check(src: *Source, allocator: std.mem.Allocator, diagnostics: *std.ArrayList(Diagnostic)) RuleError!void {
    const tree = try src.ast();
    const token_tags = tree.tokens.items(.tag);
    const token_starts = tree.tokens.items(.start);

    var seen_imports = std.StringHashMap(ImportInfo).init(allocator);
    defer seen_imports.deinit();

    var i: usize = 0;
    while (i < token_tags.len) : (i += 1) {
        if (token_tags[i] == .builtin) {
            // Check if this is @import followed by ("...")
            if (isImportPattern(token_tags, i)) {
                const import_path = getStringLiteralContent(...);
                if (seen_imports.get(import_path)) |first_import| {
                    // Report duplicate
                    try diagnostics.append(allocator, Diagnostic.init(...));
                } else {
                    try seen_imports.put(import_path, ...);
                }
            }
        }
    }
}
```

The rule:
1. Scans tokens looking for builtin identifiers (`@import`)
2. Checks for the pattern `@import("...")` by examining following tokens
3. Tracks seen import paths in a hash map
4. Reports duplicates with reference to the first occurrence

### Example: unused-decl rule

`unused-decl` combines per-file declaration/reference analysis with a separate project pass. It uses scope and receiver information rather than a raw count of matching identifier tokens.

The per-file rule checks unused container declarations with conservative exclusions for exports and entrypoints. The project pass checks public top-level declarations across analyzed files. It preserves package entrypoints, alias-style exports, and declarations exposed by used types, signatures, fields, or initializers.

The project reference index follows imports, namespace aliases, and nested type aliases. Valid alias cycles retain their reachable targets instead of losing references at a recursion cutoff. Malformed files provide no semantic reference facts.

### Example: unreachable-code and unreachable-code-engine

The AST rule `unreachable-code` handles code after unconditional terminators and fully terminating branches. `unreachable-code-engine` reports constant-condition branches and additional contradictions under immutable scalar enclosing guards.

```zig
fn integerGuard(value: i32) i32 {
    if (value > 0) {
        if (value < 0) {
            return 1;
        }
    }
    return 0;
}
```

The inner true branch contradicts the enclosing positive-value guard. A path-sensitive report requires complete analysis and a reached condition whose feasible states all retain the blocking guard. Supported proof premises use immutable integer or boolean scalars. Integer domains must fit the signed 64-bit constraint model.

An absent exploded-graph node alone does not prove unreachable code. Mutable values, arbitrary engine facts, unsupported conditions, and incomplete analyses do not establish these path proofs. Constant-condition checks run independently and retain their diagnostics when the engine reaches a limit.

### Example: empty-defer and empty-errdefer rules

These rules detect empty defer/errdefer blocks using AST analysis:

```zig
fn check(src: *Source, allocator: std.mem.Allocator, diagnostics: *std.ArrayList(Diagnostic)) RuleError!void {
    const tree = try src.ast();
    const tags = tree.nodes.items(.tag);
    const data = tree.nodes.items(.data);

    for (tags, 0..) |tag, i| {
        if (tag == .@"defer") {  // or .@"errdefer"
            const defer_body_opt = data[i].opt_node;
            if (defer_body_opt.unwrap()) |defer_body_node| {
                const body_tag = tags[defer_body_idx];

                var is_empty = false;
                switch (body_tag) {
                    .block, .block_semicolon => {
                        const extra = data[defer_body_idx].extra_range;
                        is_empty = (extra.end <= extra.start);
                    },
                    .block_two, .block_two_semicolon => {
                        const opt_nodes = data[defer_body_idx].opt_node_and_opt_node;
                        is_empty = (opt_nodes[0].unwrap() == null and opt_nodes[1].unwrap() == null);
                    },
                    else => {},
                }

                if (is_empty) {
                    try diagnostics.append(allocator, Diagnostic.init(...));
                }
            }
        }
    }
}
```

The rules:
1. Scan AST nodes for `defer` or `errdefer` tags
2. Extract the defer body from the AST node data
3. Check if the body is an empty block by examining the block structure
4. Report empty blocks as diagnostics

## Intermediate Representation (IR)

Zwanzig uses a minimal IR to bridge AST nodes and control-flow analysis, capturing the structure needed for dataflow analysis.

### IR node types

The IR (`src/ir.zig`) defines:

| Tag | Description |
|-----|-------------|
| `fn_entry` | Function entry point |
| `fn_exit` | Function exit point (normal return path) |
| `ret` | Return statement |
| `var_decl` | Variable declaration (const/var) |
| `assign` | Assignment expression |
| `call` | Function call expression |
| `block` | Block of statements |
| `expr` | Generic expression |
| `nop` | No-op placeholder for control flow merge points |
| `branch` | Branch condition evaluation (if/else) |
| `loop_header` | While/for loop header (condition evaluation) |
| `loop_body` | Loop body entry point |
| `defer_stmt` | Defer statement body |
| `errdefer_stmt` | Errdefer statement body |
| `try_expr` | Try expression - propagates errors to caller |
| `catch_expr` | Catch expression - handles errors locally |
| `break_stmt` | Labeled-block exit, after operand evaluation and before exited-scope defers |

### IR node structure

Each `IrNode` contains:
- `tag`: The kind of IR node (`IrTag`)
- `ast_node`: Optional index of the corresponding AST node
- `source_range`: Optional source location for diagnostics

```zig
pub const IrNode = struct {
    tag: IrTag,
    ast_node: ?u32,
    source_range: ?SourceRange,
};
```

## Control Flow Graph (CFG)

The CFG (`src/cfg.zig`) represents control flow within a function. It maps IR nodes to their control flow relationships. The facade in `src/cfg.zig` re-exports from `src/cfg/` (`graph.zig`, `builder.zig`, `dot.zig`).

### CFG structure

A CFG has:
- `nodes`: List of `CfgNode` entries, each containing an IR node
- `edges`: List of `CfgEdge` entries connecting nodes
- `entry`: Index of the function entry node
- `exit`: Index of the function exit node

### Edge types

| Kind | Description |
|------|-------------|
| `normal` | Sequential control flow |
| `jump` | Unconditional jump (e.g., from return to exit) |
| `branch_true` | Edge taken when branch condition is true |
| `branch_false` | Edge taken when branch condition is false |
| `loop_back` | Loop back-edge (from loop body back to condition) |
| `loop_exit` | Loop exit edge (when condition is false) |
| `defer_edge` | Defer execution edge (before return/exit) |
| `errdefer_edge` | Errdefer execution edge (on error path) |
| `try_error` | Error path from try expression (propagates to caller) |
| `try_success` | Success path from try expression (continues normally) |
| `catch_error` | Error path into catch handler |
| `catch_success` | Success path from catch (value unwrapped) |

### CFG builder

The `CfgBuilder` constructs CFGs from Zig AST function declarations. Supported constructs:

- Function entry/exit
- Block statements
- Return statements
- Variable declarations
- Assignment expressions
- Function calls
- If/else branching (with merge points)
- While loops (with back-edges)
- For loops (with back-edges)
- Defer statements
- Errdefer statements
- Try expressions
- Catch expressions

**Usage:**
```zig
var builder = CfgBuilder.init(allocator);
const tree = try source.ast();
const root_decls = tree.rootDecls();

for (root_decls) |decl| {
    if (try builder.buildFromFn(&source, decl)) |*cfg| {
        defer cfg.deinit();
        // Analyze the CFG...
    }
}
```

### CFG traversal

The CFG provides methods for traversing the graph:

```zig
// Get all successor node indices
var succs: std.ArrayList(u32) = .empty;
try cfg.getSuccessors(allocator, node_index, &succs);

// Get all predecessor node indices
var preds: std.ArrayList(u32) = .empty;
try cfg.getPredecessors(allocator, node_index, &preds);
```

### Source location mapping

CFG nodes maintain source range information for diagnostic reporting:

```zig
if (cfg.getNode(index)) |node| {
    if (node.ir_node.source_range) |range| {
        // range.start.line, range.start.column
        // range.end.line, range.end.column
    }
}
```

### Branching CFG

The CFG builder supports `if` and `if-else` constructs:

1. **Branch nodes**: An `if` creates a `branch` IR node for the condition evaluation
2. **True/false edges**: Edges to the then-block are `branch_true`, edges to else-block (or merge point) are `branch_false`
3. **Merge points**: A `nop` node after the if/else is where control flow reconverges
4. **Terminating branches**: If both branches terminate, the merge point is not connected (unreachable code)

**Example CFG for if-else:**
```
fn_entry
    │
    ▼
  branch ─────┐
    │         │
    │ true    │ false
    ▼         ▼
 then_body  else_body
    │         │
    ▼         ▼
   nop ◄──────┘
    │
    ▼
  fn_exit
```

### Loop CFG

The CFG builder supports `while` and `for` loops with back-edges:

1. **Loop header**: A `loop_header` node represents the condition evaluation
2. **Loop body**: A `loop_body` node marks entry into the body
3. **Back-edges**: After the body completes (without terminating), a `loop_back` edge connects back to the header
4. **Exit edge**: A `loop_exit` edge from the header leads to code after the loop
5. **Termination handling**: If the body terminates (e.g., with return), no back-edge is created

**Example CFG for while loop:**
```
fn_entry
    │
    ▼
loop_header ◄────┐
    │            │
    │ true       │ loop_back
    ▼            │
loop_body ───────┘
    │
    │ loop_exit
    ▼
   nop
    │
    ▼
  fn_exit
```

### Defer/errdefer CFG

The CFG builder models `defer` and `errdefer` statements:

1. **Defer nodes**: A `defer_stmt` node for each `defer`, connected via `defer_edge`
2. **Errdefer nodes**: An `errdefer_stmt` node for each `errdefer`, connected via `errdefer_edge`
3. **Body representation**: The defer body is a `block` node following the defer/errdefer node
4. **Execution order**: Defers are recorded in program order; actual execution is reverse order at function exit

**Example CFG with defers:**
```
fn_entry
    │
    ▼
defer_stmt ──► block (defer body)
    │
    ▼
errdefer_stmt ──► block (errdefer body)
    │
    ▼
  fn_exit
```

### Try/catch CFG (error flow)

The CFG builder models Zig's error handling constructs (`try` and `catch`):

#### Try expressions

A `try` expression evaluates an error union and either unwraps the success value or propagates the error:

1. **Try node**: A `try_expr` node represents the error-checking point
2. **Error path**: A `try_error` edge connects to `fn_exit` (error propagation)
3. **Success path**: A `try_success` edge connects to the next statement

**Example CFG for try:**
```
fn_entry
    │
    ▼
try_expr ──────┐
    │          │
    │ success  │ error
    ▼          ▼
var_decl    fn_exit
    │
    ▼
  fn_exit
```

#### Catch expressions

A `catch` expression handles errors locally with a fallback value or handler block:

1. **Catch node**: A `catch_expr` node represents the error-handling point
2. **Success path**: A `catch_success` edge connects to the merge point (value unwrapped)
3. **Error path**: A `catch_error` edge connects to the handler, then to the merge point

**Example CFG for catch with handler:**
```
fn_entry
    │
    ▼
catch_expr ─────────┐
    │               │
    │ success       │ error
    │               ▼
    │           handler_body
    │               │
    ▼               │
   nop ◄────────────┘
    │
    ▼
  fn_exit
```

#### Try in variable declarations

When `try` appears in a variable declaration's initializer (e.g., `const x = try foo();`), the CFG models both paths:

```
fn_entry
    │
    ▼
try_expr ──────┐
    │          │
    │ success  │ error
    ▼          ▼
var_decl    fn_exit
    │
    ▼
  ...
```

#### Catch in variable declarations

`catch` in a variable declaration creates branching for error handling:

```
fn_entry
    │
    ▼
catch_expr ─────────┐
    │               │
    │ success       │ error
    │               ▼
    │            handler
    │               │
    ▼               │
var_decl ◄──────────┘
    │
    ▼
  ...
```

## Typed IR bridge (ZIR integration)

The `ZirBridge` module (`src/zir_bridge.zig`) connects Zwanzig's analysis pipeline to Zig's AST-generated intermediate representation, ZIR. Implementation is in `src/zir/bridge.zig`, with declaration models in `src/zir/decls.zig` and shared type definitions in `src/types/type_info.zig`.

### Overview

`std.zig.AstGen` generates ZIR before full compiler semantic analysis. ZIR availability therefore does not prove that a file compiles or that every type is resolved. The bridge extracts best-effort information from AST and ZIR:

- Declaration types (variables, constants, functions)
- Function signatures and parameter types
- Type metadata that Zwanzig can recover without full build execution

`TypeContext` and project resolvers extend these queries to supported locals, parameters, nested scopes, expressions, and available project sources.

### Types

#### TypeInfo

Type information for a declaration or expression (defined in `src/types/type_info.zig`):

```zig
pub const TypeInfo = struct {
    kind: TypeKind,      // Type category (int, pointer, function, etc.)
    size_bits: u16,      // Bit width for numeric types
    is_signed: bool,     // Signedness for integers
    is_comptime: bool,   // Whether compile-time known
};

pub const TypeKind = enum {
    unknown, void_type, bool_type, int, uint, float,
    pointer, slice, array, optional, error_union,
    function, @"struct", @"enum", @"union", type_type,
};
```

#### DeclInfo

Information about a declaration extracted from ZIR:

```zig
pub const DeclInfo = struct {
    name: []const u8,        // Declaration name
    type_info: TypeInfo,     // Type information
    is_pub: bool,            // Whether exported
    is_const: bool,          // Whether constant
    is_fn: bool,             // Whether function
    ast_node: ?u32,          // AST node index
    zir_inst: ?u32,          // ZIR instruction index
};
```

### ZirBridge usage

```zig
const ZirBridge = @import("zir_bridge.zig").ZirBridge;

var bridge = ZirBridge.init(allocator);
defer bridge.deinit();

// Generate ZIR and extract declaration metadata.
try bridge.loadFromSource(&source);

// Query typed information
if (bridge.hasZir()) {
    std.debug.print("Instructions: {d}\n", .{bridge.getInstructionCount()});

    // Find a declaration by name
    if (bridge.findDeclByName("my_function")) |decl| {
        if (decl.is_fn) {
            std.debug.print("Found function: {s}\n", .{decl.name});
        }
    }

    // Iterate all declarations
    for (0..bridge.getDeclCount()) |i| {
        if (bridge.getDecl(i)) |decl| {
            std.debug.print("{s}: {}\n", .{decl.name, decl.type_info});
        }
    }
}
```

### How it works

1. **AST parsing**: Source code is parsed into `std.zig.Ast` via `Source`
2. **ZIR generation**: `std.zig.AstGen.generate()` converts AST to ZIR
3. **Declaration extraction**: Root declarations are extracted from both AST and ZIR
4. **Type mapping**: ZIR instruction types are mapped to `TypeInfo`

### AST to ZIR mapping

The `findZirInstForNode` function provides best-effort mapping from AST node indices to ZIR instruction indices by iterating ZIR instructions and checking their source node references:

- `pl_node` format: Most operations store their source node in `data.pl_node.src_node`
- `node` format: Parameters and declaration references store the node directly in `data.node`
- `un_node` format: Unary operations store their source node in `data.un_node.src_node`

### Limitations

- ZIR generation requires syntax accepted by the embedded frontend and can still fail during AstGen
- Type resolution is best-effort, not full compiler semantic analysis or complete build-context evaluation
- Supported local, parameter, nested-scope, and project-aware queries extend beyond module declarations, but can remain unresolved
- Project-aware type and reference lookup does not imply cross-file call execution
- AST-to-ZIR mapping is best-effort. Some AST nodes have no corresponding instruction or map to multiple instructions

Full sentinel-value propagation and a complete error-union value model remain roadmap work. Additional parity rules and cross-file call execution are also unshipped.

### Integration with analysis

ZirBridge typed information is used throughout the analysis pipeline for type-aware rules, CFG-based analysis, and IR nodes carrying `TypeInfo`.

### TypeContext

The `TypeContext` (`src/type_context.zig`) combines ZirBridge metadata, best-effort AST inference, and optional project resolution. It caches queries for one file. The analyzer keeps this context alive until every shared engine analysis has been released:

```zig
const TypeContext = @import("type_context.zig").TypeContext;

var ctx = TypeContext.init(allocator, &source);
defer ctx.deinit();

// Query declaration types
if (ctx.getDeclType("my_var")) |ti| {
    if (ti.kind == .error_union) {
        // Handle error union type
    }
}

// Classify identifiers (useful for naming rules)
switch (ctx.classifyIdentifier("MyType")) {
    .type_decl => {},   // struct, enum, union
    .function => {},    // function
    .constant => {},    // const declaration
    .variable => {},    // var declaration
    .unknown => {},     // not found or ZIR unavailable
}

// Type kind queries
if (ctx.isDeclErrorUnion("result")) { /* ... */ }
if (ctx.isDeclOptional("maybe_val")) { /* ... */ }
if (ctx.isDeclPointer("ptr")) { /* ... */ }
```

#### Expression Type Queries

TypeContext provides methods for querying types of expressions and calls at specific AST nodes:

```zig
// Query expression type by AST node index
if (ctx.getExpressionType(ast_node)) |ti| {
    // Use type information
}

// Check if an expression returns an error union
if (ctx.isExpressionErrorUnion(ast_node)) {
    // Expression may return an error
}

// Query the function declaration's return type.
if (ctx.getContainingFunctionReturnType(fn_ast_node)) |ti| {
    if (ti.kind == .error_union) {
        // Function returns error union
    }
}

// Get expression type for a call node
if (ctx.getExpressionType(call_node)) |ti| {
    // ti.kind indicates the type category (e.g., .error_union)
    // ti.type_str contains the type name if known (e.g., "std.fs.File")
}
```

Expression type queries handle:
- **Call expressions**: Resolve supported callee return types, including project-aware receiver queries
- **Try expressions**: Recover the error-union payload type when available
- **Catch expressions**: Require compatible success and fallback types instead of using the fallback alone
- **Error values**: Identify error values without a complete error-union value model
- **Identifiers**: Query declarations, supported local bindings, parameters, and payload captures

Unsupported or ambiguous queries remain unknown. Best-effort queries can use known-method heuristics. Strict queries exclude those heuristics.

`getExpressionTypeStrict()` excludes name-only heuristics and CFG type hints.
It caches completed top-level queries, including unresolved results, for the
lifetime of the per-file `TypeContext`. Nested queries bypass this cache because
recursion guards can produce incomplete results. Allocation failures in the
resolution guard or source parsing do not populate it. The strict cache is
separate from the heuristic cache and is released by `deinit()`.

### Source type API

The `Source` struct (`src/source.zig`) provides type information through a lazy-loaded ZirBridge. `hasTypeInfo()` and related convenience queries are best-effort. `requireZirBridge()` preserves parse, frontend, and allocation errors, including a failure from an earlier lazy query:

```zig
var source = Source.init(allocator, "test.zig", code);
defer source.deinit();

// Check if type info is available
if (source.hasTypeInfo()) {
    // Query by declaration name
    if (source.findDeclType("x")) |ti| {
        // Use type information
    }

    // Check declaration properties
    if (source.isDeclFunction("foo")) { /* ... */ }
    if (source.isDeclType("MyStruct")) { /* ... */ }
    if (source.isDeclPublic("exported")) { /* ... */ }
}
```

### CheckerContext type access

The `CheckerContext` (`src/checker.zig`) includes an optional per-file `TypeContext`. A context pointer alone does not prove frontend availability. Use `hasTypeInfo()` for best-effort availability or `TypeContext.ensureAvailable()` when failures must propagate. An optional checker must keep its AST fallback when type information is unavailable:

```zig
pub fn checkAst(
    source: *Source,
    allocator: std.mem.Allocator,
    diagnostics: *std.ArrayList(Diagnostic),
    context: CheckerContext,
) CheckerError!void {
    // Check if type info is available
    if (context.hasTypeInfo()) {
        // Use type context for type-aware analysis
        if (context.getDeclType("my_var")) |ti| {
            // Make decisions based on type
        }

        // Classify identifiers for naming rules
        const kind = context.classifyIdentifier("MyType");
    }
}
```

### Typed IR nodes

`IrNode` (`src/ir.zig`) carries optional type information:

```zig
pub const IrNode = struct {
    tag: IrTag,
    ast_node: ?u32,
    source_range: ?SourceRange,
    operand_node: ?u32,
    operand2_node: ?u32,
    type_info: ?TypeInfo,  // Best-effort type annotation

    // Type query helpers
    pub fn hasType(self: *const IrNode) bool;
    pub fn getTypeKind(self: *const IrNode) ?TypeInfo.TypeKind;
    pub fn isErrorUnion(self: *const IrNode) bool;
    pub fn isOptional(self: *const IrNode) bool;
    pub fn isPointer(self: *const IrNode) bool;
    pub fn isInteger(self: *const IrNode) bool;
};
```

### CfgBuilder type annotation

The `CfgBuilder` (`src/cfg/builder.zig`) can annotate IR nodes with types during CFG construction:

```zig
// Create builder with type context for type-annotated CFG
var type_ctx = TypeContext.init(allocator, &source);
defer type_ctx.deinit();

var builder = CfgBuilder.initWithTypes(allocator, &type_ctx);
var cfg = (try builder.buildFromFn(&source, fn_node)) orelse return;
defer cfg.deinit();

// Inspect available annotations. Unresolved nodes remain untyped.
for (cfg.nodes.items) |node| {
    if (node.ir_node.isErrorUnion()) {
        // Handle error union
    }
}
```

Declaration annotations use the supplied `TypeContext`. A builder without that context does not load ZIR implicitly. Synthetic `try_expr` and `catch_expr` error-union annotations describe control flow, not complete declaration metadata.

On a disk-cache hit, the analyzer restores live declaration annotations from the current source and type context. This restores source-backed metadata that the compact CFG format does not persist.

## Analysis engine

The analysis engine (`src/engine.zig`) implements a worklist-based traversal of the CFG to build an exploded graph for path-sensitive static analysis. The facade in `src/engine.zig` re-exports from `src/engine/` (analysis, state, values, constraints, summaries, store, dot).

### Concepts

#### ProgramPoint

A `ProgramPoint` identifies a location in the analysis:

```zig
pub const ProgramPoint = struct {
    node_index: CfgNodeId,
    kind: Kind,       // pre or post
    cfg: *const Cfg,  // CFG identity separates inlined functions

    pub const Kind = enum {
        pre,   // Before node execution
        post,  // After node execution
    };
};
```

For each CFG node, there are two program points: pre-state (before execution) and post-state (after execution).

#### ProgramState

A `ProgramState` represents abstract program state at a given point, storing the environment mapping variables to abstract values:

```zig
pub const ProgramState = struct {
    env: Environment,       // Mapping from variables to abstract values
    cached_hash: ?u64,      // Cached hash for efficient deduplication
};
```

**Operations:** `init`, `clone`, `getVar`, `setVar`, `eql`, `computeHash`.

#### Abstract values

Abstract values represent possible runtime values:

```zig
pub const AbstractValue = union(enum) {
    unknown,              // No information available
    null_val,             // Definitely null
    non_null,             // Definitely not null (actual value unknown)
    int_range: IntRange,  // Integer within a known range
    concrete_int: i64,    // Known concrete integer
    concrete_bool: bool,  // Known boolean
};
```

**Value categories:** `unknown` (default), `null_val`, `non_null`, `int_range`, `concrete_int`, `concrete_bool`.

#### Environment

The `Environment` maps variable identifiers to abstract values:

```zig
pub const Environment = struct {
    bindings: std.AutoHashMap(u32, AbstractValue),
    allocator: std.mem.Allocator,
};
```

Variables are identified by their AST node index.

#### ExplodedNode

An `ExplodedNode` combines a program point and state:

```zig
pub const ExplodedNode = struct {
    point: ProgramPoint,
    state: ProgramState,
    index: u32,
    predecessors: std.ArrayList(u32),
    successors: std.ArrayList(u32),
};
```

#### ExplodedGraph

The `ExplodedGraph` is the central data structure for path-sensitive analysis:

```zig
pub const ExplodedGraph = struct {
    nodes: std.ArrayList(ExplodedNode),
    node_map: std.AutoHashMap(u64, u32),  // For deduplication
    cfg: *const Cfg,
};
```

Deduplicates nodes with identical (point, state) pairs, tracks edges, and maps back to CFG nodes.

### Worklist algorithm

The `AnalysisEngine` uses a worklist-based algorithm:

1. Create entry node at `(pre(entry), initial_state)`
2. While worklist is not empty:
   - Pop a node
   - If at pre-state: apply transfer function, create post-state node
   - If at post-state: create pre-state nodes for all CFG successors
3. Skip nodes that already exist in the graph

```zig
var engine = AnalysisEngine.init(allocator, &cfg);
defer engine.deinit();

try engine.run();

const graph = engine.getGraph();
// Analyze the exploded graph...
```

#### Traversal order: LIFO (depth-first) by design

The worklist is an `ArrayList(WorklistItem)` consumed via `append` and `pop`, which is LIFO and gives a depth-first traversal of the exploded graph.

Why DFS:

- **Deduplication merges identical states.** In the pure-deduplication case, a complete run reaches the same fixed point regardless of traversal order. This claim excludes runs stopped by hard limits or changed by widening.
- **Widening is order-sensitive.** With widening enabled (the default), traversal order can affect precision because `AbstractValue.widen` is not commutative. For example, `int_range[a,b].widen(concrete_int v)` keeps the range when `v` lies inside `[a,b]`, while `concrete_int(v).widen(int_range[a,b])` collapses to `unknown`. DFS vs BFS can therefore change which state arrives at a widening point first and how aggressively values are widened. The engine does not aim to be deterministic across order changes; widening is a precision/termination tool, and the cheaper traversal is preferred.
- **`pop` is O(1).** Removing from the front of an `ArrayList` to get FIFO requires `orderedRemove(0)`, which is O(n); a true order-preserving deque needs `std.fifo.LinearFifo` or a head-index pattern with its own bookkeeping. DFS via `pop` is the cheapest implementation that satisfies the algorithm.
- **Better cache locality.** Items pushed last are popped next, so the processing kernel tends to reuse state freshly written by the transfer function.

When `max_worklist_steps` is exhausted, `run` warns and returns `error.AnalysisLimitExceeded`. The shared analysis handle records `complete = false`. A partial graph is not a complete path proof. Checkers can still perform independent structural or constant-condition checks. `empty-catch-engine` normally needs no engine run at all.

Under a fixed step limit, DFS can explore one branch deeply before another branch. Checkers must not treat unvisited nodes as unreachable.

#### Hard state limits

The defaults are 200,000 worklist steps per run and 50 retained states per program point. A program point includes CFG identity, node, and pre/post position. Its hard state cap includes all call contexts at that point.

At the cap, the graph can widen into a compatible state from the same call context. If no compatible state exists, analysis warns and stops instead of adding a state beyond the cap. A zero engine-level state cap rejects all states. CLI limit flags require positive values.

Widening and subsumption can reduce precision but do not increase the cap. These bounds do not limit total physical memory. CFGs, source snapshots, active analyses, and allocator overhead have separate lifetimes.

### Deduplication

Deduplication merges paths with identical program points and states. Widening controls changing abstract values, while hard step and state limits bound incomplete runs.

### Transfer function

The transfer function models state changes at CFG nodes. It evaluates supported boolean and integer literals from declarations, updates bindings, and applies call, error, and resource models. Unresolved values remain `unknown`.

Environment, constraints, store state, and violations follow explicit clone and ownership rules. Allocation failures propagate without publishing a partially constructed state or transferring ownership twice.

### Branch constraints and path pruning

The engine tracks constraints from branch conditions. When it encounters a branch node with `branch_true` or `branch_false` edges, it extracts constraints and applies them to successor states.

#### Constraints

Constraints represent conditions that must hold on a given execution path:

```zig
pub const Constraint = union(enum) {
    /// Variable compared to an integer value: var <op> value
    int_compare: struct {
        var_id: VarId,
        op: CompareOp,
        value: i64,
    },
    /// Variable compared to null: var == null or var != null
    null_check: struct {
        var_id: VarId,
        is_null: bool,
    },
    /// Boolean variable required to have this value.
    bool_check: struct {
        var_id: VarId,
        expected: bool,
    },
    /// Variable compared to another variable: var1 <op> var2
    var_compare: struct {
        var1_id: VarId,
        op: CompareOp,
        var2_id: VarId,
    },
    /// Literal branch condition.
    literal_bool: struct { value: bool },
};
```

**Comparison operators:** `eq`, `ne`, `lt`, `le`, `gt`, `ge`.

Branch extraction normalizes grouped expressions, reversed integer comparisons, signed literals, and boolean negation. Integer refinement requires a proven operand domain that fits signed 64-bit values. Floating-point, unknown, and wider integer domains do not enter this constraint model. Boolean and null checks use their own constraints.

#### ConstraintManager

The `ConstraintManager` tracks active constraints on a path. Operations: `addConstraint`, `isSatisfiable`, `refineValue`, `clone`.

#### ProgramState with constraints

The `ProgramState` includes a `ConstraintManager`:

```zig
pub const ProgramState = struct {
    env: Environment,
    constraints: ConstraintManager,
    cached_hash: ?u64,
};
```

#### Path pruning

When processing branch edges, the engine extracts constraints from the branch condition, applies the constraint (or its negation), checks satisfiability, and prunes unsatisfiable paths.

**Example:**
```
// Code:
if (x == 5) {
    // then-branch: constraint x == 5
} else {
    // else-branch: constraint x != 5
}

// If x is known to be 10:
// - then-branch is pruned (x == 5 contradicts x == 10)
// - else-branch is explored (x != 5 is satisfiable)
```

#### Value refinement

For a supported integer domain, a constraint can refine an unknown value, such as `x == 5` producing `concrete_int(5)`. A contradictory refinement can prune the path. Lack of type or domain evidence does not justify integer refinement.

#### Satisfiability checking

The `ConstraintManager.isSatisfiable` method checks environment compatibility and constraint consistency (e.g., `x == 5` AND `x == 6` is contradictory).

### Usage example

```zig
const cfg_mod = @import("cfg.zig");
const engine_mod = @import("engine.zig");

// Build CFG from source
var builder = cfg_mod.CfgBuilder.init(allocator);
const cfg = (try builder.buildFromFn(&source, fn_node)) orelse return;
defer cfg.deinit();

// Run analysis
var engine = engine_mod.AnalysisEngine.init(allocator, &cfg);
defer engine.deinit();

try engine.run();

// Examine results
const graph = engine.getGraph();
std.debug.print("Exploded graph has {d} nodes\n", .{graph.nodeCount()});
```

## Error-handling checkers

The engine supports error-handling checkers using CFG and error state tracking.

### EmptyCatchEngineChecker

The `EmptyCatchEngineChecker` (`src/checkers/empty_catch_engine.zig`) declares `.type_requirement = .none`. It detects empty catch blocks from CFG structure and checks top-level catches through syntax. An empty handler's `catch_error` edge goes directly to the merge node.

The normal diagnostic path does not run the analysis engine. A plain CFG dump also needs no engine run. Exploded-graph, annotated-CFG, or path-trace requests trigger a separate `.plain` analysis for visualization. Structural diagnostics remain available if that analysis reaches a limit. Allocation failures still propagate.

### SwallowedErrorChecker

The `SwallowedErrorChecker` (`src/checkers/swallowed_error.zig`) detects catch blocks that swallow errors.

**Detection:** The checker builds a CFG and runs `.plain` analysis to track error paths. It reports non-empty block handlers that reach their catch merge without recognized handling. Returns, potential logging calls, intentional fallback expressions, and storage of the captured error have separate exemptions. Unrelated assignments do not count as error storage.

The engine tracks `ErrorState`: `error_active`, `error_handled`, or `normal`. If analysis is incomplete, the checker uses structural handler traversal without trusting partial engine state. That fallback keeps the same handler exclusions and proves completion through an edge to the catch merge.

### StoreViolationsEngineChecker

The `StoreViolationsEngineChecker` (`src/checkers/store_violations_engine.zig`) reports double-free, free-without-alloc, close-without-open, use-after-free/close, and leaks. It acquires a configured per-function analysis and scans `ProgramState` store violations. Compatible checkers can reuse that analysis through exclusive leases.

The resource call model supports config-defined `free_owned` operations (for deinit-like APIs that free owned resources without freeing the receiver) and applies errdeferred releases on error returns to surface double-free issues on error paths.

#### Ownership escape heuristics

The store model tracks when resources "escape" (ownership transferred) to avoid false leak reports.

**1. Field assignment escape**

Resources assigned to fields of long-lived owners are marked escaped:

```zig
// Resource escapes via field assignment
cache.entries = entries;  // entries is marked escaped
```

The `recordOwnershipFromFieldAssign` function detects this when the LHS is a field access, the base is `self` (method receiver), the base is a pointer type, or the base is not a locally-tracked allocation.

**2. Container method escape**

Resources passed to container insertion methods are marked escaped:

```zig
// Resource escapes via container insertion
list.append(allocator, data);    // data is marked escaped
list.insert(allocator, 0, item); // item is marked escaped
map.put(key, value);             // key and value are marked escaped
```

The `trackEscapesFromCall` function recognizes container methods: `append`, `appendAssumeCapacity`, `appendSlice`, `insert`, `put`, `putNoClobber`, etc.

**3. Init-like function escape**

Resources passed to functions with initialization-like prefixes are marked escaped:

```zig
// Resource escapes via init function
initCache(cache, entries, ...);  // all params are marked escaped
setupComponent(ptr, data);       // all params are marked escaped
```

Recognized prefixes: `init`, `setup`, `set`, `store`, `register`, `add`, `push`.

Escape tracking is performed **before** function inlining.

#### Error-path leak policy

Leak violations are only reported on normal return paths. Error returns suppress leak reports (caller handles cleanup via `errdefer`).

The engine detects error returns via literal error values (`return error.SomeError`) and type-based detection (`TypeContext`).

#### Type-based resource detection

The store model identifies resource operations using a priority-based system:

1. Config-defined models (highest priority)
2. Built-in name patterns (`alloc`/`free`, `create`/`destroy`, `open`/`close`)
3. Type-based detection (methods returning `File`, `Dir`, `Socket`, etc.)

#### Configuration integration

The checker accepts a `Config` pointer via `AnalysisEngine.setConfig()`. Config-defined resource models are checked before built-in heuristics.

```zig
// In checker code
var engine = AnalysisEngine.initWithSource(allocator, cfg, src);
engine.setTypeContext(&type_ctx);
if (context.config) |config| {
    engine.setConfig(config);
}
```

### Registration

These checkers are registered in `src/cli/registry.zig`:

```zig
try analyzer.registerChecker(&EmptyCatchEngineChecker.checker);
try analyzer.registerChecker(&OptionalUnwrapEngineChecker.checker);
try analyzer.registerChecker(&SwallowedErrorChecker.checker);
try analyzer.registerChecker(&UnreachableCodeChecker.checker);
try analyzer.registerChecker(&StoreViolationsEngineChecker.checker);
```

## Interprocedural analysis

The engine supports limited interprocedural analysis through function inlining.

### Function inlining

When the engine encounters a function call, it attempts to inline the callee's CFG if:

1. Source is available (initialized with `initWithSource()`)
2. The call resolves to a direct identifier call in the same file
3. The depth limit is not exceeded (default: 3)
4. The callee is not already active through direct or indirect recursion

Eligible calls can use summaries instead of inlining. Other calls remain opaque to body execution, although configured or built-in resource models can still describe specific effects.

### Call stack tracking

The `ProgramState` maintains a call stack:

```zig
pub const CallSite = struct {
    call_node: u32,      // CFG node of the call instruction
    caller_cfg: *const Cfg,  // CFG containing the call
    return_node: u32,    // Node to continue from after return
};
```

When inlining: increment depth, push call site, analyze callee. On callee exit: pop call site, decrement depth, continue at caller.

### Configuration

```zig
var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
defer engine.deinit();

engine.setMaxInlineDepth(5);  // Increase inline depth to 5
try engine.run();

std.debug.print("Inlined {d} calls\n", .{engine.getInlinedCallCount()});
```

### External calls

Calls outside the same-file direct-call model remain external to body execution. These include cross-file and indirect calls, recursive calls, and calls beyond the depth limit. Type queries and resource models can still recognize some external return types and effects. They do not execute the external body, and unsupported effects remain conservative.

### Example

```zig
// Source code being analyzed
fn helper(x: i32) i32 {
    return x + 1;
}

fn main() void {
    const a = 5;
    const b = helper(a);  // This call will be inlined
    _ = b;
}

// Analysis with inlining
var engine = AnalysisEngine.initWithSource(allocator, &main_cfg, &source);
try engine.run();

// The analysis will trace through both main() and helper()
// tracking that helper() is called with x = 5 (if constant propagation is enabled)
```

### Limitations

- Body execution supports direct function calls with identifier callees
- Recursive calls remain opaque, and other inlining stops at the depth limit
- Cross-file calls remain external even when project-aware lookup resolves their types

## Function summaries

The engine supports function summaries to avoid re-analyzing the same function body at each call site.

### Summary contents

A `FunctionSummary` has fields for the following information. Generated summaries populate conservative error and effect facts, not a complete model of every return value or constraint:

- **Preconditions**: Constraints on parameter values that affect behavior
- **Postconditions**: Constraints on the return value
- **Error behavior**: Whether the function may return an error, always returns an error, or may not return
- **Return value**: Abstract value representing the return (e.g., `unknown`, `concrete_int`, etc.)
- **Side effects**: Whether the function may modify global state

```zig
pub const FunctionSummary = struct {
    fn_ast_node: u32,              // AST node of the function
    preconditions: ArrayList(Constraint),   // Input constraints
    postconditions: ArrayList(Constraint),  // Output constraints
    may_return_error: bool,        // Can return an error
    always_returns_error: bool,    // Always returns an error
    may_not_return: bool,          // May not return (e.g., @panic)
    return_value: AbstractValue,   // Abstract return value
    has_side_effects: bool,        // May modify global state
    use_count: u32,                // Number of times applied
};
```

### Summary cache

Each engine's `SummaryCache` stores summaries keyed by function AST node identity. A shared engine lease can reuse them within the file. The disk cache does not persist summaries:

```zig
var cache = SummaryCache.init(allocator);
defer cache.deinit();

// Check if a summary exists
if (cache.get(fn_node)) |summary| {
    // Use the cached summary
} else {
    // Compute a new summary
}

// Cache statistics
const stats = cache.getStats();
std.debug.print("Hits: {d}, Misses: {d}, Count: {d}\n",
    .{stats.hits, stats.misses, stats.count});
```

### Summary application

For an eligible call, the engine finds or computes a summary, checks its applicability, then applies it or tries inlining. A summary that can return either success or error produces separate outcomes. An always-error summary produces only the error outcome. Applying a successful outcome does not clear a pending caller error.

Postconditions apply once before the fork. Unsatisfiable outcomes are pruned, and allocation failures propagate. This preserves error paths without claiming a complete error-union value model.

```zig
// The engine automatically uses summaries when available
var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);

// Summaries are enabled by default
engine.setUseSummaries(true);

try engine.run();

// Check summary statistics
std.debug.print("Summary uses: {d}\n", .{engine.getSummaryUseCount()});
const cache_stats = engine.getSummaryCache().getStats();
std.debug.print("Cache hits: {d}, misses: {d}\n",
    .{cache_stats.hits, cache_stats.misses});
```

### Summary generation

Summary generation inspects the signature, error-returning constructs, and CFG exits. It distinguishes possible error returns from functions whose returning paths all produce errors. Implicit successful exits remain success possibilities. Unknown return types and effects keep conservative defaults. Purity checks also inspect calls within initializers and return expressions.

### Configuration

```zig
var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);

// Disable summaries. Eligible non-recursive calls can still inline.
engine.setUseSummaries(false);

// Set inline depth limit
engine.setMaxInlineDepth(5);
```

## Build metadata integration

The analyzer integrates build metadata and target configuration, allowing rules and checkers to access platform-specific information.

### Build metadata types

The `build_metadata.zig` module provides types for build configuration:

```zig
pub const TargetArch = enum {
    x86_64,
    aarch64,
    arm,
    riscv64,
    wasm32,
    other,
};

pub const TargetOS = enum {
    linux,
    windows,
    macos,
    freestanding,
    wasi,
    other,
};

pub const TargetConfig = struct {
    arch: TargetArch,
    os: TargetOS,
    abi: ?[]const u8,
};

pub const BuildMetadata = struct {
    target: TargetConfig,
    optimize_mode: ?OptimizeMode,
    root_source_file: ?[]const u8,
};
```

### CLI integration

The `--target` flag specifies a target triple:

```bash
zwanzig --target x86_64-linux-gnu src/
zwanzig --target aarch64-macos src/
```

The target triple is parsed into `BuildMetadata` and propagated through the analyzer. Other CLI flags (`--do`/`--skip`, `--config`, `--format`, `--max-steps`, etc.) configure the analyzer and engine.

### Analysis engine integration

Build metadata is stored in `Analyzer`, `AnalysisEngine`, and propagated to `ProgramState`:

```zig
// In Analyzer
var analyzer = Analyzer.init(allocator);
if (build_metadata) |metadata| {
    analyzer.setBuildMetadata(metadata);
}

// In AnalysisEngine
var engine = AnalysisEngine.init(allocator, &cfg);
if (analyzer.getBuildMetadata()) |metadata| {
    engine.setBuildMetadata(metadata);
}

// In ProgramState (as a shared pointer)
pub const ProgramState = struct {
    env: Environment,
    constraints: ConstraintManager,
    error_state: ErrorState,
    build_metadata: ?*const BuildMetadata,  // Shared, not owned
    // ...
};
```

### Accessing build metadata

Rules and checkers access build metadata from `ProgramState`:

```zig
pub fn check(state: *const ProgramState) void {
    if (state.build_metadata) |metadata| {
        if (metadata.target.arch == .wasm32) {
            // Apply WASM-specific checks
        }
        if (metadata.target.os == .freestanding) {
            // Apply freestanding-specific checks
        }
    }
}
```

### Use cases

Build metadata enables target-specific analysis: platform-specific APIs, size optimization, freestanding checks, ABI compatibility.

### Native target detection

When no `--target` is specified, the analyzer uses native target from `@import("builtin").target`:

```zig
pub fn fromNative() BuildMetadata {
    const native = @import("builtin").target;
    // Extract arch, os from native target
    return BuildMetadata{
        .target = TargetConfig.init(arch, os, null),
        .optimize_mode = null,
        .root_source_file = null,
    };
}
```

## Incremental cache

The disk cache reuses CFG artifacts across runs. It stores CFGs and limited type flags, not diagnostics or complete compiler metadata. The per-file `AnalysisCache` is separate and reuses engine runs only within the current file analysis.

### Cache architecture

The cache system has two components:

1. `Cache` (`src/cache.zig`): Low-level persistent storage
2. `CachedArtifacts` (`src/cached_artifacts.zig`): Serialization of intermediate artifacts

### Cache key components

Cache keys (`CacheKey`) are computed from multiple sources:

```zig
pub const CacheKey = struct {
    file_hash: [32]u8,      // SHA-256 of file content
    target_hash: [32]u8,    // Hash of target architecture/OS/ABI
    version_hash: [32]u8,   // Hash of tool and embedded frontend versions
    config_hash: [32]u8,    // Rules, type availability, and optional project fingerprint
};
```

**Invalidation triggers:** Changes to file content, target, tool or embedded frontend version, enabled rules, or type-info availability. When project sources are prepared, their fingerprint also invalidates stale entries.

### Cache behavior

**Key principle:** A cache hit reuses CFGs but does not skip syntax validation or enabled checks. Diagnostics are recomputed on every run.

```zig
var analyzer = Analyzer.init(allocator);
defer analyzer.deinit();
try analyzer.enableCache();
try analyzer.registerChecker(&MyChecker.checker);

// Each isolated result owns freshly computed diagnostics.
var first = try analyzer.analyzeFileResult("test.zig");
defer first.deinit(allocator);

var second = try analyzer.analyzeFileResult("test.zig");
defer second.deinit(allocator);
```

Using `analyzeFile()` instead appends diagnostics to the analyzer's existing result list. A second call does not reset that list.

### Cached artifacts

`CachedArtifacts` owns CFGs per function and records `had_type_info`. Checkers populate these CFGs through `getOrBuildCfg()`, and the analyzer serializes them when disk caching is enabled. The compact format stores basic IR type fields, not complete ZIR, source-backed type metadata, function summaries, or engine states.

On a warm load, the analyzer restores declaration annotations from the current `TypeContext`. CFG storage and function names remain owned by `CachedArtifacts`, independently of shared engine leases.

```zig
pub const CachedArtifacts = struct {
    allocator: std.mem.Allocator,
    cfgs: std.AutoHashMap(u32, *Cfg),
    had_type_info: bool,
};
```

### Serialization format

Binary format with magic bytes (`ZWCA`), format version, and payload. Version changes invalidate old cache entries.

### CLI usage

Enable caching with `--cache`:

```bash
zwanzig --cache src/
```

Cache files are stored in `.zwanzig-cache/` in the current directory.

### Cache directory structure

Cache files are stored in `.zwanzig-cache/` with hash-based filenames. Each file contains a header (version, key hashes, timestamp, data length) and body (serialized `CachedArtifacts`).

## Variable identification (VarId)

The analysis engine uses a `VarId` type for identifying variables. Variables are identified by their AST node index:

```zig
// In src/ids.zig
pub const VarId = enum(u32) { _ };

pub fn varId(value: u32) VarId {
    return @enumFromInt(value);
}

pub fn varIndex(id: VarId) u32 {
    return @intFromEnum(id);
}
```

Benefits: unique within a compilation unit, direct mapping to source locations, no separate symbol table, works with nested scopes.

### Environment bindings

The `Environment` maps `VarId` to `AbstractValue`:

```zig
// In src/engine/env.zig
pub const Environment = struct {
    bindings: std.AutoHashMap(VarId, AbstractValue),
    allocator: std.mem.Allocator,
};
```

For a declaration, the engine creates a `VarId` and binds a supported initial abstract value, or `unknown` when evaluation is unavailable. Variable reads resolve the binding for transfer functions and constraint checks.
