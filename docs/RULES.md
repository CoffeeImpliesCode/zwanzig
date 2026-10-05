# Rules and checkers

Zwanzig has AST/token rules (legacy `Rule` interface) and checker-based passes (`Checker` interface). Both share the same namespace for `--do`/`--skip` filtering.

## Rules (Rule interface)

### dupe-import

Flags duplicate `@import` statements that repeat the same full import path (module string plus any chained field access), usually from copy-paste mistakes or forgotten refactoring.

**Bad:**
```zig
const std = @import("std");
const mem = @import("std");  // Duplicate import of "std"
```

**Good:**
```zig
const std = @import("std");
const mem = std.mem;  // Use the already imported std
```

### todo

Finds TODO comments in line, doc (`///`, `//!`), and block (`/* */`) comments. Matching is case-insensitive (`TODO`, `todo`, etc.).

**Example:**
```zig
fn processData(data: []const u8) void {
    // TODO: implement error handling
    _ = data;
}
```

Produces a hint with the TODO's message. If no message is provided (e.g. `// TODO:`), the rule reports a default message.

### file-as-struct

Enforces naming conventions based on whether a file acts as a struct (has top-level fields):

- Files with top-level fields should have a capitalized file name (e.g., `MyType.zig`)
- Files without top-level fields should have a lowercase file name (e.g., `utils.zig`)

**Bad (struct-like file with lowercase name):**
```zig
// mytype.zig - should be MyType.zig
count: usize,
name: []const u8,

pub fn init() @This() {
    return .{ .count = 0, .name = "" };
}
```

**Good (struct-like file with capitalized name):**
```zig
// MyType.zig
count: usize,
name: []const u8,

pub fn init() @This() {
    return .{ .count = 0, .name = "" };
}
```

**Bad (module file with capitalized name):**
```zig
// Utils.zig - should be utils.zig
const std = @import("std");

pub fn helper() void {
    std.debug.print("Hello\n", .{});
}
```

**Good (module file with lowercase name):**
```zig
// utils.zig
const std = @import("std");

pub fn helper() void {
    std.debug.print("Hello\n", .{});
}
```

### unused-decl

Detects unused container-level `const`, `var`, and `fn` declarations that aren't exported. The per-file check is conservative:
- Exported (`pub`) declarations are ignored during default per-file analysis (they may be used externally)
- `export` and `extern` declarations are ignored (they may be used by other compilation units)
- Underscore-prefixed names (e.g., `_unused`) are ignored (explicit opt-out)
- Special names like `main` and `panic` are ignored (entry points)

When `unused-decl` is enabled and more than one file is analyzed, zwanzig also runs a project pass over all analyzed files. That pass reports public top-level declarations that are not referenced by any other analyzed file, while ignoring `build.zig`'s `build` entrypoint, package API roots discovered from `root_source_file` in analyzed or workspace `build.zig` files, and alias-style re-exports to avoid library facade noise. Declarations exposed through another used public declaration's type, signature, field, initializer surface, typed receiver method call, or result-location method call are treated as used. Method references through nested inline namespaces and type aliases are also resolved.
Private file-as-struct methods called through `self.method` are treated as used, even when an unrelated field has the same name. A bare field read never counts as a method call, so a same-named field on another type does not mask an unused method.
Calls to the real `std.testing.refAllDecls` and `refAllDeclsRecursive` also keep the target container's declarations reachable. Immutable aliases of the imported `std` module or its `testing` namespace are supported. Fake namespaces, shadowed bindings, and mutable aliases do not grant this exemption.
Cyclic type aliases and namespace re-exports stop at the repeated binding or file. They do not prevent resolution of independent declarations.
Guarded `@import("root")` references follow the one compilation root that reaches the file through its build module graph, including named module imports. A file that two compilation roots reach has no single root, so its `@import("root")` references resolve to no file rather than to an arbitrary root. Live comptime checker calls count as uses; unrelated root helpers can still be reported unused.
Bounded type and import searches log a warning when they exhaust their resolution budget. The warning names the search and its frame limit; the conservative result is not proof that the type or reference is absent. Cycle detection remains separate from budget exhaustion.
Contextual constants such as `.empty` count as references when the result type identifies their container, including typed initialization, assignment, and return expressions. A same-named constant in another container remains eligible for an unused-declaration report.
Project-wide unused-public reports require valid syntax in every prepared source and build file. If parsing fails, Zwanzig defers those reports rather than treating missing references as non-use. Per-file checks still run on valid siblings.

**Bad:**
```zig
const unused_value = 42;  // Never used

fn unused_helper() void {}  // Never called

pub fn main() void {
    // ...
}
```

**Good:**
```zig
const config = 42;

fn helper() void {}

pub fn main() void {
    _ = config;
    helper();
}
```

### unused-parameter

Detects function parameters that are never referenced.

- Parameters starting with `_` are ignored (explicit opt-out)
- References in range, labeled, and nested expressions count as uses when they resolve to the parameter. Comptime parameters referenced by fields or methods of a returned anonymous container also count as used. Shadowed names do not count.

**Bad:**
```zig
fn add(unused: i32, value: i32) i32 {
    return value + 1;
}
```

**Good:**
```zig
fn add(value: i32) i32 {
    return value + 1;
}
```

### unreachable-code

Detects code after an unconditional terminator (`return`, `unreachable`) or after fully terminating branches (`if`, `switch`, `while`).

**Bad:**
```zig
fn foo() void {
    return;
    const x = 42;  // Unreachable - after unconditional return
}

fn bar(x: i32) void {
    if (x > 0) {
        return;
    } else {
        return;
    }
    const y = 10;  // Unreachable - both branches return
}
```

**Good:**
```zig
fn foo() void {
    const x = 42;
    return;
}

fn bar(x: i32) void {
    const y = 10;
    if (x > 0) {
        return;
    }
}
```

### empty-defer

Flags empty `defer {}` blocks.

**Bad:**
```zig
fn foo() void {
    defer {}  // Empty defer - does nothing
}
```

**Good:**
```zig
fn foo() !void {
    var file = try std.fs.cwd().openFile("test.txt", .{});
    defer file.close();
}
```

### empty-errdefer

Flags empty `errdefer {}` blocks.

**Bad:**
```zig
fn foo() !void {
    errdefer {}  // Empty errdefer - does nothing
}
```

**Good:**
```zig
fn foo() !void {
    var allocator = std.heap.page_allocator;
    var buffer = try allocator.alloc(u8, 1024);
    errdefer allocator.free(buffer);
    // ...
}
```

### shadowed-variable

Detects variable shadowing across scopes, including payloads (if/for/while/switch/catch/errdefer).

Notes:
- Underscore-prefixed identifiers (e.g. `_x`, `_unused`) are ignored and may intentionally shadow.

**Bad:**
```zig
fn foo(x: i32) void {
    const x = 5; // Shadows parameter
    _ = x;
}
```

**Good:**
```zig
fn foo(x: i32) void {
    const value = 5;
    _ = x;
    _ = value;
}
```

### sentinel-alloc

Detects sentinel-terminated allocations that cause memory mismatch bugs when freed.

Sentinel-terminated allocations (e.g., `[:0]u8`) allocate `len + 1` bytes but the slice length is `len`. If stored in a non-sentinel type (`[]u8`), the sentinel info is lost and freeing causes an allocation size mismatch.

**Bad:**
```zig
fn readFile(allocator: std.mem.Allocator, file: std.fs.File) ![]u8 {
    // dupeZ allocates len+1 bytes but returns [:0]u8
    // If stored as []u8, freeing loses the +1 byte info
    const content = try allocator.dupeZ(u8, "hello");
    return content; // Type erased to []u8, size mismatch on free
}
```

**Good:**
```zig
fn readFile(allocator: std.mem.Allocator, file: std.fs.File) ![:0]u8 {
    // Preserve the sentinel type
    const content = try allocator.dupeZ(u8, "hello");
    return content;
}

// Or use non-sentinel allocation if sentinel isn't needed
fn readFileNoSentinel(allocator: std.mem.Allocator, file: std.fs.File) ![]u8 {
    const content = try allocator.dupe(u8, "hello");
    return content;
}
```

Detected functions:
- `dupeZ` - always creates null-terminated copy
- `allocSentinel` - always creates sentinel-terminated allocation
- `allocPrintSentinel` - always creates sentinel-terminated string
- `allocWithOptions` with non-null sentinel parameter
- `readToEndAllocOptions` with non-null sentinel parameter

The rule uses shared result-location resolution for casts, variable declarations, assignments, and returns. An untyped local initialized directly from a sentinel allocation keeps the inferred sentinel type. Explicit coercion to `[]T` remains diagnostic.

### return-local-ptr

Detects functions that return slices or pointers derived from local stack buffers. This catches use-after-return bugs where the returned data points to memory that becomes invalid when the function returns. The rule only reports when the function’s return type is a pointer/slice (including optional or error-union wrappers).

The rule uses heuristics to detect the pattern:
1. A local array variable is declared (e.g., `var buf: [N]T = undefined;`)
2. Its address is passed to a function call (`&buf`)
3. The result of that call (or a field of it) is returned
4. Or the local buffer itself is returned as a pointer/slice (e.g., `return &buf` or `return buf[0..]`)

**Bad:**
```zig
fn getMembers(tree: *const Ast, node_idx: u32) ?[]const Node.Index {
    var buf: [2]Node.Index = undefined;  // Local buffer on stack
    // containerDeclTwo fills buf and returns struct with .members pointing to buf
    return tree.containerDeclTwo(&buf, node_idx).ast.members;  // Dangling pointer!
}
```

**Good:**
```zig
fn getMembers(tree: *const Ast, node_idx: u32, buf: *[2]Node.Index) ?[]const Node.Index {
    // Buffer passed from caller, stays alive after return
    return tree.containerDeclTwo(buf, node_idx).ast.members;
}

// Caller:
var buf: [2]Node.Index = undefined;
const members = getMembers(tree, node_idx, &buf);
```

This rule complements `stack-escape-engine` by catching patterns where the escape happens through an intermediate function call that the dataflow analysis can't track.

### deinit-lifecycle

Detects two lifecycle patterns that often produce double-cleanup bugs during error unwind:

- **Warning:** the same cleanup call (for example, `x.deinit()`) is registered in both `defer` and `errdefer` within the same block.
- **Hint:** a cleanup call such as `x.deinit()` or `x.close()` is followed later in the same block by `x = try ...`, while a deferred cleanup for the same method is active. Any intervening statements are allowed, as long as the receiver is not assigned a new value first.

The hint does not trigger when:

- The reinitialization is infallible (`x = make()`), since no error unwind can occur.
- The receiver is assigned a non-`try` value before the `try` assignment, resetting it to a valid state.
- The active deferred cleanup uses a different method than the direct call (`defer x.close()` with `x.deinit()` does not match).

Receiver matching handles simple variables and field chains such as `holder.value.deinit()`, so lifecycle checks apply to cleanup methods on nested resources as well as local variables.
For allocator `free` and `destroy` calls, cleanup identity includes the cleaned argument. Calls that clean different values do not match.

**Bad (warning):**
```zig
fn run() !void {
    var value = Obj{};
    errdefer value.deinit();
    defer value.deinit(); // same cleanup also in errdefer
}
```

**Potentially risky (hint), applies to any cleanup method:**
```zig
fn run() !void {
    var stream = Stream{};
    defer stream.close();
    stream.close();
    stream = try reopen(); // if reopen() fails, defer calls close() on already-closed stream
}
```

**Allowed — infallible reinit:**
```zig
fn run() !void {
    var value = Obj{};
    defer value.deinit();
    value.deinit();
    value = makeObj(); // no try, no error unwind possible
}
```

**Allowed — non-try assignment before try:**
```zig
fn run() !void {
    var value = Obj{};
    defer value.deinit();
    value.deinit();
    value = makeObj();        // resets receiver to a valid state
    value = try makeObjFallible(); // no double-deinit risk now
}
```

### identifier-style

Enforces Zig naming conventions:

- Types: PascalCase
- Functions: camelCase, except functions declared to return `type`, which use PascalCase
- Variables/constants/parameters/payloads: snake_case (lowercase); SCREAMING_SNAKE_CASE only when mirroring established external conventions (e.g., `std.posix.ENOENT`)
- Namespaces/modules declared as `const` structs may use lowercase (e.g., `std.mem`)
- Direct `@import` aliases for namespaces and file structs may use lower_snake_case or PascalCase. Imported value constants must use snake_case.
- Quoted identifiers (e.g., `@"weird-name"`) are exempt from these checks
- Explicit `const Name: type = ...` aliases use PascalCase. When type info is available, other type aliases and function type aliases are treated as types and should use PascalCase. Heuristics also treat C-style `*_t` aliases as types (lowercase `*_t` names are allowed when mirroring external conventions like `fd_t`)
- Type-valued builtin, factory, conditional, and switch expressions use PascalCase. Standard-library factories such as `std.StaticBitSet(256)` require a verified `std` import. A local `std` shadow does not get this exemption.
- `@typeInfo(T)` returns a value, not a type. Its result uses snake_case.
- Payloads from `?type` fields of a verified `@typeInfo` switch capture may use PascalCase. Examples include `Union.tag_type` and `Fn.return_type`. Ordinary value payloads still use snake_case.
- Aliases of namespace member types keep PascalCase. The resolved member declaration, not the spelling of the member name, determines whether it is a type. A member of a namespace declared by another file produces no type verdict from this rule, because the walk stops at an import whose file it never reads. A chain longer than the walk's hop budget and a cycle among the aliases are not that case: both leave the member unproved rather than exempt, so the spelling-based fallback behind the type information classifies that member from its spelling. The type information and that fallback read the file under analysis only. They never consult another file for a member.
- Type fields such as `@typeInfo(T).pointer.child` use PascalCase. A labeled block is type-valued only when every reachable exit yields a type and each labeled break reaches that block; value, mixed, and fall-through exits do not qualify.
- Member values keep snake_case, including aliases of `std.base64.standard.Encoder` and `Decoder`, and reads of flag fields.

**Bad:**
```zig
const MaxValue = 10;

fn DoThing(BadParameter: ?i32) void {
    if (BadParameter) |Value| {
        _ = Value;
    }
}
```

**Good:**
```zig
const max_value = 10;

fn doThing(good_param: ?i32) void {
    if (good_param) |value| {
        _ = value;
    }
}
```

## Checkers (Checker interface)

### unreachable-code-engine

Detects constant-condition branches and proven contradictions under immutable scalar guards. Constant `true`/`false` conditions include const boolean identifiers and constant expressions such as `(1 + 1) == 2`.

Path-sensitive reports require complete engine analysis and proof from enclosing guards. An absent graph node alone is not proof. Constant-condition checks still run when an engine limit prevents a complete analysis.

A compile-time assertion guard is not reported as runtime dead code. Both halves must hold. The branch sits inside an explicit `comptime` scope, and every statement of its body is a `@compileError(...)` call or a call to a verified `std.debug.assert`. The shape must be unconditional, so an `if` with an `else` and a `while` with a `continue` or an `else` stay reported. A `comptime` branch that runs application logic, a runtime branch whose body only asserts, and every runtime constant or contradictory guard stay reported.

**Bad:**
```zig
fn foo() i32 {
    if (false) {
        return 1;  // Unreachable - condition is always false
    }
    return 0;
}

fn bar() i32 {
    if (true) {
        return 1;
    } else {
        return 0;  // Unreachable - condition is always true
    }
}

fn baz() void {
    while (false) {
        doWork();  // Unreachable - loop never executes
    }
}
```

**Good:**
```zig
fn foo(condition: bool) i32 {
    if (condition) {
        return 1;
    }
    return 0;
}
```

### optional-unwrap

Flags forced optional unwraps using `.?`, which panic at runtime if the value is `null`. Prefer handling the optional with `if (opt) |value|` or `orelse`.

The `optional_unwrap_test_severity` config setting selects `hint`, `warning`, or `error` for unwraps in test bodies. It defaults to `warning`. Nested function and method bodies, and production bodies, keep `warning`. The setting cannot disable the check. A hint still makes the CLI exit with code 1.

An unwrap passed to a `std.testing` expectation is skipped before any severity applies. The recognized names are `expect`, `expectEqual`, `expectEqualStrings`, `expectEqualSlices`, `expectEqualDeep`, `expectApproxEqAbs`, `expectApproxEqRel`, `expectError`, `expectFmt`, and `assert`. The callee must be reached through a verified `std.testing` namespace or a `const` alias of one. A bare `expect(...)` callee is accepted only inside a `test` body. A `testing` namespace of the user's own gets no exemption.

The checker can replay a deterministic local lookup over a retained prefix when a matching successful lookup guarded each stored row. This proof requires a fixed-size buffer and its counter declared in the analyzed function, a capacity guard, and stores that write the counter's own slot and are paired with a one-step `+ 1` move of it. Between the guard and the replay the lookup inputs, the buffer, and the count must all be unchanged; any other write must land in storage this function owns, and every call that runs in between must be proved pure on its arguments. Buffer, count, and input mutations, escapes through a call, address, or cast, unwritten slots, and any other loop shape keep the warning; for those, check for null in the consuming loop.

**Bad:**
```zig
fn readConfig(opt: ?[]const u8) []const u8 {
    return opt.?; // Panics if opt is null
}
```

**Good:**
```zig
fn readConfig(opt: ?[]const u8) []const u8 {
    return opt orelse "default";
}
```

#### Recognized safe patterns

The checker uses flow analysis to recognize patterns where the optional is non-null before the unwrap. These **do not produce warnings**:

**Null check guard:**
```zig
if (opt != null) {
    const value = opt.?;  // Safe: guarded by null check
}
```

**Early return guard:**
```zig
if (opt == null) {
    return null;
}
const value = opt.?;  // Safe: null case already returned
```

**Compound null check:**
```zig
if (a == null or b == null) {
    return null;
}
const sum = a.? + b.?;  // Safe: both guarded
```

**Short-circuit evaluation:**
```zig
// Safe: .? only evaluated when opt is non-null
return opt != null and opt.? == expected;
return opt == null or opt.? != expected;
```

**Ternary if expression:**
```zig
const value = if (opt != null) opt.? else 0;  // Safe: then branch guarded
```

**Lazy initialization:**
```zig
if (self.cached == null) {
    self.cached = computeValue();
}
return &self.cached.?;  // Safe: initialized above if null
```

**Payload capture:**
```zig
if (opt) |value| {
    _ = value;  // Safe: payload binding
}
```

**Debug assertion guard:**
```zig
std.debug.assert(opt != null);
const value = opt.?;  // Safe: assert guarantees non-null
```

Field guards also support `std.debug.assert(state.value != null)` and `try std.testing.expect(state.value != null)`.
A write through the address of a different struct field preserves the guard.
Replacing the guarded field or passing its address to a mutating call invalidates it.
An ignored `expect` error does not establish a guard.
Writes to independent local values and slice `len` or `ptr` headers preserve field guards. Pointer and slice-element writes can change the referenced object. They invalidate a guard when they reach its field or overlapping union storage. Writes to independent by-value sibling fields preserve the guard, and so does a write to a member a by-value copy owns outright. A pointer member the copy carried still designates what the original pointed at, so `const copy = self.flags; copy.cell.value = null;` writes the field the guard read through the original. A call placed on such a member reaches it too, while a call on the copy's own bytes does not. A pointer member of a type that carries nothing the guard was taken from reaches nothing the guard covers. A call this analysis cannot resolve invalidates a guard on a module-level value, because such a call may write it.


**Switch null-case guard:**
```zig
switch (opt) {
    null => return null,
    else => |value| _ = value,
}
const value = opt.?;  // Safe: null path returned
```

**Comptime type expressions:**
```zig
// Safe: evaluated at compile time, fails as compile error not runtime panic
const ReturnType = @typeInfo(@TypeOf(func)).@"fn".return_type.?;
```

**Method call with catch guard:**
```zig
fn render(self: *Self) void {
    self.ensureTexture() catch return;  // Returns early if texture init fails
    draw(self.texture.?);  // Safe: ensureTexture assigns self.texture on success
}
```

The callee must leave the field non-null on every successful return or fallthrough, after its deferred writes run. A conditional assignment is not rejected on that account: a null check on the field itself hands the fact to the branch that does not see the null, so `if (self.index == null) self.index = 0;` proves the field from an unknown starting state. What does not prove it is an assignment under a condition the analysis does not connect to the field, a later reset, a mutating return operand, or a reset still pending in a `defer` when the scope exits. An `errdefer` body runs only on the error exits, which never reach the caller's unwrap.
A successful `orelse return` or `catch return` before an assignment does not establish a new field fact.

Successful constructor results retain fields proven non-null in their returned values, including fields in nested owner wrappers. Facts belong to the initialized binding, not to unrelated initialized locals. Replacement values, teardown, nullable success results, and mutations invalidate the affected facts.

**Caller-proved field:**
```zig
const Owner = struct {
    index: ?u32 = null,

    fn ensure(self: *Owner, fail: bool) error{Unavailable}!void {
        if (fail) return error.Unavailable;
        if (self.index == null) self.index = 0;
    }

    fn append(self: *Owner, value: u8) void {
        self.index.? += value;  // Safe: every attributed caller fills index first
    }

    fn process(self: *Owner, value: u8, fail: bool) !void {
        try self.ensure(fail);
        var sink: Sink = .{ .owner = self };
        scan(value, &sink);
    }
};

const Sink = struct {
    owner: *Owner,

    // The same name as the owner's reducer, in a container of its own.
    fn append(self: *Sink, value: u8) void {
        self.owner.append(value);
    }
};

/// The parameter carries no type, so the call inside is read from the object
/// each visible caller passes.
fn scan(value: u8, sink: anytype) void {
    sink.append(value);
}
```

Private helpers can use field guards established by every verified caller. The guard must apply to the object passed to the helper, and it must survive the callee's own body: a call the helper makes on a parameter of another type writes only the bytes that parameter owns, while a call it makes on a foreign pointer reaches the module-level object that pointer designates and can store a null back over what every caller proved.

A successful fallible initializer must dominate the call. Generic callback resolution uses the supplied object's method and actual argument positions. The proof includes every operand evaluated before callee entry. An operand that clears the guarded field defeats the proof. Public callees, unverified or recursive callers, escaped callback addresses, and rebound contexts do not establish this proof. Ignored initializer errors and guarded-field mutations preserve warnings.

**Conditional construction:**

A private type factory can establish a field invariant when every visible construction stores a non-null value under the same `comptime bool` condition that guards the unwrap. The constructor's name is not evidence, and the value it stores has to be the factory parameter that condition guards: a local the constructor wrote itself could be assigned again before the field it fills is read.

This proof requires a private factory and no external construction or mutation path for its container. Relevance is transitive rather than nominal: any function this file declares that can produce the container counts, including one that returns a factory's result through a chain of exported helpers. A function the analysis cannot follow leaves the question open. Undefined storage, replacement instances, guarded-field writes, pointer escapes, and opaque calls that can receive the container keep the warning. Local calls are inspected; writes to independent sibling fields remain permitted.
Unclassified aggregate constructions, including contextual array elements and switch results, do not establish this proof.

Public factories, runtime flags, missing assertions, alternate nullable constructions, pointer escapes, and caller or callee resets retain the warning. For these cases, check the field at the use site.

**Try-assign guard:**
```zig
self.path = try allocator.dupe(u8, input);
const basename = getBasename(self.path.?);  // Safe: try succeeded, so path is non-null
```

A successful generic constructor that returns a non-optional container also establishes the assigned field after `try`. Registering an `errdefer` does not run its cleanup on that success path. Optional or unresolved constructor results do not establish this fact.

**Labeled block invariant:**
```zig
const should_process = blk: {
    const value = opt orelse break :blk false;  // Break with false if null
    break :blk value.isValid();
};
if (should_process) {
    use(opt.?);  // Safe: should_process=true implies opt was non-null
}
```

**Error partition guards:**

A local producer and a local predicate can narrow a payload field when both partition the same declared error set, and when a guard before the unwrap calls the predicate with the very error value the producer received. Every tag accepted by the predicate must select a non-null field in the producer. A different error argument, an accepted nullable tag, or a payload that escapes - handed to a call, taken by address, or reached through a cast - keeps the warning. The binding has to be `const` and free of attributes, because a `var` payload can be rewritten between the producer and the unwrap.

**ArrayList removal bound:**
```zig
while (items.items.len > 0) {
    const row = items.pop().?;  // Safe: the guard proves one removal
}
```

A verified `std.ArrayList(T)` length guard on a declared local, parameter, or struct field bounds removals before an unwrap. Each preceding removal spends one element. The guarded pop does not invalidate its own proof. A call or storage write that can empty the list cancels the proof. This includes mutations in the guard condition, body, or loop continuation. A nested loop that removes elements from the same list cancels the bound. A loop over another list spends nothing.

### divide-by-zero-engine

Detects integer division/modulo expressions where the denominator can be zero on at least one reachable path.

The checker is path-sensitive and tracks:
- constant literals
- variable assignments of literal/range-like values
- branch constraints such as `x == 0`, `x != 0`, `x > 0`, `x <= -1`
- mixed-path outcomes (reports "possible" when some paths are safe and some are unsafe)

Integer guard refinement requires a proven domain that fits signed 64-bit values: signed integers up to 64 bits and unsigned integers up to 63 bits. Floating-point, unknown, and wider domains remain conservative.

Assigning a variable retires the branch constraints that refer to it. The engine explores branches that the assignment makes reachable again. Loop widening keeps an interval's stable bound and expands only a changing bound to the integer-domain limit. An increasing counter therefore keeps its starting lower bound.

Labeled `break` statements that exit an enclosing block preserve the constraints of the continuing path. The engine evaluates the break operand and runs reached defers in the exited scopes before the jump. Unresolved labels and loop breaks remain conservative; they do not remove a possible-zero path.

Supported operations:
- binary operators: `/` and `%`
- builtins: `@divTrunc`, `@divFloor`, `@divExact`, `@mod`, `@rem`

**Bad:**
```zig
fn badLiteral() i32 {
    return @divTrunc(10, 0); // division by zero
}

fn badPathSensitive(x: i32) i32 {
    if (x == 0) {
        return @mod(10, x); // modulo by zero on this branch
    }
    return 0;
}
```

**Good:**
```zig
fn goodGuarded(x: i32) i32 {
    if (x != 0) {
        return @divTrunc(10, x); // guarded non-zero denominator
    }
    return 0;
}
```

### empty-catch-engine

Detects empty `catch {}` blocks with structural CFG checks. Normal runs do not execute dataflow analysis for this checker. Exploded-graph, annotated-CFG, and path-trace requests enable the engine for those visualizations; plain CFG dumps do not.

**Bad:**
```zig
const file = std.fs.cwd().openFile("test.txt", .{}) catch {};
```

**Good:**
```zig
const file = std.fs.cwd().openFile("test.txt", .{}) catch |err| {
    std.debug.print("Failed to open file: {}\n", .{err});
    return err;
};
```

### swallowed-error

Detects catch blocks that ignore errors without rethrowing or logging. An error is "swallowed" when the handler:

- Has a non-empty body (not just `catch {}`)
- Doesn't rethrow the error
- Doesn't call any functions (potential logging)
- Simply continues execution
- A fallback expression in `catch` counts as intentional handling. Captured-error storage counts only when every path that continues past the handler stores that payload outside the handler. Immutable pointer aliases to caller-owned storage are supported. Handler-local values, shadowed payloads, unreachable stores, and storage on only some continuing paths do not grant this exemption. Assignments unrelated to the captured error remain swallowed.

If the engine reaches an analysis limit, structural checks still inspect the handler up to its catch merge. A call after the merge does not count as error handling. A handler that terminates with `unreachable` does not silently continue.

A handler can also report failure through the binding the function returns: a boolean rejection or a nonzero failure-count update. A reset, address escape, shadowed binding, different return value, or zero/unknown counter increment does not establish this proof. Empty catches remain the `empty-catch-engine` checker's responsibility.

**Bad:**
```zig
fn bar() i32 {
    var y: i32 = 0;
    const x = foo() catch |_| {
        y = 1;  // Swallowed - just assigns, no logging or rethrow
    };
    _ = x;
    return y;
}
```

**Good:**
```zig
fn bar() !i32 {
    const x = foo() catch |err| {
        return err;  // Rethrows error
    };
    return x;
}

fn baz() i32 {
    const x = foo() catch |err| {
        std.debug.print("Error: {}\n", .{err});  // Logs error
        return 0;
    };
    return x;
}
```

### store-violations-engine

Detects allocator/resource misuse. It reports eight kinds: double-free, double-close, free-without-alloc, close-without-open, use-after-free, use-after-close, leak, and **defer-frees-escapee** (a resource freed by `defer` that has already escaped into an outer container).

**Error-path leak policy:** Leak checks run only on normal return paths. When a function returns an error - a literal error value, a member of a declared error set such as `ConfigError.InvalidConfigFormat`, or a switch or conditional whose branches all return one - the path takes the error state, the `errdefer` cleanup for it is applied, and leak reports are suppressed. This avoids false positives in code that cleans up via `errdefer`.

**Tracking scope:** The rule only tracks resources created by known alloc/open APIs (including built-in models for common std allocator and file/posix patterns). Closing a value that was not opened by a tracked API is reported as "close without tracked open". This includes manually constructed handles (for example, `std.fs.File{ .handle = fd }`) or values provided by external code, unless you model ownership with `resource_models`.

**Release wrappers:** A wrapper that closes the resource it is handed releases the caller's argument, so `compat.closeDir(ctx, &directory)` ends the caller's hold just as `directory.close()` does. The proof comes from the callee's body, never from its spelling: the callee must resolve to one function declaration, its body must be a single unconditional statement that closes a genuine resource field - `std.fs.File`, `std.fs.Dir`, `std.fs.IterableDir`, `std.posix.fd_t`, `std.Io.File` or `std.Io.Dir` - and that wrapper type must carry exactly one such field. A sibling that only reads the argument, a close behind a branch, a close on a second resource field, and a look-alike close on any other type are all still reported, and the caller must pass the resource by address.

**Deferred closes:** Zig 0.16 `std.Io` handles use `file.close(io)` or `dir.close(io)`. Pre-0.16 `std.fs` handles use `file.close()` or `dir.close()`. POSIX descriptors use `std.posix.close(fd)`. A deferred close releases a successful acquisition from a verified standard API, including immutable namespace aliases and method-syntax opens. A failed open creates no handle. Error mapping does not cancel cleanup registered for a successful open. Standard `cwd`, `stdin`, `stdout`, and `stderr` factories return borrowed handles. User-defined look-alike factories and close methods do not get these ownership rules.

A `catch` chain names the producer each arm selected, so a handle opened inside a fallback belongs to that arm. The fallback may sit inside the guarded operand of an outer `catch`, where it still decides arms of its own.

**Returned allocations:** Pointer-preserving casts and returned aggregates retain their allocations. Stores through a cast or a helper that returns its pointer argument retain the resolved destination's ownership, and the same is true of a store through a field that the destination's own declaration filled with a pointer: returning either the field or the binding behind it carries the payload out. What still reports is a dropped destination and a store into a slot whose pointee type cannot be read. A dereference store whose destination is a bare binding to a scalar pointee hands that block nothing to own, so the stored bytes stay the caller's to release - `const length = try allocator.create(usize); length.* = bytes.len;` does not move the bytes - and this holds whether or not the binding writes its pointee type down. A `create` slot whose pointee is a scalar holds no payload. A successful `realloc` transfers ownership to its replacement; returning that replacement is not a leak. Each arm of a `catch` chain around a resize names its own producer, so a fallback that is not a resize leaves the block handed to the primary resize live. A discarded or unreleased replacement remains diagnostic, and a failed resize leaves the original allocation owned by the caller - by the function's `errdefer`, or by the caller it is returned to.

**Arena contexts:** An allocation through a context field can share a caller's proven arena lifetime. The allocator may be reached through nested context fields, or through a local binding of a context that carries another one by value. Every visible call must pass a stable context tied to a genuine arena owner, and a function with no visible call site in the analyzed file proves nothing at all. Each reachable successful exit must release that arena or transfer its state by value through the returned owner. Returning a different arena or a pointer to the caller's local arena does not transfer that lifetime; an owner that carries the arena itself beside other fields does.

A `defer` covers an exit once control reaches its registration, and a `defer` written in an inner block settles every exit reached after that block has run to its end. A matching `errdefer` covers an explicit error return, not a successful return, and an `errdefer` on its own never discharges the lifetime. Replacing the allocator - through an address alias of its field, directly or through a chain of them, through a helper, or through a method - cancels the lifetime proof, as does handing the context on or returning it. Read-only calls and sibling-field writes keep it.

**Diagnostics per path:** When multiple control-flow paths violate the rule, multiple diagnostics can be emitted for the same source line.

**Resources stored in aggregates:** `aggregate[index] = payload` moves the payload's resources into the aggregate, so they travel with it and are released with it. The transfer needs a proof that the store lands in a slot that stays reachable: the store must be the penultimate statement of a `for` body whose last statement is `<index> += 1`, both the aggregate and the index must be declared outside that loop, and nothing else in the function may write the index or reach the aggregate - no second store, no field or whole-aggregate assignment, and no call that takes either by value or address (a proven allocator release is the one call allowed through). Every store that cannot be proven this way leaves the resources with the payload, so a payload dropped by a cursor that advances by zero, a constant index, or a later write through the aggregate is still reported. A whole-binding assignment settles it instead: when nothing names the aggregate after that assignment, the lost aggregate is what gets reported, and the payload it carried goes with that block. A value stored into an aggregate that owns nothing is unchanged.

**Resource modeling:** Built-in allocator detection includes `alloc`/`free`, `dupe`, and `create`/`destroy`. Configurable `resource_models` can add project-specific APIs. Model matching uses shared call resolution for identifier calls, receiver methods, receiver types, and FQNs. `kind: "free_owned"` models APIs like `deinit` that free resources owned by a value without freeing the value itself.

**Defer-frees-escapee detection:** When a value with a pending `defer <allocator>.free(x)` is passed into `append`/`appendSlice`/`appendAssumeCapacity`/`appendSliceAssumeCapacity`/`insert`/`insertSlice` on a container whose declaration outlives the defer's lexical scope, the engine reports a future use-after-free. "Outlives" covers function parameters, top-level decls, `self.field` chains, and any local container declared above the defer's block. The check applies uniformly to defers in any block — `if`, `while`, `for`, `switch` arms, plain `{ ... }`, and the function body itself — because the safety question is always the same: does the container survive past the moment the defer fires? Same-block local containers are not flagged: defers fire in reverse declaration order, so the container is destroyed before the resource. A direct slice argument to `appendSlice`/`appendSliceAssumeCapacity`/`insertSlice` (e.g. `try out.appendSlice(allocator, tmp)` or `tmp[start..end]`) is treated as the byte-copy idiom and not flagged; only nested references (e.g. `&.{tmp}`) trigger the diagnostic for those methods. `errdefer` is not flagged because the canonical `errdefer free(x); try list.append(x)` ownership-transfer idiom is correct on the success path. The `put`/`putAssumeCapacity` family is not flagged because many non-container APIs (caches, writers, IO sinks) share the same names but consume their input during the call; a future type-aware extension can lift these restrictions.

**Bad — double free:**
```zig
fn foo(allocator: std.mem.Allocator) !void {
    var ptr = try allocator.alloc(u8, 1);
    allocator.free(ptr);
    allocator.free(ptr); // double-free
}
```

**Bad — defer frees escapee:**
```zig
fn render(allocator: std.mem.Allocator, run_inputs: *std.ArrayList(Item)) !void {
    if (indent > 0) {
        const spaces = try allocator.alloc(u8, indent);
        defer allocator.free(spaces); // fires when this if-block exits
        try run_inputs.append(allocator, .{ .text = spaces });
    }
    // run_inputs now holds a dangling slice
}
```

**Good (lift the lifetime up to match the container):**
```zig
fn render(allocator: std.mem.Allocator, run_inputs: *std.ArrayList(Item)) !void {
    var spaces_opt: ?[]u8 = null;
    defer if (spaces_opt) |s| allocator.free(s);
    if (indent > 0) {
        const spaces = try allocator.alloc(u8, indent);
        spaces_opt = spaces;
        try run_inputs.append(allocator, .{ .text = spaces });
    }
}
```

### stack-escape-engine

Detects stack-backed pointers/slices that escape the current function scope or async/thread lifetime.

Key patterns:
- Stack array literals (e.g., `&.{ "open", owned_url }`) captured into a long-lived value
- Values captured into detached threads without a guaranteed `join()`
- Returning values that contain stack-backed references
- Escape is reported if any path proves a stack-backed origin can reach a capture sink

**Bad:**
```zig
fn openUrl(allocator: std.mem.Allocator, url: []const u8) !void {
    const owned_url = try allocator.dupe(u8, url);
    const child = std.process.Child.init(&.{ "open", owned_url }, allocator);
    const thread = try std.Thread.spawn(.{}, openUrlThread, .{ child });
    thread.detach(); // child carries stack-backed argv
}
```

**Good:**
```zig
fn openUrl(allocator: std.mem.Allocator, url: []const u8) !void {
    const owned_url = try allocator.dupe(u8, url);
    var argv = try allocator.alloc([]const u8, 2);
    argv[0] = "open";
    argv[1] = owned_url;
    const child = std.process.Child.init(argv, allocator);
    const thread = try std.Thread.spawn(.{}, openUrlThread, .{ child });
    thread.join(); // join guarantees thread completion before return
}
```

Built-in escape models:
- `std.process.Child.init` captures `argv` into the returned `Child`
- `std.Thread.spawn` captures its argument tuple into the spawned thread

Config:
- `escape_models`: custom escape/capture rules
- `escape_max_depth`: helper call depth for origin tracking (default: 3)
- `resource_models` of kind `alloc` are used to treat allocator-backed values as heap

Custom escape models use the same shared call resolution as resource models, including identifier calls, receiver method calls, receiver types, and FQNs.

Notes:
- `try std.Thread.spawn(...)` ignores the `try_error` edge when checking join guarantees (no thread is created on the error path).
- Joining must be guaranteed on all paths; a join in only some branches still reports an escape.
- Capturing allocator-backed or static data does not trigger this rule.

### slice-bounds-engine

Detects array and slice out-of-bounds access using path-sensitive analysis with abstract values.

The checker tracks index values and array/slice lengths through the dataflow engine. It reports:

- **Definite OOB**: index is provably outside the valid range on all reaching paths
- **Possible OOB**: index may be outside the valid range on some paths

Supported sources of length information:
- Array literals (e.g., `[_]u8{ 1, 2, 3 }` — length 3)
- String literals (e.g., `"hello"` — length 5)

Index values are tracked as concrete integers or ranges via the `AbstractValue` system.

**Bad:**
```zig
fn definiteOob() void {
    const arr = [_]u8{ 1, 2, 3 };
    _ = arr[5]; // index 5 >= length 3
}

fn possibleOob(flag: bool) void {
    const arr = [_]u8{ 1, 2, 3 };
    var idx: i32 = 1;
    if (flag) {
        idx = 5;
    }
    _ = arr[@intCast(idx)]; // idx may be 1 or 5
}
```

**Good:**
```zig
fn safeAccess() void {
    const arr = [_]u8{ 1, 2, 3 };
    _ = arr[2]; // index 2 < length 3
    _ = arr[1];
}
```

Limitations:
- Does not track dynamic `slice.len` from runtime operations
- No interprocedural bounds tracking
- Handles basic `+`/`-` arithmetic on indices only
- Loop-derived index ranges may be too imprecise to report in all cases
