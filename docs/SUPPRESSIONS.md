# Inline suppressions

Suppress diagnostics directly in your code using special comments.

## Suppress all rules on the next line

```zig
// zwanzig-disable-next-line
const x = problematic_code();  // No diagnostics reported for this line
```

## Suppress specific rules on the next line

```zig
// zwanzig-disable-next-line: empty-catch, todo
try foo() catch {};  // Only empty-catch and todo suppressed
```

## Suppress rules for a region of the file

```zig
// zwanzig-disable: unused-decl
const unused1 = 1;  // Suppressed
const unused2 = 2;  // Suppressed
// zwanzig-enable: unused-decl
const unused3 = 3;  // Reported again
```

## Suppress all rules for a region

```zig
// zwanzig-disable
// Everything here is suppressed
// zwanzig-enable
```

## Suppression comment format

| Comment | Effect |
|---------|--------|
| `// zwanzig-disable-next-line` | Suppress all rules on the next line |
| `// zwanzig-disable-next-line: rule1, rule2` | Suppress specific rules on the next line |
| `// zwanzig-disable` | Suppress all rules until end of file or `enable` |
| `// zwanzig-disable: rule1, rule2` | Suppress specific rules until end of file or `enable` |
| `// zwanzig-enable` | Re-enable all rules |
| `// zwanzig-enable: rule1, rule2` | Re-enable specific rules |

## Infrastructure diagnostics

`analysis-limit-exceeded` is an ordinary diagnostic and follows the same
suppression rules as any other. Suppressing it hides the fact that the
function's dataflow analysis was truncated, so raise the corresponding
`max_worklist_steps` or `max_states_per_point` limit instead.

Syntax errors are reported from a separate pass and are not suppressible.
