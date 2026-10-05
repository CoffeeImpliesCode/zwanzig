//! Relational facts for `optional-unwrap`.
//!
//! Two unwraps are non-null because of a relation between two sites rather
//! than because the value was checked where it is used:
//!
//!   * `retained_row_lookup` (#73) - a filter appends a row to a
//!     function-local buffer only after the *same* lookup call on the *same*
//!     query succeeded for those bytes, and a later loop replays that call
//!     over the retained prefix.
//!   * `error_partition_payload` (#74) - a producer fills a nullable field
//!     from an exhaustive `switch` over an error-set parameter, and a separate
//!     predicate over the *same* error value is known true at the unwrap.
//!
//! Both proofs are closed on purpose and never consult what an unmodelled
//! caller might do. The lookup must be a local function whose every statement
//! is a `return` of an expression built only from its parameters, so the same
//! arguments always give the same answer. The producer and the predicate must
//! both be local functions over the same declared error set, and the guard
//! must carry the same error value the producer partitioned.
//!
//! #73 additionally depends on the *bytes* the replay reads being the bytes a
//! guard inspected, and a `[]const T` element type does not establish that: it
//! says this function will not write them through the buffer, not that no
//! other name can. So the retained buffer, its counter, and the read must all
//! be function-local, the buffer must hold rows whose bytes the buffer itself
//! cannot write, the prefix must stay bounded, every store must write the
//! counter's own slot and be paired with a `+ 1` move of it, and between the
//! guard lookup and the replay no tracked binding may be written, every other
//! write must land in storage this function owns, and no call may run unless it
//! is itself proved pure on its arguments. Anything else keeps the warning.
//!
//! `isProvenNonNull` is the whole interface: a caller learns that the unwrap is
//! proved, or nothing. There is no separate "this site takes part in a
//! relation" query to word a diagnostic from, because every site this module
//! cannot prove is genuinely unproved.
const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
const lexical_index = @import("../../analysis/lexical_index.zig");
const TypeContext = @import("../../type_context.zig").TypeContext;
const QueryContext = @import("bindings.zig").QueryContext;
const guards = @import("guards.zig");

/// How many distinct bindings one proof tracks at once.
const name_capacity = 8;
/// How many arguments one lookup call may take.
const arg_capacity = 8;
/// How many tags one error-set partition may carry.
const tag_capacity = 16;
/// How many blocks one store may be wrapped in before the shape is dropped.
const nesting_capacity = 4;
/// How far a purity query may recurse through local callees.
const purity_depth = 8;

/// Which relation, if any, an unwrap site takes part in. `classifyRelation`
/// recognizes the shape; `isProvenNonNull` decides the proof. Nothing outside
/// this module reads the shape, so it stays private: an exported shape query
/// invites a caller to word a diagnostic "unsupported relational proof" for a
/// relation it never checked.
const Relation = enum {
    /// No modelled relation reaches this unwrap.
    none,
    /// A filter kept this row only after the same lookup succeeded on it.
    retained_row_lookup,
    /// A producer's error partition decides whether this payload is filled.
    error_partition_payload,
};

/// The relation an unwrap site takes part in, ignoring whether the relation
/// holds here.
fn classifyRelation(query: *const QueryContext, target: u32) Relation {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (target == 0 or target >= tags.len) return .none;
    switch (tags[target]) {
        .call, .call_comma, .call_one, .call_one_comma => {
            if (readPrefix(query, target) == null) return .none;
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, @enumFromInt(target)) orelse
                return .none;
            if (resolveLocalFunction(query, @intFromEnum(call.ast.fn_expr)) == null)
                return .none;
            return .retained_row_lookup;
        },
        .field_access => {
            const produced = producedBinding(query, target) orelse
                return .none;
            if (!returnsStructLiteral(query, produced.producer))
                return .none;
            return .error_partition_payload;
        },
        else => return .none,
    }
}

/// Shared contract for both relations: does the relation between the two sites
/// prove the unwrapped value non-null at `unwrap_node`?
pub fn isProvenNonNull(
    query: *const QueryContext,
    unwrap_node: u32,
    target: u32,
    type_context: ?*TypeContext,
) bool {
    const relation = classifyRelation(query, target);
    return switch (relation) {
        .none => false,
        .retained_row_lookup => provesRetainedRow(query, unwrap_node, target),
        .error_partition_payload => provesErrorPartition(query, unwrap_node, target, type_context),
    };
}

// ---------------------------------------------------------------------------
// Issue #73: a row kept only after the same deterministic lookup succeeded
// ---------------------------------------------------------------------------

/// `for (buffer[0..count]) |row|` read back over a function-local buffer.
const ReadPrefix = struct {
    function: u32,
    /// The loop payload's own name token, which is also its binding.
    payload: u32,
    container: u32,
    container_node: u32,
    counter: u32,
};

/// One validated store: the row was kept, and the counter moved, only on a
/// path where the matching lookup on the same query had already succeeded.
const Store = struct {
    /// The store statement itself. Together with `increment` it is the only
    /// write inside the closed window that provably lands in this function's
    /// own buffer.
    statement: u32,
    /// First token of the statement that ran the matching lookup. The window
    /// that has to stay closed starts here, not at the store.
    guard_token: u32,
    increment: u32,
    end_token: u32,
};

fn provesRetainedRow(query: *const QueryContext, unwrap_node: u32, target: u32) bool {
    const read = readPrefix(query, target) orelse {
        return false;
    };

    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = query.tree.fullCall(&buffer, @enumFromInt(target)) orelse {
        return false;
    };
    if (call.ast.params.len == 0 or call.ast.params.len > arg_capacity) {
        return false;
    }
    const callee = resolveLocalFunction(query, @intFromEnum(call.ast.fn_expr)) orelse {
        return false;
    };
    if (!isDeterministicBody(query, callee, 0)) {
        return false;
    }

    // A `[]const T` element only says this function cannot write a row through
    // the buffer; it says nothing about a second alias of the same backing.
    // `regionIsClosed` is what rules that half out.
    if (!isBoundedRowBuffer(query, read.container_node, read.function)) {
        return false;
    }

    var name_storage: [arg_capacity]u32 = undefined;
    var row_index: ?usize = null;
    for (call.ast.params, 0..) |param, index| {
        const name = bindingNameToken(query, @intFromEnum(param)) orelse {
            return false;
        };
        name_storage[index] = name;
        if (name != read.payload) continue;
        // Exactly one argument is the retained row: two arguments sharing the
        // loop payload would leave the replay ambiguous.
        if (row_index != null) {
            return false;
        }
        row_index = index;
    }
    const index = row_index orelse {
        return false;
    };
    // Only the arguments the call actually passed are named from here on, so
    // no uninitialized slot of the storage can be read or tracked.
    const names = name_storage[0..call.ast.params.len];

    var tracked: NameSet = .{};
    tracked.add(read.container);
    tracked.add(read.counter);
    tracked.add(read.payload);
    for (names, 0..) |name, i| {
        if (i == index) continue;
        tracked.add(name);
    }
    if (tracked.isFull()) {
        return false;
    }

    const store = validatedStore(query, read, callee, index, names, tracked) orelse {
        return false;
    };
    // The invariant has to have been established before the replay reads it.
    if (store.end_token >= query.firstToken(unwrap_node)) {
        return false;
    }
    if (!regionIsClosed(query, store, tracked, unwrap_node, read.function)) {
        return false;
    }
    return true;
}

/// Does the unwrap read a bounded prefix of a function-local buffer?
fn readPrefix(query: *const QueryContext, target: u32) ?ReadPrefix {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    var node = target;
    while (node != 0 and node < tags.len) {
        const parent = query.lexical.parent(node) orelse {
            return null;
        };
        if (parent == 0 or parent >= tags.len) {
            return null;
        }
        if (tags[parent] == .fn_decl or tags[parent] == .test_decl) {
            return null;
        }
        if (tags[parent] == .@"for" or tags[parent] == .for_simple) {
            const full = tree.fullFor(@enumFromInt(parent)) orelse {
                return null;
            };
            if (!containsNode(tree, @intFromEnum(full.ast.then_expr), target)) {
                node = parent;
                continue;
            }
            return describeReadPrefix(query, parent, full);
        }
        node = parent;
    }
    return null;
}

fn describeReadPrefix(query: *const QueryContext, loop: u32, full: std.zig.Ast.full.For) ?ReadPrefix {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    // `for (a, b) |row, index|` and pointer captures are not this shape.
    if (full.ast.inputs.len != 1) {
        return null;
    }
    const input = @intFromEnum(full.ast.inputs[0]);
    if (input >= tags.len) {
        return null;
    }
    if (tags[input] != .slice) {
        return null;
    }
    const sliced = tree.fullSlice(@enumFromInt(input)) orelse return null;

    // Only the whole retained prefix is covered: `buffer[0..count]`.
    const start = @intFromEnum(sliced.ast.start);
    if (!isIntLiteral(tree, start, 0)) {
        return null;
    }
    const end = @intFromEnum(sliced.ast.end);
    const container_node = bindingIdentifier(query, @intFromEnum(sliced.ast.sliced)) orelse {
        return null;
    };
    const counter_node = bindingIdentifier(query, end) orelse {
        return null;
    };

    return .{
        .function = enclosingFunction(query, loop) orelse {
            return null;
        },
        // The payload is read off the whole loop input: its last token is the
        // `)` that closes `for (buffer[0..count])`, which is what the scan
        // continues from. The prefix end is only the upper-bound expression.
        .payload = forPayloadToken(tree, input) orelse {
            return null;
        },
        .container = bindingNameToken(query, container_node) orelse {
            return null;
        },
        .container_node = container_node,
        .counter = bindingNameToken(query, counter_node) orelse {
            return null;
        },
    };
}

/// The function's validated store of the buffer, and only when every write to
/// the buffer *and* to the counter is part of a validated pair.
fn validatedStore(
    query: *const QueryContext,
    read: ReadPrefix,
    callee: u32,
    row_index: usize,
    names: []const u32,
    tracked: NameSet,
) ?Store {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    var first: ?Store = null;
    var pairs: [arg_capacity][2]u32 = undefined;
    var pair_count: usize = 0;

    var node: u32 = 1;
    while (node < tags.len) : (node += 1) {
        if (!insideFunction(query, node, read.function)) continue;
        if (tags[node] != .assign) continue;
        const lhs = @intFromEnum(datas[node].node_and_node[0]);
        if (!namesBinding(query, lhs, read.container)) continue;
        // A write to the buffer that is not a validated store drops the whole
        // invariant, so it can never be skipped past.
        const store = validateStore(query, read, callee, row_index, names, tracked, node) orelse {
            return null;
        };
        if (first == null) first = store;
        if (pair_count < arg_capacity) {
            pairs[pair_count] = .{ store.statement, store.increment };
            pair_count += 1;
        }
    }
    const store = first orelse {
        return null;
    };

    // The counter defines the prefix, so no write to it may escape a pair. A
    // validated store names the counter only to name the slot it writes, which
    // `validateStore` reads straight off that store; every other assignment
    // that mentions the counter could move it.
    node = 1;
    while (node < tags.len) : (node += 1) {
        if (!insideFunction(query, node, read.function)) continue;
        if (!isAssignmentTag(tags[node])) continue;
        var paired = false;
        for (pairs[0..pair_count]) |pair| {
            if (pair[0] == node or pair[1] == node) paired = true;
        }
        if (paired) continue;
        const lhs = @intFromEnum(datas[node].node_and_node[0]);
        if (namesBinding(query, lhs, read.counter)) {
            return null;
        }
    }
    return store;
}

/// `buffer[counter] = row`: the slot a store writes has to be the very counter
/// the replay cuts the prefix at, or the store and the replay name different
/// rows. Any other index leaves a slot the replay never wrote.
fn storeSlot(query: *const QueryContext, statement: u32, read: ReadPrefix) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (statement >= tags.len or tags[statement] != .assign) return null;
    const lhs = @intFromEnum(tree.nodes.items(.data)[statement].node_and_node[0]);
    if (lhs >= tags.len or tags[lhs] != .array_access) return null;
    const access = tree.nodes.items(.data)[lhs].node_and_node;
    if (bindingNameToken(query, @intFromEnum(access[0])) != read.container) return null;
    return bindingNameToken(query, @intFromEnum(access[1]));
}

/// Is `node` a store into the counter's own slot whose only path runs the
/// matching lookup successfully, and whose counter moves by one immediately
/// afterwards?
fn validateStore(
    query: *const QueryContext,
    read: ReadPrefix,
    callee: u32,
    row_index: usize,
    names: []const u32,
    tracked: NameSet,
    node: u32,
) ?Store {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    // The kept value must be the identifier the lookup inspected, not an
    // expression derived from the lookup's own answer.
    const row = bindingNameToken(query, @intFromEnum(datas[node].node_and_node[1])) orelse {
        return null;
    };

    // The row has to land in the slot the replay reads back, so the store
    // indexes the buffer with the counter itself.
    if (storeSlot(query, node, read) != read.counter) {
        return null;
    }

    const increment = followingStatement(query, node) orelse {
        return null;
    };
    if (increment >= tags.len or tags[increment] != .assign_add) {
        return null;
    }
    const pair = datas[increment].node_and_node;
    if (bindingNameToken(query, @intFromEnum(pair[0])) != read.counter) {
        return null;
    }
    if (!isIntLiteral(tree, @intFromEnum(pair[1]), 1)) {
        return null;
    }

    var guarded = tracked;
    guarded.add(row);

    // Walk outwards from the store: every statement between the lookup guard
    // and the store must leave the row, the query, the buffer, and the counter
    // alone, and a capacity guard must have run first.
    var current = node;
    var bounded = false;
    var guard_statement: u32 = 0;
    var found = false;
    var steps: u8 = 0;
    while (steps < nesting_capacity) : (steps += 1) {
        const block = query.lexical.parent(current) orelse {
            return null;
        };
        if (block >= tags.len or !isBlockTag(tags[block])) {
            return null;
        }
        var block_buffer: [2]u32 = undefined;
        const statements = ast_walk.getBlockStatements(tree, block, &block_buffer) orelse {
            return null;
        };
        var index = statementIndex(statements, current) orelse {
            return null;
        };
        // The statement the walk landed on, the store itself or an enclosing
        // capacity guard, is not one of the statements between the lookup
        // guard and the store, so the walk starts at the statement above it.
        // Starting two above would leave a gap a tracked write could hide in,
        // and would skip the capacity guard that has to have run first.
        if (index == 0) {
            return null;
        }
        index -= 1;
        while (true) {
            const statement = statements[index];
            if (isCapacityGuard(query, statement, read)) {
                bounded = true;
            } else if (guardRunsLookup(query, statement, callee, row_index, names, row, guarded)) {
                // Without the capacity guard the prefix could run past the
                // buffer, which is not the invariant being claimed.
                if (!bounded) {
                    return null;
                }
                found = true;
                guard_statement = statement;
                break;
            } else if (namesAnyOf(query, statement, guarded)) {
                return null;
            }
            if (index == 0) break;
            index -= 1;
        }
        if (found) break;

        const parent = query.lexical.parent(block) orelse {
            return null;
        };
        if (parent >= tags.len) {
            return null;
        }
        switch (tags[parent]) {
            .@"if", .if_simple => {
                const full_if = tree.fullIf(@enumFromInt(parent)) orelse {
                    return null;
                };
                if (@intFromEnum(full_if.ast.then_expr) != block) {
                    return null;
                }
                if (full_if.ast.else_expr.unwrap() != null) {
                    return null;
                }
                if (!provesBelowCapacity(query, @intFromEnum(full_if.ast.cond_expr), read)) {
                    return null;
                }
                bounded = true;
                current = parent;
            },
            else => {
                return null;
            },
        }
    }
    if (!found) {
        return null;
    }
    return .{
        .statement = node,
        .guard_token = query.firstToken(guard_statement),
        .increment = increment,
        .end_token = query.lastToken(increment),
    };
}

/// `_ = lookup(row, query) orelse continue;` on the path to the store.
fn guardRunsLookup(
    query: *const QueryContext,
    statement: u32,
    callee: u32,
    row_index: usize,
    names: []const u32,
    row: u32,
    guarded: NameSet,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (statement >= tags.len or tags[statement] != .assign) return false;
    // The guard's own left side may only hold the lookup's answer: a stored
    // row or query could be read back and rewritten around the guard.
    if (namesAnyOf(query, @intFromEnum(datas[statement].node_and_node[0]), guarded)) {
        return false;
    }
    const expr = @intFromEnum(datas[statement].node_and_node[1]);
    if (expr >= tags.len or tags[expr] != .@"orelse") return false;
    const orelse_pair = datas[expr].node_and_node;
    if (!leavesTheLoop(tree, @intFromEnum(orelse_pair[1]))) {
        return false;
    }

    const call_node = @intFromEnum(orelse_pair[0]);
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse {
        return false;
    };
    // The guard has to run the same call the replay does, over as many
    // arguments as the replay passes; `names` is the replay's own argument
    // list, so this compares two real counts and never a capacity.
    if (call.ast.params.len != names.len) {
        return false;
    }
    if (resolveLocalFunction(query, @intFromEnum(call.ast.fn_expr)) != callee) {
        return false;
    }
    for (call.ast.params, 0..) |param, index| {
        // The row is the loop payload that got stored; every other argument
        // must be the same binding the replay passes.
        const want = if (index == row_index) row else names[index];
        if (bindingNameToken(query, @intFromEnum(param)) != want) {
            return false;
        }
    }
    return true;
}

/// `if (count == buffer.len) break;` before the store.
fn isCapacityGuard(query: *const QueryContext, statement: u32, read: ReadPrefix) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (statement >= tags.len) return false;
    if (tags[statement] != .@"if" and tags[statement] != .if_simple) return false;
    const full = tree.fullIf(@enumFromInt(statement)) orelse return false;
    if (full.ast.else_expr.unwrap() != null) return false;
    const then_expr = @intFromEnum(full.ast.then_expr);
    if (then_expr >= tags.len or tags[then_expr] != .@"break") return false;
    if (isLabeledExit(tree, then_expr)) return false;
    return isAtCapacity(query, @intFromEnum(full.ast.cond_expr), read);
}

fn isAtCapacity(query: *const QueryContext, condition: u32, read: ReadPrefix) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (condition >= tags.len) return false;
    switch (tags[condition]) {
        .equal_equal, .greater_or_equal => {},
        else => return false,
    }
    const pair = tree.nodes.items(.data)[condition].node_and_node;
    if (bindingNameToken(query, @intFromEnum(pair[0])) != read.counter) return false;
    return isContainerLength(query, @intFromEnum(pair[1]), read.container);
}

/// `if (count < buffer.len) { ... }` around the store.
fn provesBelowCapacity(query: *const QueryContext, condition: u32, read: ReadPrefix) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (condition >= tags.len or tags[condition] != .less_than) return false;
    const pair = tree.nodes.items(.data)[condition].node_and_node;
    if (bindingNameToken(query, @intFromEnum(pair[0])) != read.counter) return false;
    return isContainerLength(query, @intFromEnum(pair[1]), read.container);
}

fn isContainerLength(query: *const QueryContext, node: u32, container: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .field_access) return false;
    const access = tree.nodes.items(.data)[node].node_and_token;
    if (!std.mem.eql(u8, tree.tokenSlice(access[1]), "len")) return false;
    return bindingNameToken(query, @intFromEnum(access[0])) == container;
}

/// `[8][]const u8` held by a function-local `var`: the buffer cannot be used to
/// write a row's bytes, and a comptime-known non-zero length is what makes the
/// prefix bounded. This is a statement about the buffer alone. It is not a
/// claim about the memory a row points at, which a second mutable alias can
/// still rewrite; `regionIsClosed` is what rules that half out.
fn isBoundedRowBuffer(query: *const QueryContext, ident_node: u32, function: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const decl = localVarDecl(query, ident_node, function) orelse {
        return false;
    };
    const full = tree.fullVarDecl(@enumFromInt(decl)) orelse return false;
    const type_node = full.ast.type_node.unwrap() orelse {
        return false;
    };
    const type_id = @intFromEnum(type_node);
    if (type_id >= tags.len or tags[type_id] != .array_type) {
        return false;
    }
    const array = tree.fullArrayType(@enumFromInt(type_id)) orelse return false;
    // A comptime-known, non-zero length is what makes the prefix bounded.
    if (!isPositiveIntLiteral(tree, @intFromEnum(array.ast.elem_count))) {
        return false;
    }
    const element = @intFromEnum(array.ast.elem_type);
    if (element >= tags.len) return false;
    const pointer = tree.fullPtrType(@enumFromInt(element)) orelse {
        return false;
    };
    if (pointer.size != .slice) {
        return false;
    }
    if (pointer.const_token == null) {
        return false;
    }
    return true;
}

/// Nothing between the guard lookup and the replay may reach the row's bytes,
/// the query's bytes, or the binding the replay names. A `[]const` element
/// stops *this* function from writing a row through the buffer and nothing
/// else, so the window is closed on its own terms: a tracked binding may not
/// be written at all, any other write has to land in storage this function
/// owns, and a call may run only when it is itself proved to answer from its
/// arguments. A nullary `purge()` writes whatever its body writes, and an
/// argument the proof never tracked can still be a mutable view of the very
/// bytes the guard inspected.
fn regionIsClosed(
    query: *const QueryContext,
    store: Store,
    tracked: NameSet,
    unwrap_node: u32,
    function: u32,
) bool {
    // Without a guard statement there is no window to close.
    if (store.guard_token == 0) {
        return false;
    }
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const high = query.firstToken(unwrap_node);
    var node: u32 = 1;
    while (node < tags.len) : (node += 1) {
        // The store and the counter move are the validated pair itself:
        // `validateStore` already read off the value it keeps and that the
        // move is a literal `+ 1` on the path the guard opened.
        if (node == store.statement or node == store.increment) continue;
        const token = query.firstToken(node);
        if (token <= store.guard_token or token >= high) continue;
        // The unwrap's own statement and its lookup are the relation being
        // proven, not a violation of it.
        if (containsNode(tree, node, unwrap_node) or containsNode(tree, unwrap_node, node)) continue;
        switch (tags[node]) {
            .address_of, .@"asm", .asm_simple, .assign_destructure => {
                return false;
            },
            .call,
            .call_comma,
            .call_one,
            .call_one_comma,
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => {
                if (!isPureCall(query, node)) {
                    return false;
                }
            },
            else => {
                if (!isAssignmentTag(tags[node])) continue;
                // Writing a tracked binding changes what the replay names,
                // even when the new value only overwrites a local header.
                const lhs = @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]);
                if (namesAnyOf(query, lhs, tracked)) {
                    return false;
                }
                if (!writesOwnedStorage(query, node, function)) {
                    return false;
                }
            },
        }
    }
    return true;
}

/// Does this assignment land only in storage this function owns? A plain
/// binding to a parameter or to a local `var` cannot be written through an
/// alias held by the caller or by another function, and a discard writes
/// nothing at all. Every other target - a field, an index, a dereference, a
/// global - could land in the backing of a retained row.
fn writesOwnedStorage(query: *const QueryContext, statement: u32, function: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const lhs = @intFromEnum(tree.nodes.items(.data)[statement].node_and_node[0]);
    if (lhs >= tags.len or tags[lhs] != .identifier) return false;
    if (isDiscardBinding(tree, lhs)) return true;
    if (isParameterOf(query, lhs, function)) return true;
    const name = bindingNameToken(query, lhs) orelse return false;
    const decl = varDeclAtName(query, name) orelse return false;
    return enclosingFunction(query, decl) == function;
}

/// `_ = ...;` keeps no value and cannot have written one.
fn isDiscardBinding(tree: *const std.zig.Ast, ident_node: u32) bool {
    const token = tree.nodes.items(.main_token)[ident_node];
    if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return false;
    return std.mem.eql(u8, tree.tokenSlice(token), "_");
}

/// A call may run inside the closed window only when its whole answer is
/// decided by its arguments. A local helper is held to the same purity walk
/// the lookup itself is held to; anything else has to be on the verified `std`
/// list, so an unmodelled callee closes the window instead of quietly
/// proving nothing about the bytes.
fn isPureCall(query: *const QueryContext, node: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (node == 0 or node >= tags.len) return false;
    switch (tags[node]) {
        .call, .call_comma, .call_one, .call_one_comma => {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return false;
            const callee = @intFromEnum(call.ast.fn_expr);
            if (tags[callee] == .identifier) {
                const local = resolveLocalFunction(query, callee) orelse return false;
                return isDeterministicBody(query, local, 0);
            }
            return isVerifiedPureStdCall(query, callee);
        },
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            return isPureBuiltinCall(tree, node);
        },
        else => return false,
    }
}

/// The builtins that answer from their arguments and write nothing. Everything
/// else - each `@memcpy`, `@memset`, `@atomic*`, and each cast that could hand
/// back a mutable view - closes the window.
fn isPureBuiltinCall(tree: *const std.zig.Ast, node: u32) bool {
    const token = tree.nodes.items(.main_token)[node];
    if (token >= tree.tokens.len) return false;
    const name = tree.tokenSlice(token);
    inline for (pure_builtin_calls) |pure| {
        if (std.mem.eql(u8, name, pure)) return true;
    }
    return false;
}

// ---------------------------------------------------------------------------
// Issue #74: a producer's error partition decides its nullable payload
// ---------------------------------------------------------------------------

/// `const info = diagnostic(err);` where `diagnostic` is a local function.
const ProducedBinding = struct {
    producer: u32,
    argument: u32,
    name: u32,
    function: u32,
};

/// Which error tags leave the producer's payload null, and which fill it.
const NullablePartition = struct {
    error_set: ErrorSet,
    null_tags: TagSet = .{},
    solid_tags: TagSet = .{},
};

/// Which error tags a predicate reports true for, and which for false.
const BoolPartition = struct {
    error_set: ErrorSet,
    true_tags: TagSet = .{},
    false_tags: TagSet = .{},
};

/// A declared error set, named by its own declaration so two spellings of one
/// type are told apart from two look-alike sets.
const ErrorSet = struct {
    declaration: u32,
    members: [tag_capacity]u32 = undefined,
    len: usize = 0,

    fn declares(self: ErrorSet, tree: *const std.zig.Ast, token: u32) bool {
        if (self.len == 0) return false;
        for (self.members[0..self.len]) |member| {
            if (std.mem.eql(u8, tree.tokenSlice(member), tree.tokenSlice(token))) return true;
        }
        return false;
    }
};

const TagSet = struct {
    tokens: [tag_capacity]u32 = undefined,
    len: usize = 0,

    fn add(self: *TagSet, tree: *const std.zig.Ast, token: u32) void {
        if (self.len == tag_capacity) return;
        if (self.contains(tree, token)) return;
        self.tokens[self.len] = token;
        self.len += 1;
    }

    fn contains(self: TagSet, tree: *const std.zig.Ast, token: u32) bool {
        for (self.tokens[0..self.len]) |existing| {
            if (std.mem.eql(u8, tree.tokenSlice(existing), tree.tokenSlice(token))) return true;
        }
        return false;
    }

    fn isEmpty(self: TagSet) bool {
        return self.len == 0;
    }
};

fn provesErrorPartition(
    query: *const QueryContext,
    unwrap_node: u32,
    target: u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const produced = producedBinding(query, target) orelse return false;
    if (enclosingFunction(query, unwrap_node) != produced.function) return false;
    const field_token = tree.nodes.items(.data)[target].node_and_token[1];

    const nullable = nullablePartition(query, produced.producer, field_token, type_context) orelse return false;
    if (nullable.null_tags.isEmpty() or nullable.solid_tags.isEmpty()) return false;
    const predicate = guardPredicate(query, unwrap_node, produced) orelse return false;
    const flags = boolPartition(query, predicate) orelse return false;
    // A whitelist over a different set of tags says nothing about this payload.
    if (!sameErrorSet(nullable.error_set, flags.error_set, tree)) return false;
    if (flags.true_tags.isEmpty()) return false;
    for (flags.true_tags.tokens[0..flags.true_tags.len]) |token| {
        if (!nullable.solid_tags.contains(tree, token)) return false;
    }
    return isPartitionArgument(query, produced, nullable.error_set);
}

fn producedBinding(query: *const QueryContext, access: u32) ?ProducedBinding {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const receiver = @intFromEnum(tree.nodes.items(.data)[access].node_and_token[0]);
    if (tags[receiver] != .identifier) return null;
    const name = query.resolveIdentifierBinding(receiver) orelse return null;
    const decl = varDeclAtName(query, name) orelse return null;
    const full = tree.fullVarDecl(@enumFromInt(decl)) orelse return null;
    if (tree.tokenTag(full.ast.mut_token) != .keyword_const) return null;
    if (full.comptime_token != null or full.ast.align_node != .none or
        full.ast.addrspace_node != .none or full.ast.section_node != .none) return null;
    const init = full.ast.init_node.unwrap() orelse return null;

    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, init) orelse return null;
    if (call.ast.params.len != 1) return null;
    const producer = resolveLocalFunction(query, @intFromEnum(call.ast.fn_expr)) orelse return null;
    return .{
        .producer = producer,
        .argument = @intFromEnum(call.ast.params[0]),
        .name = name,
        .function = enclosingFunction(query, decl) orelse return null,
    };
}

/// The predicate the guard established as true at the unwrap, together with
/// proof that its argument is the same error value the producer partitioned.
fn guardPredicate(query: *const QueryContext, unwrap_node: u32, produced: ProducedBinding) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    // A payload handed to a call or taken by address is no longer this
    // producer's own partition.
    if (payloadEscapes(query, produced.function, produced.name)) return null;

    const block = containingBlock(query, unwrap_node) orelse return null;
    var block_buffer: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &block_buffer) orelse return null;
    const position = containingStatement(tree, statements, unwrap_node) orelse return null;

    // `if (!isPositioned(err)) return null;` somewhere before the unwrap.
    var index = position;
    while (index > 0) {
        index -= 1;
        const statement = statements[index];
        if (statement >= tags.len) continue;
        if (tags[statement] != .@"if" and tags[statement] != .if_simple) continue;
        const full = tree.fullIf(@enumFromInt(statement)) orelse continue;
        if (full.ast.else_expr.unwrap() != null) continue;
        if (!leavesTheFunction(tree, @intFromEnum(full.ast.then_expr))) continue;
        const condition = @intFromEnum(full.ast.cond_expr);
        if (condition >= tags.len or tags[condition] != .bool_not) continue;
        const call_node = @intFromEnum(tree.nodes.items(.data)[condition].node);
        if (correlationHolds(query, call_node, produced)) |predicate| return predicate;
    }

    // `if (isPositioned(err)) { ... info.position.? ... }` around the unwrap.
    var node = unwrap_node;
    while (node != 0 and node < tags.len) {
        const parent = query.lexical.parent(node) orelse return null;
        if (parent == 0 or parent >= tags.len) return null;
        if (tags[parent] == .@"if" or tags[parent] == .if_simple) {
            const full = tree.fullIf(@enumFromInt(parent)) orelse return null;
            if (!containsNode(tree, @intFromEnum(full.ast.then_expr), unwrap_node)) {
                node = parent;
                continue;
            }
            if (full.ast.else_expr.unwrap() != null) return null;
            if (correlationHolds(query, @intFromEnum(full.ast.cond_expr), produced)) |predicate| return predicate;
        }
        node = parent;
    }
    return null;
}

/// Does `call_node` ask the predicate about the same error value the producer
/// partitioned?
fn correlationHolds(query: *const QueryContext, call_node: u32, produced: ProducedBinding) ?u32 {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = query.tree.fullCall(&buffer, @enumFromInt(call_node)) orelse return null;
    if (call.ast.params.len != 1) return null;
    const predicate = resolveLocalFunction(query, @intFromEnum(call.ast.fn_expr)) orelse return null;
    const same = sameErrorValue(query, @intFromEnum(call.ast.params[0]), produced.argument) orelse return null;
    if (!same) return null;
    return predicate;
}

fn sameErrorValue(query: *const QueryContext, left: u32, right: u32) ?bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (left >= tags.len or right >= tags.len) return null;
    if (tags[left] == .error_value and tags[right] == .error_value) {
        const left_tag = errorTagToken(tree, left) orelse return null;
        const right_tag = errorTagToken(tree, right) orelse return null;
        return std.mem.eql(u8, tree.tokenSlice(left_tag), tree.tokenSlice(right_tag));
    }
    if (tags[left] != .identifier or tags[right] != .identifier) return null;
    const left_binding = query.resolveIdentifierBinding(left) orelse return null;
    if (query.resolveIdentifierBinding(right) != left_binding) return false;
    return true;
}

/// The partition argument has to be an error value the producer's own set
/// declares: an immutable parameter of the same error set, or one of its tags.
fn isPartitionArgument(query: *const QueryContext, produced: ProducedBinding, error_set: ErrorSet) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const argument = produced.argument;
    if (argument >= tags.len) return false;
    if (tags[argument] == .error_value) {
        const token = errorTagToken(tree, argument) orelse return false;
        return error_set.declares(tree, token);
    }
    if (tags[argument] != .identifier) return false;

    // A parameter cannot be rewritten between the producer call and the guard.
    const candidate = parameterOf(query, argument) orelse return false;
    if (query.lexical.enclosingFunction(candidate.scope.first_token) != produced.function) return false;
    const declared = parameterTypeNode(tree, candidate.node) orelse return false;
    const set = errorSetOfTypeNode(query, declared) orelse return false;
    return sameErrorSet(set, error_set, tree);
}

/// The producer's error partition: every return stores the field from a
/// `switch` over the same error-set parameter, with no `else` prong and no tag
/// left undecided.
fn nullablePartition(
    query: *const QueryContext,
    producer: u32,
    field_token: u32,
    type_context: ?*TypeContext,
) ?NullablePartition {
    const tree = query.tree;
    var partition: NullablePartition = .{ .error_set = undefined };
    var block_buffer: [2]u32 = undefined;
    const statements = returnOnlyBody(query, producer, &block_buffer) orelse return null;
    var returns: usize = 0;
    for (statements) |statement| {
        const operand = tree.nodes.items(.data)[statement].opt_node.unwrap() orelse return null;
        const switch_node = storedSwitchOver(query, @intFromEnum(operand), field_token, producer) orelse return null;
        const subject = switchSubject(query, switch_node) orelse return null;
        const declared = parameterTypeNode(tree, parameterNodeOf(query, subject, producer) orelse return null) orelse return null;
        const set = errorSetOfTypeNode(query, declared) orelse return null;
        if (returns == 0) {
            partition.error_set = set;
        } else if (!sameErrorSet(set, partition.error_set, tree)) {
            return null;
        }
        if (!collectNullableArms(
            tree,
            switch_node,
            partition.error_set,
            &partition.null_tags,
            &partition.solid_tags,
            type_context,
        )) return null;
        returns += 1;
    }
    // A tag that one return fills and another leaves null decides nothing.
    for (partition.null_tags.tokens[0..partition.null_tags.len]) |token| {
        if (partition.solid_tags.contains(tree, token)) return null;
    }
    for (partition.solid_tags.tokens[0..partition.solid_tags.len]) |token| {
        if (!partition.error_set.declares(tree, token)) return null;
    }
    for (partition.error_set.members[0..partition.error_set.len]) |member| {
        if (!partition.null_tags.contains(tree, member) and !partition.solid_tags.contains(tree, member)) return null;
    }
    return partition;
}

/// The predicate's own partition over the same set: `true` for the tags the
/// whitelist accepts, `false` for the rest, with nothing left undecided.
fn boolPartition(query: *const QueryContext, predicate: u32) ?BoolPartition {
    const tree = query.tree;
    var partition: BoolPartition = .{ .error_set = undefined };
    var block_buffer: [2]u32 = undefined;
    const statements = returnOnlyBody(query, predicate, &block_buffer) orelse return null;
    var returns: usize = 0;
    for (statements) |statement| {
        const operand = tree.nodes.items(.data)[statement].opt_node.unwrap() orelse return null;
        const subject = switchSubject(query, @intFromEnum(operand)) orelse return null;
        const declared = parameterTypeNode(tree, parameterNodeOf(query, subject, predicate) orelse return null) orelse return null;
        const set = errorSetOfTypeNode(query, declared) orelse return null;
        if (returns == 0) {
            partition.error_set = set;
        } else if (!sameErrorSet(set, partition.error_set, tree)) {
            return null;
        }
        if (!collectBoolArms(tree, @intFromEnum(operand), partition.error_set, &partition)) return null;
        returns += 1;
    }
    for (partition.error_set.members[0..partition.error_set.len]) |member| {
        if (!partition.true_tags.contains(tree, member) and !partition.false_tags.contains(tree, member)) return null;
    }
    for (partition.true_tags.tokens[0..partition.true_tags.len]) |token| {
        if (partition.false_tags.contains(tree, token)) return null;
    }
    return partition;
}

/// The body of a function whose every statement is a `return`. A partition can
/// only be read off a body that decides its result and nothing else.
fn returnOnlyBody(
    query: *const QueryContext,
    function: u32,
    block_buffer: *[2]u32,
) ?[]const u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const body = functionBody(query, function) orelse return null;
    const statements = ast_walk.getBlockStatements(tree, body, block_buffer) orelse return null;
    if (statements.len == 0) return null;
    for (statements) |statement| {
        if (statement >= tags.len or tags[statement] != .@"return") return null;
    }
    return statements;
}

/// The `switch` whose arms decide `field_token` in this struct literal.
fn storedSwitchOver(
    query: *const QueryContext,
    operand: u32,
    field_token: u32,
    producer: u32,
) ?u32 {
    const tree = query.tree;
    var buffer: [2]std.zig.Ast.Node.Index = undefined;
    const init = tree.fullStructInit(&buffer, @enumFromInt(operand)) orelse return null;
    const wanted = tree.tokenSlice(field_token);
    for (init.ast.fields) |field| {
        const name = structInitFieldNameToken(tree, field) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name), wanted)) continue;
        const value = @intFromEnum(field);
        if (!isSwitchNode(tree, value)) return null;
        const subject = switchSubject(query, value) orelse return null;
        if (!isParameterOf(query, subject, producer)) return null;
        return value;
    }
    return null;
}

fn collectNullableArms(
    tree: *const std.zig.Ast,
    switch_node: u32,
    error_set: ErrorSet,
    null_tags: *TagSet,
    solid_tags: *TagSet,
    type_context: ?*TypeContext,
) bool {
    const tags = tree.nodes.items(.tag);
    const full = tree.switchFull(@enumFromInt(switch_node));
    if (full.ast.cases.len == 0) return false;
    for (full.ast.cases) |case_node| {
        const case = tree.fullSwitchCase(case_node) orelse return false;
        // An `else` prong decides nothing about the error partition.
        if (case.ast.values.len == 0) return false;
        const value = @intFromEnum(case.ast.target_expr);
        if (value >= tags.len) return false;
        const is_null = isNullIdentifier(tree, value);
        if (!is_null and !guards.isDefinitelyNonNullExpression(
            tree,
            value,
            type_context,
            tags,
            tree.nodes.items(.data),
        )) return false;
        for (case.ast.values) |prong| {
            const tag = errorTagToken(tree, @intFromEnum(prong)) orelse return false;
            if (!error_set.declares(tree, tag)) return false;
            if (is_null) null_tags.add(tree, tag) else solid_tags.add(tree, tag);
        }
    }
    return true;
}

fn collectBoolArms(
    tree: *const std.zig.Ast,
    switch_node: u32,
    error_set: ErrorSet,
    partition: *BoolPartition,
) bool {
    const full = tree.switchFull(@enumFromInt(switch_node));
    if (full.ast.cases.len == 0) return false;
    for (full.ast.cases) |case_node| {
        const case = tree.fullSwitchCase(case_node) orelse return false;
        if (case.ast.values.len == 0) return false;
        const truth = boolLiteral(tree, @intFromEnum(case.ast.target_expr)) orelse return false;
        for (case.ast.values) |prong| {
            const tag = errorTagToken(tree, @intFromEnum(prong)) orelse return false;
            if (!error_set.declares(tree, tag)) return false;
            if (truth) partition.true_tags.add(tree, tag) else partition.false_tags.add(tree, tag);
        }
    }
    return true;
}

// ---------------------------------------------------------------------------
// Lookup purity
// ---------------------------------------------------------------------------

/// The lookup must decide its answer from its parameters alone: a stateful
/// function could succeed on the first row and fail on the replay.
fn isDeterministicBody(query: *const QueryContext, function: u32, depth: u8) bool {
    if (depth >= purity_depth) return false;
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (function >= tags.len or tags[function] != .fn_decl) return false;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = treeFnProto(tree, function, &buffer) orelse return false;
    if (proto.extern_export_inline_token) |token| {
        switch (tree.tokenTag(token)) {
            .keyword_extern, .keyword_export, .keyword_inline => return false,
            else => {},
        }
    }
    const body = functionBody(query, function) orelse return false;
    var block_buffer: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, body, &block_buffer) orelse return false;
    var returns: usize = 0;
    for (statements) |statement| {
        if (statement >= tags.len or tags[statement] != .@"return") {
            return false;
        }
        const operand = tree.nodes.items(.data)[statement].opt_node.unwrap() orelse {
            return false;
        };
        if (!isPureExpression(query, function, @intFromEnum(operand), depth)) {
            return false;
        }
        returns += 1;
    }
    if (returns == 0) {
        return false;
    }
    return true;
}

fn isPureExpression(query: *const QueryContext, function: u32, node: u32, depth: u8) bool {
    if (depth >= purity_depth) return false;
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (node == 0 or node >= tags.len) return false;
    switch (tags[node]) {
        .grouped_expression, .@"comptime" => return isPureExpression(
            query,
            function,
            @intFromEnum(tree.nodes.items(.data)[node].node),
            depth,
        ),
        // A generic argument names a type instead of a parameter; a primitive
        // type name is a compile-time constant and cannot change the answer.
        .identifier => return isParameterOf(query, node, function) or isPrimitiveTypeName(tree, node),
        .number_literal, .char_literal, .string_literal, .multiline_string_literal, .enum_literal => return true,
        .call, .call_comma, .call_one, .call_one_comma => {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return false;
            for (call.ast.params) |param| {
                if (!isPureExpression(query, function, @intFromEnum(param), depth + 1)) return false;
            }
            const callee = @intFromEnum(call.ast.fn_expr);
            if (tags[callee] == .identifier) {
                const local = resolveLocalFunction(query, callee) orelse return false;
                return isDeterministicBody(query, local, depth + 1);
            }
            return isVerifiedPureStdCall(query, callee);
        },
        else => return false,
    }
}

/// The standard-library calls whose result depends on nothing but their
/// arguments. An arbitrary lookup, or an unresolvable callee, proves nothing.
fn isVerifiedPureStdCall(query: *const QueryContext, callee: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (callee >= tags.len or tags[callee] != .field_access) return false;

    var parts: [2][]const u8 = undefined;
    var len: usize = 0;
    var node = callee;
    while (len < parts.len) {
        if (node >= tags.len or tags[node] != .field_access) break;
        const access = tree.nodes.items(.data)[node].node_and_token;
        parts[len] = tree.tokenSlice(access[1]);
        len += 1;
        node = @intFromEnum(access[0]);
    }
    if (len == 0) return false;
    // The chain has to hang off the file's verified `std` import, not off a
    // local namespace that merely happens to be spelled `std`.
    if (node >= tags.len or tags[node] != .identifier) return false;

    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    if (!resolver.isVerifiedImportBinding(node, "std")) return false;

    // `a.b.c` is a `field_access` whose own token is the trailing name, so
    // `parts` was collected outermost first and the dotted name reads the
    // other way around: `std.mem.indexOf` is not `indexOf.mem`.
    var name: [64]u8 = undefined;
    var written: usize = 0;
    var index = len;
    while (index > 0) {
        index -= 1;
        if (written != 0) {
            name[written] = '.';
            written += 1;
        }
        if (written + parts[index].len >= name.len) return false;
        @memcpy(name[written .. written + parts[index].len], parts[index]);
        written += parts[index].len;
    }
    inline for (pure_std_calls) |allowed| {
        if (std.mem.eql(u8, name[0..written], allowed)) return true;
    }
    return false;
}

/// The primitive type names a call may name in a generic argument position.
/// Anything else has to be a parameter, so an unmodelled type or a global
/// value can never stand in for one.
fn isPrimitiveTypeName(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .identifier) return false;
    const token = tree.nodes.items(.main_token)[node];
    if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return false;
    const name = tree.tokenSlice(token);
    inline for (primitive_types) |primitive| {
        if (std.mem.eql(u8, name, primitive)) return true;
    }
    return false;
}

const primitive_types = [_][]const u8{
    "u1",   "u2",        "u8",       "u16",          "u32",            "u64",   "u128",
    "i8",   "i16",       "i32",      "i64",          "i128",           "usize", "isize",
    "f16",  "f32",       "f64",      "f80",          "f128",           "bool",  "void",
    "type", "anyopaque", "noreturn", "comptime_int", "comptime_float",
};

const pure_std_calls = [_][]const u8{
    "mem.indexOf",
    "mem.lastIndexOf",
    "mem.indexOfScalar",
    "mem.lastIndexOfScalar",
    "mem.indexOfPos",
    "mem.count",
    "mem.countScalar",
    "mem.eql",
    "mem.order",
    "mem.compare",
    "mem.startsWith",
    "mem.endsWith",
    "ascii.eqlIgnoreCase",
    "fmt.parseInt",
    "fmt.parseFloat",
    "fmt.parseBool",
};

/// The builtins that answer from their arguments and write nothing. Every
/// other builtin closes the window, which is what keeps `@memcpy`, `@memset`,
/// `@atomicStore`, `@atomicRmw`, `@swap`, and `@cmpxchg` out of it.
const pure_builtin_calls = [_][]const u8{
    "@Type",
    "@TypeOf",
    "@alignOf",
    "@as",
    "@bitCast",
    "@divExact",
    "@divFloor",
    "@divTrunc",
    "@enumFromInt",
    "@errorName",
    "@FieldType",
    "@hasDecl",
    "@hasField",
    "@import",
    "@intCast",
    "@intFromEnum",
    "@max",
    "@min",
    "@mod",
    "@rem",
    "@sizeOf",
    "@tagName",
    "@This",
    "@truncate",
    "@typeInfo",
    "@typeName",
};

// ---------------------------------------------------------------------------
// Structure helpers
// ---------------------------------------------------------------------------

/// A small set of binding name tokens. Overflow is treated as failure, so a
/// proof never silently drops a binding it was meant to track.
const NameSet = struct {
    tokens: [name_capacity]u32 = undefined,
    len: usize = 0,

    fn add(self: *NameSet, token: u32) void {
        if (token == 0 or self.len == name_capacity) return;
        if (self.contains(token)) return;
        self.tokens[self.len] = token;
        self.len += 1;
    }

    fn contains(self: NameSet, token: u32) bool {
        for (self.tokens[0..self.len]) |existing| {
            if (existing == token) return true;
        }
        return false;
    }

    fn isFull(self: NameSet) bool {
        return self.len == name_capacity;
    }
};

/// The declaration a bare name resolves to. `LexicalIndex` names a function by
/// its *prototype* node, but a body, a parameter scope, and every identity
/// check against them are keyed to the declaration that owns them, so the
/// prototype is only a way to find that declaration.
fn resolveLocalFunction(query: *const QueryContext, expr: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (expr == 0 or expr >= tags.len or tags[expr] != .identifier) return null;
    const token = tree.nodes.items(.main_token)[expr];
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));
    const found = query.lexical.findFunction(name, token) orelse return null;
    if (found >= tags.len) return null;
    if (tags[found] == .fn_decl) return found;
    return declarationOfPrototype(tree, found);
}

/// The declaration whose prototype is `proto`. The parent map cannot supply
/// it: a declaration walks its body only, never its own prototype, so the
/// link has to be read back off the declaration itself.
fn declarationOfPrototype(tree: *const std.zig.Ast, proto: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (proto == 0 or proto >= tags.len) return null;
    switch (tags[proto]) {
        .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi => {},
        else => return null,
    }
    const datas = tree.nodes.items(.data);
    for (tags, 0..) |tag, node| {
        if (tag != .fn_decl) continue;
        if (@intFromEnum(datas[node].node_and_node[0]) != proto) continue;
        return @intCast(node);
    }
    return null;
}

fn functionBody(query: *const QueryContext, function: u32) ?u32 {
    const tree = query.tree;
    if (function >= tree.nodes.len or tree.nodeTag(@enumFromInt(function)) != .fn_decl) return null;
    const body = @intFromEnum(tree.nodes.items(.data)[function].node_and_node[1]);
    if (body == 0 or body >= tree.nodes.len) return null;
    return body;
}

fn enclosingFunction(query: *const QueryContext, node: u32) ?u32 {
    if (node >= query.tree.nodes.len) return null;
    return query.lexical.enclosingFunction(query.firstToken(node));
}

fn insideFunction(query: *const QueryContext, node: u32, function: u32) bool {
    const tree = query.tree;
    const first = tree.firstToken(@enumFromInt(function));
    const last = tree.lastToken(@enumFromInt(function));
    const token = query.firstToken(node);
    return token >= first and token <= last;
}

fn containingBlock(query: *const QueryContext, node: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    var current = node;
    while (current != 0 and current < tags.len) {
        const parent = query.lexical.parent(current) orelse return null;
        if (parent == 0 or parent >= tags.len) return null;
        if (isBlockTag(tags[parent])) return parent;
        current = parent;
    }
    return null;
}

fn treeFnProto(
    tree: *const std.zig.Ast,
    node: u32,
    buffer: *[1]std.zig.Ast.Node.Index,
) ?std.zig.Ast.full.FnProto {
    if (node >= tree.nodes.len) return null;
    return switch (tree.nodeTag(@enumFromInt(node))) {
        .fn_proto => tree.fnProto(@enumFromInt(node)),
        .fn_proto_simple => tree.fnProtoSimple(buffer, @enumFromInt(node)),
        .fn_proto_one => tree.fnProtoOne(buffer, @enumFromInt(node)),
        .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(node)),
        .fn_decl => blk: {
            const proto = @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]);
            if (proto >= tree.nodes.len) break :blk null;
            break :blk treeFnProto(tree, proto, buffer);
        },
        else => null,
    };
}

fn isBlockTag(tag: std.zig.Ast.Node.Tag) bool {
    return tag == .block or tag == .block_semicolon or
        tag == .block_two or tag == .block_two_semicolon;
}

fn isSwitchNode(tree: *const std.zig.Ast, node: u32) bool {
    if (node >= tree.nodes.len) return false;
    return switch (tree.nodeTag(@enumFromInt(node))) {
        .@"switch", .switch_comma => true,
        else => false,
    };
}

fn isAssignmentTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .assign,
        .assign_add,
        .assign_sub,
        .assign_mul,
        .assign_div,
        .assign_mod,
        .assign_bit_and,
        .assign_bit_or,
        .assign_bit_xor,
        .assign_shl,
        .assign_shl_sat,
        .assign_shr,
        .assign_add_wrap,
        .assign_sub_wrap,
        .assign_mul_wrap,
        .assign_mul_sat,
        .assign_add_sat,
        .assign_sub_sat,
        => true,
        else => false,
    };
}

fn containsNode(tree: *const std.zig.Ast, node: u32, target: u32) bool {
    if (node == 0 or node >= tree.nodes.len or target >= tree.nodes.len) return false;
    return tree.firstToken(@enumFromInt(node)) <= tree.firstToken(@enumFromInt(target)) and
        tree.lastToken(@enumFromInt(target)) <= tree.lastToken(@enumFromInt(node));
}

fn statementIndex(statements: []const u32, statement: u32) ?usize {
    for (statements, 0..) |candidate, index| {
        if (candidate == statement) return index;
    }
    return null;
}

/// The statement of `statements` that holds `node`, which need not be the
/// statement itself: an unwrap usually sits inside a `return`.
fn containingStatement(
    tree: *const std.zig.Ast,
    statements: []const u32,
    node: u32,
) ?usize {
    for (statements, 0..) |statement, index| {
        if (statement == node or containsNode(tree, statement, node)) return index;
    }
    return null;
}

fn followingStatement(query: *const QueryContext, statement: u32) ?u32 {
    const tree = query.tree;
    const block = query.lexical.parent(statement) orelse return null;
    if (block >= tree.nodes.len or !isBlockTag(tree.nodeTag(@enumFromInt(block)))) return null;
    var block_buffer: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &block_buffer) orelse return null;
    const index = statementIndex(statements, statement) orelse return null;
    if (index + 1 >= statements.len) return null;
    return statements[index + 1];
}

fn bindingIdentifier(query: *const QueryContext, node: u32) ?u32 {
    const tree = query.tree;
    if (node >= tree.nodes.len or tree.nodeTag(@enumFromInt(node)) != .identifier) return null;
    if (query.resolveIdentifierBinding(node) == null) return null;
    return node;
}

fn bindingNameToken(query: *const QueryContext, node: u32) ?u32 {
    const tree = query.tree;
    if (node >= tree.nodes.len or tree.nodeTag(@enumFromInt(node)) != .identifier) return null;
    return query.resolveIdentifierBinding(node);
}

fn parameterOf(query: *const QueryContext, ident_node: u32) ?lexical_index.Candidate {
    const tree = query.tree;
    if (ident_node >= tree.nodes.len or tree.nodeTag(@enumFromInt(ident_node)) != .identifier) return null;
    const resolved = query.resolveIdentifierBinding(ident_node) orelse return null;
    const token = tree.nodeMainToken(@enumFromInt(ident_node));
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));
    for (query.lexical.namedCandidates(name)) |candidate| {
        if (candidate.kind != .parameter or candidate.name_token != resolved) continue;
        return candidate;
    }
    return null;
}

fn isParameterOf(query: *const QueryContext, ident_node: u32, function: u32) bool {
    const candidate = parameterOf(query, ident_node) orelse return false;
    return query.lexical.enclosingFunction(candidate.scope.first_token) == function;
}

fn parameterNodeOf(query: *const QueryContext, ident_node: u32, function: u32) ?u32 {
    const candidate = parameterOf(query, ident_node) orelse return null;
    if (query.lexical.enclosingFunction(candidate.scope.first_token) != function) return null;
    return candidate.node;
}

fn parameterTypeNode(tree: *const std.zig.Ast, param: u32) ?u32 {
    if (param >= tree.nodes.len) return null;
    if (import_resolver.isVarDeclTag(tree.nodeTag(@enumFromInt(param)))) {
        const full = tree.fullVarDecl(@enumFromInt(param)) orelse return null;
        const type_node = full.ast.type_node.unwrap() orelse return null;
        return @intFromEnum(type_node);
    }
    return param;
}

/// The declaration a name token belongs to, when it declares a variable. A
/// binding resolves to the identifier *after* `var`/`const`, which is what
/// `mut_token + 1` names; a declaration's own `main_token` is its `var` or
/// `const` keyword and names nothing, so matching on it finds no declaration
/// at all. Matching the name token instead also keeps two declarations of one
/// name apart, which is what lets the caller's own-function check decide.
fn varDeclAtName(query: *const QueryContext, name_token: u32) ?u32 {
    const tree = query.tree;
    if (name_token == 0) return null;
    for (tree.nodes.items(.tag), 0..) |tag, node| {
        if (!import_resolver.isVarDeclTag(tag)) continue;
        const full = tree.fullVarDecl(@enumFromInt(node)) orelse continue;
        if (full.ast.mut_token + 1 != name_token) continue;
        return @intCast(node);
    }
    return null;
}

fn localVarDecl(query: *const QueryContext, ident_node: u32, function: u32) ?u32 {
    const tree = query.tree;
    const name_token = bindingNameToken(query, ident_node) orelse return null;
    const decl = varDeclAtName(query, name_token) orelse return null;
    if (enclosingFunction(query, decl) != function) return null;
    const full = tree.fullVarDecl(@enumFromInt(decl)) orelse return null;
    if (full.visib_token != null or full.extern_export_token != null or full.threadlocal_token != null) return null;
    if (full.comptime_token != null or full.ast.align_node != .none or
        full.ast.addrspace_node != .none or full.ast.section_node != .none) return null;
    if (tree.tokenTag(full.ast.mut_token) != .keyword_var) return null;
    return decl;
}

/// `|row|` after a `for` input: a single, plain capture. An index capture or a
/// pointer capture changes what the loop body receives.
fn forPayloadToken(tree: *const std.zig.Ast, last_input_node: u32) ?u32 {
    const token_tags = tree.tokens.items(.tag);
    const expected = [_]std.zig.Token.Tag{ .r_paren, .pipe, .identifier, .pipe };
    var token = tree.lastToken(@enumFromInt(last_input_node));
    for (expected) |want| {
        if (token + 1 >= token_tags.len) return null;
        token += 1;
        if (token_tags[token] != want) return null;
    }
    return token - 1;
}

fn isIntLiteral(tree: *const std.zig.Ast, node: u32, want: u64) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .number_literal) return false;
    const text = tree.tokenSlice(tree.nodes.items(.main_token)[node]);
    const value = std.fmt.parseUnsigned(u64, text, 10) catch return false;
    return value == want;
}

fn isPositiveIntLiteral(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .number_literal) return false;
    const text = tree.tokenSlice(tree.nodes.items(.main_token)[node]);
    const value = std.fmt.parseUnsigned(u64, text, 10) catch return false;
    return value > 0;
}

fn isNullIdentifier(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .identifier) return false;
    const token = tree.nodes.items(.main_token)[node];
    if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return false;
    return std.mem.eql(u8, tree.tokenSlice(token), "null");
}

fn boolLiteral(tree: *const std.zig.Ast, node: u32) ?bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .identifier) return null;
    const token = tree.nodes.items(.main_token)[node];
    if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return null;
    const text = tree.tokenSlice(token);
    if (std.mem.eql(u8, text, "true")) return true;
    if (std.mem.eql(u8, text, "false")) return false;
    return null;
}

fn structInitFieldNameToken(tree: *const std.zig.Ast, value_node: std.zig.Ast.Node.Index) ?u32 {
    const first = tree.firstToken(value_node);
    if (first < 3 or first >= tree.tokens.len) return null;
    if (tree.tokenTag(first - 1) != .equal) return null;
    if (tree.tokenTag(first - 2) != .identifier) return null;
    if (tree.tokenTag(first - 3) != .period) return null;
    return first - 2;
}

fn switchSubject(query: *const QueryContext, switch_node: u32) ?u32 {
    const tree = query.tree;
    if (!isSwitchNode(tree, switch_node)) return null;
    const full = tree.switchFull(@enumFromInt(switch_node));
    return @intFromEnum(full.ast.condition);
}

/// The tag name of an `error.Foo` literal. `main_token` is the `error`
/// keyword and `data` is never written for this tag, so the name is the
/// identifier two tokens on.
fn errorTagToken(tree: *const std.zig.Ast, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .error_value) return null;
    const token = tree.nodeMainToken(@enumFromInt(node)) + 2;
    if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return null;
    return token;
}

// ---------------------------------------------------------------------------
// Escape checks
// ---------------------------------------------------------------------------

fn namesBinding(query: *const QueryContext, node: u32, name_token: u32) bool {
    var found = false;
    mentionsBinding(query, node, name_token, &found);
    return found;
}

fn namesAnyOf(query: *const QueryContext, node: u32, names: NameSet) bool {
    var found = false;
    for (names.tokens[0..names.len]) |name_token| {
        mentionsBinding(query, node, name_token, &found);
        if (found) return true;
    }
    return false;
}

fn mentionsBinding(query: *const QueryContext, node: u32, name_token: u32, found: *bool) void {
    if (found.* or node == 0) return;
    const Visitor = struct {
        query: *const QueryContext,
        name_token: u32,
        found: *bool,
        stop: bool = false,

        pub fn visit(self: *@This(), tree: *const std.zig.Ast, child: u32, tag: std.zig.Ast.Node.Tag) !void {
            if (self.found.* or self.stop) return;
            if (child >= tree.nodes.len or tag != .identifier) return;
            if (self.query.resolveIdentifierBinding(child) == self.name_token) {
                self.found.* = true;
                self.stop = true;
            }
        }
    };
    var visitor = Visitor{ .query = query, .name_token = name_token, .found = found };
    // The visitor only records whether the name is bound, so it has no error
    // to return and the walk cannot fail.
    ast_walk.walk(Visitor, query.tree, node, &visitor) catch unreachable;
}

/// Is `name` ever handed to a call or taken by address inside `function`? A
/// payload that leaves cannot carry the producer's partition into the unwrap.
fn payloadEscapes(query: *const QueryContext, function: u32, name: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    var node: u32 = 1;
    while (node < tags.len) : (node += 1) {
        if (!insideFunction(query, node, function)) continue;
        switch (tags[node]) {
            .address_of => {
                if (namesBinding(query, @intFromEnum(tree.nodes.items(.data)[node].node), name)) return true;
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                // A cast is the only way to reach through a `const` payload.
                const token = tree.nodes.items(.main_token)[node];
                if (token >= tree.tokens.len) return true;
                const builtin = tree.tokenSlice(token);
                if (!std.mem.eql(u8, builtin, "@constCast") and
                    !std.mem.eql(u8, builtin, "@ptrCast") and
                    !std.mem.eql(u8, builtin, "@alignCast")) continue;
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&buffer, @enumFromInt(node)) orelse return true;
                if (params.len != 1) return true;
                if (namesBinding(query, @intFromEnum(params[0]), name)) return true;
            },
            .call, .call_comma, .call_one, .call_one_comma => {
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return true;
                for (call.ast.params) |param| {
                    if (namesBinding(query, @intFromEnum(param), name)) return true;
                }
            },
            else => {},
        }
    }
    return false;
}

fn leavesTheLoop(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;
    switch (tags[node]) {
        .@"return" => return true,
        .@"break", .@"continue" => return !isLabeledExit(tree, node),
        else => return false,
    }
}

/// A guard that returns, breaks, or continues leaves the guarded code behind;
/// a labeled exit only leaves its own block and proves nothing. The same shape
/// answers both "leaves the loop" and "leaves the function".
fn leavesTheFunction(tree: *const std.zig.Ast, node: u32) bool {
    return leavesTheLoop(tree, node);
}

fn isLabeledExit(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;
    return switch (tags[node]) {
        .@"break", .@"continue" => tree.nodes.items(.data)[node].opt_token_and_opt_node[0].unwrap() != null,
        else => false,
    };
}

fn returnsStructLiteral(query: *const QueryContext, function: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const body = functionBody(query, function) orelse return false;
    var block_buffer: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, body, &block_buffer) orelse return false;
    if (statements.len == 0) return false;
    for (statements) |statement| {
        if (statement >= tags.len or tags[statement] != .@"return") return false;
        const operand = tree.nodes.items(.data)[statement].opt_node.unwrap() orelse return false;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        if (tree.fullStructInit(&buffer, operand) == null) return false;
    }
    return true;
}

// ---------------------------------------------------------------------------
// Error sets
// ---------------------------------------------------------------------------

fn errorSetOfTypeNode(query: *const QueryContext, type_node: u32) ?ErrorSet {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (type_node >= tags.len) return null;
    if (tags[type_node] == .error_set_decl) return errorSetAt(tree, type_node, 0);
    if (tags[type_node] != .identifier) return null;
    const name_token = query.resolveIdentifierBinding(type_node) orelse return null;
    const decl = varDeclAtName(query, name_token) orelse return null;
    const full = tree.fullVarDecl(@enumFromInt(decl)) orelse return null;
    const init = full.ast.init_node.unwrap() orelse return null;
    const init_node = @intFromEnum(init);
    if (init_node >= tags.len or tags[init_node] != .error_set_decl) return null;
    return errorSetAt(tree, init_node, decl);
}

fn errorSetAt(tree: *const std.zig.Ast, error_set_node: u32, declaration: u32) ?ErrorSet {
    const token_tags = tree.tokens.items(.tag);
    var set = ErrorSet{ .declaration = declaration };
    var token = tree.firstToken(@enumFromInt(error_set_node));
    const end = tree.lastToken(@enumFromInt(error_set_node));
    while (token <= end and token < token_tags.len) : (token += 1) {
        if (token_tags[token] != .identifier) continue;
        // The `error` keyword itself is never a tag.
        if (std.mem.eql(u8, tree.tokenSlice(token), "error")) continue;
        if (set.len == tag_capacity) return null;
        set.members[set.len] = token;
        set.len += 1;
    }
    if (set.len == 0) return null;
    return set;
}

fn sameErrorSet(left: ErrorSet, right: ErrorSet, tree: *const std.zig.Ast) bool {
    if (left.len != right.len) return false;
    // A named set is the same set only when it is the same declaration; two
    // inline `error{...}` spellings match only member for member.
    if (left.declaration != 0 or right.declaration != 0) return left.declaration == right.declaration;
    for (left.members[0..left.len], 0..) |member, index| {
        if (!std.mem.eql(u8, tree.tokenSlice(member), tree.tokenSlice(right.members[index]))) return false;
    }
    return true;
}

// ---------------------------------------------------------------------------
// Regression scenarios
// ---------------------------------------------------------------------------

const Source = @import("../../source.zig").Source;
const Diagnostic = @import("../../diagnostic.zig").Diagnostic;
const Checker = @import("../optional_unwrap_engine.zig").OptionalUnwrapEngineChecker;

/// A filter that keeps only the rows whose lookup succeeded, replayed over the
/// retained prefix with the same query. `preamble` sits at container scope,
/// `guard` is the statement that decides whether a row is kept, and `between`
/// runs after the filter and before the replay.
fn retainedFixture(
    comptime preamble: []const u8,
    comptime guard: []const u8,
    comptime capacity: []const u8,
    comptime between: []const u8,
    comptime replay: []const u8,
) [:0]const u8 {
    return "const std = @import(\"std\");\n\n" ++
        preamble ++
        "\npub fn sumPositions(items: []const []const u8, query: []const u8) usize {\n" ++
        "var retained: [8][]const u8 = undefined;\nvar count: usize = 0;\n" ++
        "for (items) |item| {\n" ++
        guard ++
        capacity ++
        "retained[count] = item;\ncount += 1;\n}\n" ++
        between ++
        "var sum: usize = 0;\nfor (retained[0..count]) |row| sum += " ++ replay ++ ";\n" ++
        "return sum;\n}\n\n" ++
        "pub fn unchecked(row: []const u8, query: []const u8) usize {\n" ++
        "return locate(row, query).?;\n}\n";
}

/// The lookup the issue's filter replays: a pure call on its two arguments.
const deterministic_lookup =
    "fn locate(text: []const u8, query: []const u8) ?usize {\n" ++
    "return std.mem.indexOf(u8, text, query);\n}\n";

/// `count` reaching the buffer's length ends the append, so the prefix read
/// back is always inside the buffer.
const bounded_filter = "if (count == retained.len) break;\n";

const matched_lookup_guard = "_ = locate(item, query) orelse continue;\n";

/// Container-scope declarations spelled like the filter's own. The buffer is
/// still the replaying function's declaration, so the proof holds: a name
/// token names one declaration, and it is the one inside `sumPositions`.
const shadowed_buffer_names =
    "var retained: [8][]const u8 = undefined;\nvar count: usize = 0;\n";

/// The same replay over a buffer the function was handed. The prefix is still
/// bounded, but no declaration here owns the storage, and only a declaration
/// inside the replaying function carries that claim.
fn handedBufferFixture() [:0]const u8 {
    return "const std = @import(\"std\");\n\n" ++
        deterministic_lookup ++
        "\npub fn sumPositions(items: []const []const u8, query: []const u8, " ++
        "retained: [8][]const u8) usize {\n" ++
        "var count: usize = 0;\n" ++
        "for (items) |item| {\n" ++
        matched_lookup_guard ++
        bounded_filter ++
        "retained[count] = item;\ncount += 1;\n}\n" ++
        "var sum: usize = 0;\nfor (retained[0..count]) |row| sum += " ++
        "locate(row, query).?;\n" ++
        "return sum;\n}\n\n" ++
        "pub fn unchecked(row: []const u8, query: []const u8) usize {\n" ++
        "return locate(row, query).?;\n}\n";
}

/// The same filter, with one extra parameter the proof never tracks: a
/// mutable view of bytes the caller owns. This is the shape `[]const` cannot
/// answer for, because it says nothing about who else may write the backing.
fn aliasFixture(
    comptime param: []const u8,
    comptime between: []const u8,
) [:0]const u8 {
    return "const std = @import(\"std\");\n\n" ++
        deterministic_lookup ++
        "\npub fn sumPositions(items: []const []const u8, query: []const u8, " ++
        param ++
        ") usize {\n" ++
        "var retained: [8][]const u8 = undefined;\nvar count: usize = 0;\n" ++
        "for (items) |item| {\n" ++
        matched_lookup_guard ++
        bounded_filter ++
        "retained[count] = item;\ncount += 1;\n}\n" ++
        between ++
        "var sum: usize = 0;\nfor (retained[0..count]) |row| sum += " ++
        "locate(row, query).?;\n" ++
        "return sum;\n}\n\n" ++
        "pub fn unchecked(row: []const u8, query: []const u8) usize {\n" ++
        "return locate(row, query).?;\n}\n";
}

/// A local helper the purity walk accepts: one `return` of a verified `std`
/// call over its own parameter.
const pure_helper = "fn isEmpty(text: []const u8) bool { return std.mem.eql(u8, text, \"\"); }\n";

/// A producer whose payload follows its own error partition, and a whitelist
/// over the very same error set.
fn taxonomyFixture(
    comptime producer: []const u8,
    comptime predicate: []const u8,
    comptime consumer: []const u8,
) [:0]const u8 {
    return "const ParseError = error{BadEscape, UnexpectedEnd, OutOfMemory};\n" ++
        "const Info = struct { position: ?usize };\n\n" ++
        producer ++
        "\n" ++
        predicate ++
        "\n" ++
        consumer ++
        "\n";
}

const positioned_producer =
    "fn diagnostic(err: ParseError) Info {\nreturn .{ .position = switch (err) {\n" ++
    "error.BadEscape, error.UnexpectedEnd => 6,\nerror.OutOfMemory => null,\n} };\n}\n";

const positioned_predicate =
    "fn isPositioned(err: ParseError) bool {\nreturn switch (err) {\n" ++
    "error.BadEscape, error.UnexpectedEnd => true,\nerror.OutOfMemory => false,\n};\n}\n";

fn countUnwraps(code: [:0]const u8, name: []const u8) !usize {
    var source = Source.init(std.testing.allocator, name, code);
    defer source.deinit();
    try std.testing.expectEqual(@as(usize, 0), (try source.ast()).errors.len);
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(std.testing.allocator);
        diagnostics.deinit(std.testing.allocator);
    }
    try Checker.checker.checkAst(&source, std.testing.allocator, &diagnostics, .{
        .build_metadata = null,
    });
    for (diagnostics.items) |diagnostic| {
        try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
    return diagnostics.items.len;
}

test "a retained row is replayed only for the row the lookup accepted" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{
            .name = "deterministic retained filter",
            .input = retainedFixture(
                deterministic_lookup,
                matched_lookup_guard,
                bounded_filter,
                "",
                "locate(row, query).?",
            ),
            // The retained replay is proved; the public caller is not.
            .warnings = 1,
        },
        .{
            .name = "buffer name also declared at container scope",
            .input = retainedFixture(
                deterministic_lookup ++ shadowed_buffer_names,
                matched_lookup_guard,
                bounded_filter,
                "",
                "locate(row, query).?",
            ),
            // Two declarations spell one name; only the replaying function's
            // own is storage it can prove it wrote.
            .warnings = 1,
        },
        .{
            .name = "buffer handed in as a parameter",
            .input = handedBufferFixture(),
            .warnings = 2,
        },
        .{
            .name = "stateful lookup",
            .input = retainedFixture(
                "var attempts: usize = 0;\nfn locate(text: []const u8, query: []const u8) ?usize {\n" ++
                    "attempts += 1;\nreturn std.mem.indexOf(u8, text, query);\n}\n",
                matched_lookup_guard,
                bounded_filter,
                "",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "lookup over a global table",
            .input = retainedFixture(
                "const table = [_][]const u8{ \"ab\" };\nfn locate(text: []const u8, query: []const u8) ?usize {\n" ++
                    "return std.mem.indexOf(u8, table[0], query);\n}\n",
                matched_lookup_guard,
                bounded_filter,
                "",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "replayed with a different query",
            .input = retainedFixture(
                deterministic_lookup,
                matched_lookup_guard,
                bounded_filter,
                "const other: []const u8 = \"zz\";\n",
                "locate(row, other).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "query rebound before the replay",
            .input = retainedFixture(
                deterministic_lookup,
                matched_lookup_guard,
                bounded_filter,
                "query = \"\";\n",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "buffer address taken before the replay",
            .input = retainedFixture(
                deterministic_lookup ++ "fn observe(values: *[8][]const u8) void { _ = values; }\n",
                matched_lookup_guard,
                bounded_filter,
                "observe(&retained);\n",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "buffer written outside the pair",
            .input = retainedFixture(
                deterministic_lookup,
                matched_lookup_guard,
                bounded_filter,
                "if (items.len > 0) retained[0] = items[0];\n",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "counter moved outside the pair",
            .input = retainedFixture(
                deterministic_lookup,
                matched_lookup_guard,
                bounded_filter,
                "count += 2;\n",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "no capacity guard",
            .input = retainedFixture(
                deterministic_lookup,
                matched_lookup_guard,
                "",
                "",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "guard tests a different predicate",
            .input = retainedFixture(
                deterministic_lookup,
                "_ = std.mem.startsWith(u8, item, query) orelse continue;\n",
                bounded_filter,
                "",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "verified pure call inside the closed window",
            .input = retainedFixture(
                deterministic_lookup ++ pure_helper,
                matched_lookup_guard,
                bounded_filter,
                "if (isEmpty(query)) return 0;\n",
                "locate(row, query).?",
            ),
            // The purity proof is reused rather than re-derived: a call that
            // names the shared query is fine once the call itself is proved.
            .warnings = 1,
        },
        .{
            .name = "nullary helper rewrites the backing between guard and replay",
            .input = retainedFixture(
                deterministic_lookup ++
                    "var backing: [4]u8 = undefined;\nfn clobber() void { backing[0] = 'z'; }\n",
                matched_lookup_guard,
                bounded_filter,
                "clobber();\n",
                "locate(row, query).?",
            ),
            // The call names nothing at all, and the bytes still change.
            .warnings = 2,
        },
        .{
            .name = "global written between the filter and the replay",
            .input = retainedFixture(
                deterministic_lookup ++ "var tally: usize = 0;\n",
                matched_lookup_guard,
                bounded_filter,
                "tally += 1;\n",
                "locate(row, query).?",
            ),
            .warnings = 2,
        },
        .{
            .name = "write builtin rewrites the retained bytes",
            .input = aliasFixture("editor: []u8", "@memset(editor, 'z');\n"),
            // The builtin writes every byte of a mutable view the proof cannot
            // tie to the buffer, so the bytes the guard matched may be gone and
            // the replay really can panic. A builtin that only filled fresh
            // local storage would model no defect at all.
            .warnings = 2,
        },
        .{
            .name = "row bytes rewritten through a mutable alias",
            .input = aliasFixture("editor: []u8", "editor[0] = 'z';\n"),
            .warnings = 2,
        },
        .{
            .name = "row bytes rewritten through an indirect alias",
            .input = aliasFixture("editor: *[]u8", "editor.*[0] = 'z';\n"),
            .warnings = 2,
        },
        .{
            .name = "query rewritten through a local mutable copy",
            .input = aliasFixture("editor: []u8", "var local = query;\nlocal[0] = 'z';\n"),
            // The header write is owned storage; the element write behind it
            // is the very bytes the guard inspected.
            .warnings = 2,
        },
    };
    for (cases) |case| {
        const warnings = countUnwraps(case.input, case.name) catch |err| {
            std.debug.print("retained row scenario: {s}\n", .{case.name});
            return err;
        };
        try std.testing.expectEqual(case.warnings, warnings);
    }
}

test "a producer's error partition decides its own payload" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{
            .name = "matched producer and whitelist",
            .input = taxonomyFixture(
                positioned_producer,
                positioned_predicate,
                "fn consume(value: Info) void { _ = value; }\n\n" ++
                    "fn position(err: ParseError) ?usize {\n" ++
                    "const info = diagnostic(err);\n" ++
                    "if (!isPositioned(err)) return null;\n" ++
                    "return info.position.?;\n}\n",
            ),
            .warnings = 0,
        },
        .{
            .name = "whitelist decides the unwrap's branch",
            .input = taxonomyFixture(
                positioned_producer,
                positioned_predicate,
                "fn position(err: ParseError) ?usize {\n" ++
                    "const info = diagnostic(err);\n" ++
                    "if (isPositioned(err)) return info.position.?;\n" ++
                    "return null;\n}\n",
            ),
            .warnings = 0,
        },
        .{
            .name = "producer partitioned another error value",
            .input = taxonomyFixture(
                positioned_producer,
                positioned_predicate,
                "fn mismatched(reported: ParseError) usize {\n" ++
                    "const info = diagnostic(error.OutOfMemory);\n" ++
                    "if (!isPositioned(reported)) return 0;\n" ++
                    "return info.position.?;\n}\n",
            ),
            .warnings = 1,
        },
        .{
            .name = "unrelated whitelist accepts an unpositioned tag",
            .input = taxonomyFixture(
                positioned_producer,
                "fn acceptsAny(err: ParseError) bool {\nreturn switch (err) {\n" ++
                    "error.BadEscape, error.UnexpectedEnd, error.OutOfMemory => true,\n};\n}\n",
                "fn unrelated(err: ParseError) usize {\n" ++
                    "const info = diagnostic(err);\n" ++
                    "if (!acceptsAny(err)) return 0;\n" ++
                    "return info.position.?;\n}\n",
            ),
            .warnings = 1,
        },
        .{
            .name = "allocation failure payload without a guard",
            .input = taxonomyFixture(
                positioned_producer,
                positioned_predicate,
                "fn unpositioned(err: ParseError) usize {\n" ++
                    "const info = diagnostic(err);\n" ++
                    "return info.position.?;\n}\n",
            ),
            .warnings = 1,
        },
        .{
            .name = "payload handed to a call before the unwrap",
            .input = taxonomyFixture(
                positioned_producer,
                positioned_predicate,
                "fn consume(value: Info) void { _ = value; }\n\n" ++
                    "fn escaped(err: ParseError) usize {\n" ++
                    "const info = diagnostic(err);\n" ++
                    "if (!isPositioned(err)) return 0;\n" ++
                    "consume(info);\n" ++
                    "return info.position.?;\n}\n",
            ),
            .warnings = 1,
        },
        .{
            .name = "producer without an exhaustive partition",
            .input = taxonomyFixture(
                "fn diagnostic(err: ParseError) Info {\nreturn .{ .position = switch (err) {\n" ++
                    "error.BadEscape, error.UnexpectedEnd => 6,\n" ++
                    "else => null,\n} };\n}\n",
                positioned_predicate,
                "fn position(err: ParseError) ?usize {\n" ++
                    "const info = diagnostic(err);\n" ++
                    "if (!isPositioned(err)) return null;\n" ++
                    "return info.position.?;\n}\n",
            ),
            .warnings = 1,
        },
    };
    for (cases) |case| {
        const warnings = countUnwraps(case.input, case.name) catch |err| {
            std.debug.print("error partition scenario: {s}\n", .{case.name});
            return err;
        };
        try std.testing.expectEqual(case.warnings, warnings);
    }
}
