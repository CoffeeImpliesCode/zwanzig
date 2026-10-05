const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
const lexical_index = @import("../../analysis/lexical_index.zig");
const ids = @import("../../ids.zig");
const TypeContext = @import("../../type_context.zig").TypeContext;
const assertions = @import("../../assertions.zig");
pub const QueryContext = @import("bindings.zig").QueryContext;

pub fn isGuardedByAssertion(
    query: *const QueryContext,
    unwrap_node: u32,
    target: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
    scope: *const assertions.AssertionScope,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var block = unwrap_node;
    for (0..64) |_| {
        if (block >= parent_map.len) return false;
        block = parent_map[block];
        if (block == 0 or block >= tags.len) return false;
        switch (tags[block]) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => break,
            else => {},
        }
    } else return false;
    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;
    const before = tree.nodeMainToken(@enumFromInt(unwrap_node));
    var fact = false;
    for (statements) |statement| {
        if (query.firstToken(statement) >= before) break;
        if (statementMayMutateStorageBefore(query, statement, target, tags, datas, block, unwrap_node, type_context))
            fact = false;
        if (query.lastToken(statement) >= before) continue;
        const is_try = tags[statement] == .@"try";
        const call_node = if (is_try) @intFromEnum(datas[statement].node) else statement;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse continue;
        if (call.ast.params.len != 1) continue;
        const name = assertions.resolveDebugAssertionName(tree, call.ast.fn_expr, scope, query.lexical) orelse
            if (is_try) assertions.resolveAssertionName(tree, call.ast.fn_expr, scope) orelse continue else continue;
        if (assertions.constraintKindForName(name) != .boolean) continue;
        const condition = @intFromEnum(call.ast.params[0]);
        if (conditionImpliesNotNull(query, condition, target) and
            !statementMayMutateStorage(query, condition, target, tags, datas, block, type_context))
            fact = true;
    }
    return fact;
}

pub fn isGuardedByLazyInit(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    // Find the containing block
    var node = unwrap_node;
    var block_node: ?u32 = null;
    var depth: u32 = 0;

    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;

        if (tags[parent] == .block or tags[parent] == .block_two or
            tags[parent] == .block_semicolon or tags[parent] == .block_two_semicolon)
        {
            block_node = parent;
            break;
        }
        node = parent;
    }

    const block = block_node orelse return false;

    // Scan the block for lazy init pattern
    return scanBlockForLazyInit(
        query,
        block,
        unwrap_node,
        unwrapped_var,
        type_context,
        tags,
        datas,
        main_tokens,
        token_starts,
    );
}

fn scanBlockForLazyInit(
    query: *const QueryContext,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
) bool {
    const tree = query.tree;
    if (block >= tags.len) return false;

    // Get position of the unwrap node.
    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    // Get statements from the block.
    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;
    var fact = false;

    // A lazy initialization proof remains valid only until a later storage write.
    for (statements) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) continue;
        if (isInSubtree(tree, stmt, unwrap_node)) {
            // The statement holding the unwrap proves nothing about itself,
            // but what it evaluates ahead of the unwrap runs first.
            if (statementMayMutateStorageBefore(query, stmt, unwrapped_var, tags, datas, block, unwrap_node, type_context))
                fact = false;
            continue;
        }

        if (tags[stmt] == .@"if" or tags[stmt] == .if_simple) {
            const full = tree.fullIf(@enumFromInt(stmt)) orelse {
                fact = false;
                continue;
            };
            const cond = @intFromEnum(full.ast.cond_expr);
            if (checksNull(query, cond, unwrapped_var)) {
                const then_expr = @intFromEnum(full.ast.then_expr);
                if (branchProvesNonNull(
                    query,
                    then_expr,
                    unwrapped_var,
                    type_context,
                    tags,
                    datas,
                    block,
                )) {
                    if (full.ast.else_expr.unwrap()) |else_node| {
                        if (statementMayMutateStorage(
                            query,
                            @intFromEnum(else_node),
                            unwrapped_var,
                            tags,
                            datas,
                            block,
                            type_context,
                        )) {
                            fact = false;
                            continue;
                        }
                    }
                    fact = true;
                    continue;
                }
            }
        }
        if (statementMayMutateStorage(query, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
        }
    }

    return fact;
}

/// A `defer` reached as a direct statement of a branch body is registered by
/// the branch's own scope, so its body runs when that scope exits: after every
/// statement of the branch and before the statement holding the guarded
/// unwrap. A write such a deferred body may make therefore outlives the
/// assignment that would otherwise prove the branch target non-null, and no
/// later statement of the branch can revive the fact it destroys. An
/// `errdefer` body runs only when its scope exits with an error, which cannot
/// reach the following statement, so it keeps the ordinary treatment where a
/// later assignment may still re-establish the fact.
fn branchSchedulesPendingDefer(
    query: *const QueryContext,
    statement: u32,
    var_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    type_context: ?*TypeContext,
) bool {
    if (statement >= tags.len or tags[statement] != .@"defer") return false;
    return statementMayMutateStorageAfterScopeExit(query, statement, var_node, tags, datas, block, type_context);
}

fn branchProvesNonNull(
    query: *const QueryContext,
    node: u32,
    var_node: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
) bool {
    const tree = query.tree;
    if (node >= tags.len) return false;

    switch (tags[node]) {
        .assign => {
            const pair = datas[node].node_and_node;
            const lhs = @intFromEnum(pair[0]);
            const rhs = @intFromEnum(pair[1]);
            return sameVariable(query, lhs, var_node) and
                isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas);
        },
        .block, .block_semicolon => {
            const extra = datas[node].extra_range;
            const start: usize = @intFromEnum(extra.start);
            const end: usize = @intFromEnum(extra.end);
            var fact = false;

            for (start..end) |index| {
                const statement = tree.extra_data[index];
                if (statement >= tags.len) continue;
                if (branchSchedulesPendingDefer(
                    query,
                    statement,
                    var_node,
                    tags,
                    datas,
                    block,
                    type_context,
                )) return false;

                if (tags[statement] == .assign) {
                    const pair = datas[statement].node_and_node;
                    const lhs = @intFromEnum(pair[0]);
                    const rhs = @intFromEnum(pair[1]);
                    if (sameVariable(query, lhs, var_node)) {
                        fact = isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas);
                        continue;
                    }
                }

                if (statementMayMutateStorage(query, statement, var_node, tags, datas, block, type_context)) {
                    fact = false;
                }
            }

            return fact;
        },
        .block_two, .block_two_semicolon => {
            const opt_nodes = datas[node].opt_node_and_opt_node;
            var fact = false;
            if (opt_nodes[0].unwrap()) |statement| {
                const statement_node = @intFromEnum(statement);
                if (branchSchedulesPendingDefer(
                    query,
                    statement_node,
                    var_node,
                    tags,
                    datas,
                    block,
                    type_context,
                )) return false;
                fact = branchProvesNonNull(
                    query,
                    statement_node,
                    var_node,
                    type_context,
                    tags,
                    datas,
                    block,
                );
            }
            if (opt_nodes[1].unwrap()) |statement| {
                const statement_node = @intFromEnum(statement);
                if (branchSchedulesPendingDefer(
                    query,
                    statement_node,
                    var_node,
                    tags,
                    datas,
                    block,
                    type_context,
                )) return false;
                if (tags[statement_node] == .assign) {
                    const pair = datas[statement_node].node_and_node;
                    const lhs = @intFromEnum(pair[0]);
                    const rhs = @intFromEnum(pair[1]);
                    if (sameVariable(query, lhs, var_node)) {
                        fact = isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas);
                    } else if (statementMayMutateStorage(query, statement_node, var_node, tags, datas, block, type_context)) {
                        fact = false;
                    }
                } else if (statementMayMutateStorage(query, statement_node, var_node, tags, datas, block, type_context)) {
                    fact = false;
                }
            }
            return fact;
        },
        else => return false,
    }
}

/// Two ways the storage is proved non-null by the statements that precede the
/// unwrap in its own block: a declaration written with an optional type and a
/// value that cannot be null, and a branch join whose every exit leaves the
/// storage non-null. Both facts end at the first statement that may write the
/// storage, so a later clear is still reported.
pub fn isProvenByLocalInitialization(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    var node = unwrap_node;
    var block_node: ?u32 = null;
    var depth: u32 = 0;
    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;
        if (tags[parent] == .block or tags[parent] == .block_two or
            tags[parent] == .block_semicolon or tags[parent] == .block_two_semicolon)
        {
            block_node = parent;
            break;
        }
        node = parent;
    }

    const block = block_node orelse return false;
    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    var fact = false;
    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;

    for (statements) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;
        if (token_starts[main_tokens[stmt]] >= unwrap_pos) continue;
        // The statement that holds the unwrap is the only one that spans it:
        // it cannot prove anything about itself, but an operand it evaluates
        // ahead of the unwrap still runs first and ends an earlier fact.
        if (query.firstToken(stmt) <= query.firstToken(unwrap_node) and
            query.lastToken(stmt) >= query.lastToken(unwrap_node))
        {
            if (statementMayMutateStorageBefore(query, stmt, unwrapped_var, tags, datas, block, unwrap_node, type_context))
                fact = false;
            continue;
        }

        if (declaresOptionalFromNonNullValue(query, stmt, unwrapped_var, type_context, tags, datas)) {
            fact = true;
            continue;
        }
        if (branchJoinProvesNonNull(query, stmt, unwrapped_var, type_context, tags, datas, block, 0)) {
            fact = true;
            continue;
        }
        if (statementMayMutateStorageBefore(query, stmt, unwrapped_var, tags, datas, block, unwrap_node, type_context)) {
            fact = false;
        }
    }
    return fact;
}

/// `const built: ?Fd = .{ .n = 0 };` — the declaration names the unwrapped
/// storage, spells an optional type, and gives it a value that cannot be
/// null. The written type is required because an inferred declaration says
/// nothing about nullability at all.
fn declaresOptionalFromNonNullValue(
    query: *const QueryContext,
    statement: u32,
    target: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const tree = query.tree;
    if (statement >= tags.len or !import_resolver.isVarDeclTag(tags[statement])) return false;
    const full = tree.fullVarDecl(@enumFromInt(statement)) orelse return false;
    const type_node = @intFromEnum(full.ast.type_node.unwrap() orelse return false);
    if (!isOptionalTypeNode(type_node, tags, datas)) return false;
    if (query.resolveIdentifierBinding(target) != full.ast.mut_token + 1) return false;
    const initializer = @intFromEnum(full.ast.init_node.unwrap() orelse return false);
    return isDefinitelyNonNullExpression(tree, initializer, type_context, tags, datas);
}

fn isOptionalTypeNode(
    type_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    var node = type_node;
    for (0..8) |_| {
        if (node >= tags.len) return false;
        switch (tags[node]) {
            .optional_type => return true,
            .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
            else => return false,
        }
    }
    return false;
}

/// Every way out of one statement leaves the storage non-null: a branch join
/// whose arms are each a definite non-null write or an exit that never reaches
/// the code after the statement, and whose condition itself leaves the storage
/// alone. An arm that fills the storage on only some path proves nothing, and
/// an `if` with no alternative proves only what its own condition implies on
/// the branch that falls through to the code after the statement.
fn branchJoinProvesNonNull(
    query: *const QueryContext,
    statement: u32,
    target: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    depth: u8,
) bool {
    if (depth > 8 or statement >= tags.len) return false;
    if (tags[statement] != .@"if" and tags[statement] != .if_simple) return false;
    const full = query.tree.fullIf(@enumFromInt(statement)) orelse return false;
    const cond = @intFromEnum(full.ast.cond_expr);
    if (statementMayMutateStorage(query, cond, target, tags, datas, block, type_context)) return false;
    if (!armProvesNonNull(query, @intFromEnum(full.ast.then_expr), target, type_context, tags, datas, block, depth + 1)) return false;
    // Without an alternative the code after the statement is reached only when
    // the condition was false, so the condition decides there — and it decides
    // on the branch that did *not* see the null.
    const else_expr = full.ast.else_expr.unwrap() orelse
        return conditionImpliesNullnessOnFalse(query, cond, target, false);
    return armProvesNonNull(query, @intFromEnum(else_expr), target, type_context, tags, datas, block, depth + 1);
}

fn armProvesNonNull(
    query: *const QueryContext,
    node: u32,
    target: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    depth: u8,
) bool {
    if (depth > 8 or node >= tags.len) return false;
    const tree = query.tree;
    switch (tags[node]) {
        // A return never reaches the statement after the join. A bare `break`
        // leaves the enclosing loop or switch, which the join is inside of
        // only when that construct sits between here and the guarded
        // statement, and a labeled or `continue` transfer can land back on
        // code that skipped this arm entirely.
        .@"return" => return true,
        .@"break" => return datas[node].opt_token_and_opt_node[0] == .none,
        .@"if", .if_simple => return branchJoinProvesNonNull(query, node, target, type_context, tags, datas, block, depth + 1),
        .block, .block_semicolon, .block_two, .block_two_semicolon => {
            var inline_statements: [2]u32 = undefined;
            const statements = ast_walk.getBlockStatements(tree, node, &inline_statements) orelse return false;
            var fact = false;
            for (statements) |statement| {
                if (statement >= tags.len) continue;
                if (branchSchedulesPendingDefer(query, statement, target, tags, datas, node, type_context)) return false;
                switch (tags[statement]) {
                    .@"return" => return true,
                    .@"break" => {
                        if (datas[statement].opt_token_and_opt_node[0] == .none) return true;
                    },
                    .@"if", .if_simple => {
                        fact = branchJoinProvesNonNull(query, statement, target, type_context, tags, datas, block, depth + 1);
                        continue;
                    },
                    else => {},
                }
                if (tags[statement] == .assign) {
                    const pair = datas[statement].node_and_node;
                    if (sameVariable(query, @intFromEnum(pair[0]), target)) {
                        fact = isDefinitelyNonNullExpression(tree, @intFromEnum(pair[1]), type_context, tags, datas);
                        continue;
                    }
                }
                if (statementMayMutateStorage(query, statement, target, tags, datas, block, type_context)) fact = false;
            }
            return fact;
        },
        else => return false,
    }
}

pub fn isGuardedByEarlyExit(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    // Find the containing block (could be loop body or function body)
    var node = unwrap_node;
    var block_node: ?u32 = null;
    var depth: u32 = 0;

    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;

        if (tags[parent] == .block or tags[parent] == .block_two or
            tags[parent] == .block_semicolon or tags[parent] == .block_two_semicolon)
        {
            block_node = parent;
            break;
        }
        node = parent;
    }

    const block = block_node orelse return false;

    // Scan the block for early exit pattern.
    return scanBlockForEarlyExit(
        query,
        block,
        unwrap_node,
        unwrapped_var,
        type_context,
        tags,
        datas,
        main_tokens,
        token_starts,
    );
}

pub fn isGuardedBySwitchNullCase(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    // Find the containing block (could be loop body or function body)
    var node = unwrap_node;
    var block_node: ?u32 = null;
    var depth: u32 = 0;

    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;

        if (tags[parent] == .block or tags[parent] == .block_two or
            tags[parent] == .block_semicolon or tags[parent] == .block_two_semicolon)
        {
            block_node = parent;
            break;
        }
        node = parent;
    }

    const block = block_node orelse return false;

    return scanBlockForSwitchNullCase(
        query,
        block,
        unwrap_node,
        unwrapped_var,
        type_context,
        tags,
        datas,
        main_tokens,
        token_starts,
    );
}

fn scanBlockForEarlyExit(
    query: *const QueryContext,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
) bool {
    const tree = query.tree;
    if (block >= tags.len) return false;

    // Get the position of the unwrap node.
    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    // Get statements from the block.
    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;
    var fact = false;

    // A condition whose true branch exits leaves the false-branch facts in
    // force.  Use the full boolean expression, not only a direct comparison:
    // `if (x == null or other_is_invalid) return; x.?` is safe.
    for (statements) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) continue;
        if (statementMayMutateStorage(query, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
            continue;
        }

        if (tags[stmt] != .@"if" and tags[stmt] != .if_simple) continue;
        const full = tree.fullIf(@enumFromInt(stmt)) orelse continue;
        const cond = @intFromEnum(full.ast.cond_expr);
        const then_expr = @intFromEnum(full.ast.then_expr);
        if (isEarlyExitExpr(tree, then_expr, tags, datas) and
            conditionImpliesNullnessOnFalse(query, cond, unwrapped_var, false))
        {
            fact = true;
        }
    }

    return fact;
}

fn scanBlockForSwitchNullCase(
    query: *const QueryContext,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
) bool {
    const tree = query.tree;
    if (block >= tags.len) return false;

    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;
    var fact = false;

    for (statements) |stmt| {
        if (stmt >= tags.len) continue;
        if (stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) continue;
        if (statementMayMutateStorage(query, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
            continue;
        }

        if (tags[stmt] != .@"switch" and tags[stmt] != .switch_comma) continue;

        const full_switch = tree.switchFull(@enumFromInt(stmt));
        const cond = @intFromEnum(full_switch.ast.condition);
        if (!sameVariable(query, cond, unwrapped_var)) continue;

        if (switchHasNullCaseEarlyExit(tree, stmt, tags, datas)) {
            fact = true;
        }
    }

    return fact;
}

fn switchHasNullCaseEarlyExit(
    tree: *const std.zig.Ast,
    switch_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const full_switch = tree.switchFull(@enumFromInt(switch_node));
    for (full_switch.ast.cases) |case_node| {
        const full_case = tree.fullSwitchCase(case_node) orelse continue;
        if (!caseHasNullValue(tree, full_case)) continue;

        const target_expr = @intFromEnum(full_case.ast.target_expr);
        if (isEarlyExitExpr(tree, target_expr, tags, datas)) {
            return true;
        }
    }

    return false;
}

fn caseHasNullValue(
    tree: *const std.zig.Ast,
    full_case: std.zig.Ast.full.SwitchCase,
) bool {
    for (full_case.ast.values) |value| {
        if (isNullIdentifier(tree, @intFromEnum(value))) {
            return true;
        }
    }
    return false;
}

fn isEarlyExitExpr(
    tree: *const std.zig.Ast,
    node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len) return false;

    switch (tags[node]) {
        .@"continue", .@"break", .@"return" => return true,
        .block, .block_semicolon, .block_two, .block_two_semicolon => {
            var inline_statements: [2]u32 = undefined;
            const statements = ast_walk.getBlockStatements(tree, node, &inline_statements) orelse return false;
            for (statements) |statement| {
                if (isEarlyExitExpr(tree, statement, tags, datas)) return true;
            }
            return false;
        },
        .@"if", .if_simple => {
            const full = tree.fullIf(@enumFromInt(node)) orelse return false;
            const else_node = full.ast.else_expr.unwrap() orelse return false;
            return isEarlyExitExpr(tree, @intFromEnum(full.ast.then_expr), tags, datas) and
                isEarlyExitExpr(tree, @intFromEnum(else_node), tags, datas);
        },
        else => return false,
    }
}

pub fn isGuardedByPriorAssignment(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    var boundary = unwrap_node;
    var current = unwrap_node;
    var depth: u32 = 0;
    while (depth < 64) : (depth += 1) {
        const block = findContainingBlock(tree, current, parent_map, tags) orelse return false;
        // A failed proof in a nested block must not be replaced by an outer
        // assignment when that block already wrote or escaped the target.
        if (boundary != unwrap_node and statementMayMutateStorageBefore(
            query,
            boundary,
            unwrapped_var,
            tags,
            datas,
            block,
            unwrap_node,
            type_context,
        )) return false;
        if (scanBlockForPriorAssignment(
            query,
            block,
            boundary,
            unwrapped_var,
            type_context,
            tags,
            datas,
            main_tokens,
            token_starts,
        )) return true;

        boundary = block;
        current = block;
    }
    return false;
}

pub fn isGuardedByPriorUnwrap(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    var node = unwrap_node;
    var block_node: ?u32 = null;
    var depth: u32 = 0;
    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;
        if (tags[parent] == .block or tags[parent] == .block_two or
            tags[parent] == .block_semicolon or tags[parent] == .block_two_semicolon)
        {
            block_node = parent;
            break;
        }
        node = parent;
    }

    const block = block_node orelse return false;
    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;
    var fact = false;

    for (statements) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;
        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) break;

        // `stmt` can be the very statement that holds the unwrap: only its main
        // token has to precede the unwrap's. A call, a write, or an operand
        // that reaches past the unwrap is evaluated after it, so this keeps
        // exactly the effects that really happen first.
        if (statementMayMutateStorageBefore(query, stmt, unwrapped_var, tags, datas, block, unwrap_node, type_context)) {
            fact = false;
            continue;
        }
        if (statementHasPriorUnwrap(query, stmt, unwrap_node, unwrapped_var, unwrap_pos, tags, datas)) {
            fact = true;
        }
    }
    return fact;
}

fn scanBlockForPriorAssignment(
    query: *const QueryContext,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
) bool {
    const tree = query.tree;
    if (block >= tags.len or unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;
    var fact = false;

    for (statements) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;
        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) break;

        if (tags[stmt] == .assign and query.lastToken(stmt) < main_tokens[unwrap_node]) {
            const pair = datas[stmt].node_and_node;
            const lhs = @intFromEnum(pair[0]);
            const rhs = @intFromEnum(pair[1]);
            if (sameVariable(query, lhs, unwrapped_var)) {
                // A constructor call is read through its own declared result
                // type, so `owner.resource = try Resource(u8).init(v);` is a
                // proof a written `error{Invalid}!@This()` makes and an
                // optional one does not.
                fact = isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas) or
                    constructorResultProvesNonNull(query, rhs);
                continue;
            }
            if (storageFieldsAreDisjoint(query, lhs, unwrapped_var, type_context)) {
                if (statementMayMutateStorageBefore(query, rhs, unwrapped_var, tags, datas, block, unwrap_node, type_context))
                    fact = false;
                continue;
            }
        }

        if (statementMayMutateStorageBefore(query, stmt, unwrapped_var, tags, datas, block, unwrap_node, type_context)) {
            fact = false;
        }
    }
    return fact;
}

/// The value a completed call leaves behind. `try` unwinds before its
/// statement finishes, and a `catch` handler that itself leaves means the
/// stored value is still the call's own result.
fn constructorResultProvesNonNull(query: *const QueryContext, expr: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var node = expr;
    for (0..4) |_| {
        if (node >= tags.len) return false;
        switch (tags[node]) {
            .@"try" => node = @intFromEnum(datas[node].node),
            .@"catch" => {
                const handler = @intFromEnum(datas[node].node_and_node[1]);
                if (!handlerPreventsCompletion(tree, handler, tags, datas)) return false;
                node = @intFromEnum(datas[node].node_and_node[0]);
            },
            .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
            else => return isFactoryConstructorCall(query, node),
        }
    }
    return false;
}

/// `Resource(u8).init(value)`: the receiver calls a function this file
/// declares to return `type`, and the member it names is declared in the
/// container that factory literally returns. The member's own declared result
/// type is the reading, so a same-spelled constructor elsewhere, a factory that
/// computes its type instead of returning one, and a receiver that is not a
/// factory call all keep the diagnostic.
fn isFactoryConstructorCall(query: *const QueryContext, call_node: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (call_node >= tags.len or !call_resolver.isCallNode(tags[call_node])) return false;
    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(call_node)) orelse return false;
    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return false;
    const access = datas[callee].node_and_token;
    const member_name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));

    const receiver = @intFromEnum(access[0]);
    if (receiver >= tags.len or !call_resolver.isCallNode(tags[receiver])) return false;
    var receiver_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const factory_call = tree.fullCall(&receiver_buffer, @enumFromInt(receiver)) orelse return false;
    const factory_name = @intFromEnum(factory_call.ast.fn_expr);
    if (factory_name >= tags.len or tags[factory_name] != .identifier) return false;

    const container = typeFactoryContainer(query, factory_name) orelse return false;
    const proto = containerMemberProto(tree, container, member_name) orelse return false;
    const result = protoReturnTypeNode(tree, proto) orelse return false;
    return declaredResultExcludesNull(tree, container, result, tags, datas);
}

/// The container a `fn Name(...) type` factory in this file returns. The name
/// has to belong to exactly one declaration in the file, so no local can
/// shadow the factory; the factory has to name `type` as its result and
/// `return` the container itself.
fn typeFactoryContainer(query: *const QueryContext, factory_name: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (factory_name >= tags.len) return null;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(tree.nodeMainToken(@enumFromInt(factory_name))));

    var factory_decl: ?u32 = null;
    for (query.lexical.namedCandidates(name)) |candidate| {
        if (candidate.kind != .function) return null;
        const fn_decl = query.lexical.enclosingFunction(candidate.name_token) orelse return null;
        if (factory_decl != null and factory_decl.? != fn_decl) return null;
        factory_decl = fn_decl;
    }
    const fn_decl = factory_decl orelse return null;
    if (fn_decl >= tags.len or tags[fn_decl] != .fn_decl) return null;

    const proto = @intFromEnum(datas[fn_decl].node_and_node[0]);
    const result = protoReturnTypeNode(tree, proto) orelse return null;
    if (!typeNodeIsTypeKeyword(tree, result, tags)) return null;
    return returnedContainer(tree, @intFromEnum(datas[fn_decl].node_and_node[1]), tags, datas);
}

/// `type` is a keyword the tree spells as a plain identifier.
fn typeNodeIsTypeKeyword(
    tree: *const std.zig.Ast,
    type_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
) bool {
    if (type_node >= tags.len or tags[type_node] != .identifier) return false;
    const token = tree.nodeMainToken(@enumFromInt(type_node));
    if (token >= tree.tokens.len) return false;
    return std.mem.eql(u8, tree.tokenSlice(token), "type");
}

/// The container a factory body returns directly. A factory that assembles its
/// type from a call, a field or a parameter, or whose body returns from more
/// than one place, is not read.
fn returnedContainer(
    tree: *const std.zig.Ast,
    body: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) ?u32 {
    if (body >= tags.len) return null;
    if (tags[body] != .block and tags[body] != .block_semicolon and
        tags[body] != .block_two and tags[body] != .block_two_semicolon) return null;

    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, body, &inline_statements) orelse return null;
    if (statements.len != 1) return null;
    const statement = statements[0];
    if (statement >= tags.len or tags[statement] != .@"return") return null;
    const operand = @intFromEnum(datas[statement].opt_node.unwrap() orelse return null);
    if (operand >= tags.len or !call_resolver.isContainerTag(tags[operand])) return null;
    return operand;
}

/// The prototype of a container member function, so a member written
/// `pub fn init(...) ... {}` reads the same as a bare `fn init(...);`.
fn containerMemberProto(tree: *const std.zig.Ast, container: u32, member_name: []const u8) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (container >= tags.len) return null;
    var buffer: [2]std.zig.Ast.Node.Index = undefined;
    const decl = tree.fullContainerDecl(&buffer, @enumFromInt(container)) orelse return null;
    for (decl.ast.members) |member| {
        const member_node = @intFromEnum(member);
        if (member_node >= tags.len) continue;
        if (tags[member_node] != .fn_decl and !isFnProtoTag(tags[member_node])) continue;
        if (protoNames(tree, member_node, member_name)) return member_node;
    }
    return null;
}

fn isFnProtoTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi => true,
        else => false,
    };
}

fn fullProto(
    tree: *const std.zig.Ast,
    node: u32,
    buffer: *[1]std.zig.Ast.Node.Index,
) ?std.zig.Ast.full.FnProto {
    if (node >= tree.nodes.len) return null;
    const tags = tree.nodes.items(.tag);
    return switch (tags[node]) {
        .fn_proto => tree.fnProto(@enumFromInt(node)),
        .fn_proto_simple => tree.fnProtoSimple(buffer, @enumFromInt(node)),
        .fn_proto_one => tree.fnProtoOne(buffer, @enumFromInt(node)),
        .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(node)),
        .fn_decl => blk: {
            const proto = @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]);
            break :blk fullProto(tree, proto, buffer);
        },
        else => null,
    };
}

fn protoNames(tree: *const std.zig.Ast, proto_node: u32, member_name: []const u8) bool {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = fullProto(tree, proto_node, &buffer) orelse return false;
    const name_token = proto.name_token orelse return false;
    if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return false;
    return std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), member_name);
}

fn protoReturnTypeNode(tree: *const std.zig.Ast, proto_node: u32) ?u32 {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = fullProto(tree, proto_node, &buffer) orelse return null;
    const return_type = proto.ast.return_type.unwrap() orelse return null;
    return @intFromEnum(return_type);
}

/// Can the declared result of a constructor hold `null`? Only an optional
/// can, so peeling the error union a `try` unwraps is enough to read the
/// verdict. The payload forms accepted are the ones whose value cannot be an
/// optional: `@This()`, whose factory is already known to return the struct or
/// union `container` declares, a container this file declares, and an inline
/// struct or union. A type parameter, a builtin or anything else is unknown.
fn declaredResultExcludesNull(
    tree: *const std.zig.Ast,
    container: u32,
    result: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (container >= tags.len) return false;
    var node = result;
    for (0..8) |_| {
        if (node >= tags.len) return false;
        switch (tags[node]) {
            .optional_type => return false,
            .error_union => node = @intFromEnum(datas[node].node_and_node[1]),
            .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                const token = tree.nodes.items(.main_token)[node];
                if (token >= tree.tokens.len or tree.tokenTag(token) != .builtin) return false;
                if (!std.mem.eql(u8, tree.tokenSlice(token), "@This")) return false;
                return call_resolver.isContainerTag(tags[container]);
            },
            .identifier => return containerDeclForTypeName(tree, node, tags, datas) != null,
            else => return call_resolver.isContainerTag(tags[node]),
        }
    }
    return false;
}

pub fn isDefinitelyNonNullExpression(
    tree: *const std.zig.Ast,
    node: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len) return false;
    if (isOrelseWithEarlyExit(node, tags, datas)) return true;

    switch (tags[node]) {
        .number_literal,
        .string_literal,
        .multiline_string_literal,
        .char_literal,
        .enum_literal,
        .array_init,
        .array_init_comma,
        .array_init_one,
        .array_init_one_comma,
        .array_init_dot,
        .array_init_dot_comma,
        .array_init_dot_two,
        .array_init_dot_two_comma,
        .struct_init,
        .struct_init_comma,
        .struct_init_one,
        .struct_init_one_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        => return true,
        .identifier => return !isNullIdentifier(tree, node) and typeInfoProvesNonNull(type_context, node),
        .@"orelse" => {
            const fallback = @intFromEnum(datas[node].node_and_node[1]);
            return isEarlyExitNode(fallback, tags) or
                isDefinitelyNonNullExpression(tree, fallback, type_context, tags, datas);
        },
        .@"try", .@"catch" => {
            // The wrapper's own resolved type is the value the code after it
            // receives, and `try` has already peeled the error union off it:
            // the operand's type is still `!T`, which proves nothing, while
            // the wrapper's is `T`.
            if (typeInfoProvesNonNull(type_context, node)) return true;
            const operand = completionOperand(tree, node, tags, datas) orelse return false;
            return isDefinitelyNonNullExpression(tree, operand, type_context, tags, datas);
        },
        else => return typeInfoProvesNonNull(type_context, node),
    }
}

/// The value a `try` or `catch` wrapper hands to the code after it, when
/// arriving there means the wrapper's operand completed and the statement
/// around it therefore stored that operand.
///
/// `try` leaves the function before the statement finishes, so the
/// assignment always ran. `catch` runs a handler instead, and that handler
/// supplies the value the statement stores; the assignment only performed
/// the operand when the handler leaves the enclosing scope. `orelse` keeps
/// the operand's own nullability and `errdefer` is not an expression, so
/// neither is peeled here.
fn completionOperand(
    tree: *const std.zig.Ast,
    node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) ?u32 {
    if (node >= tags.len) return null;
    switch (tags[node]) {
        .@"try" => return @intFromEnum(datas[node].node),
        .@"catch" => {
            const handler = @intFromEnum(datas[node].node_and_node[1]);
            if (!handlerPreventsCompletion(tree, handler, tags, datas)) return null;
            return @intFromEnum(datas[node].node_and_node[0]);
        },
        else => return null,
    }
}

/// Does a `catch` handler keep its statement from finishing? Only then did the
/// statement store the operand's value rather than the handler's.
///
/// `return` and `unreachable` always do, and a bare `break`/`continue` leaves
/// the construct that encloses the statement. A *labeled* `break` does not:
/// `catch |err| blk: { record(err); break :blk value; }` ends the handler's
/// own block and supplies `value` as the statement's result, so the operand's
/// value never reaches the field. An empty block handler completes too, so it
/// proves nothing.
pub fn handlerPreventsCompletion(
    tree: *const std.zig.Ast,
    node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len) return false;
    switch (tags[node]) {
        .@"return", .unreachable_literal => return true,
        .@"break", .@"continue" => return datas[node].opt_token_and_opt_node[0] == .none,
        .block, .block_semicolon, .block_two, .block_two_semicolon => {
            var inline_statements: [2]u32 = undefined;
            const statements = ast_walk.getBlockStatements(tree, node, &inline_statements) orelse
                return false;
            if (statements.len == 0) return false;
            for (statements) |statement| {
                if (!handlerPreventsCompletion(tree, statement, tags, datas)) return false;
            }
            return true;
        },
        .@"if", .if_simple => {
            const full = tree.fullIf(@enumFromInt(node)) orelse return false;
            const else_node = @intFromEnum(full.ast.else_expr.unwrap() orelse return false);
            return handlerPreventsCompletion(tree, @intFromEnum(full.ast.then_expr), tags, datas) and
                handlerPreventsCompletion(tree, else_node, tags, datas);
        },
        else => return false,
    }
}

/// Does the resolved type of `node` exclude `null`? A type that could not be
/// read, an optional, and a *still-wrapped* error union all prove nothing: a
/// `try`/`catch` expression carries the payload of its error union, but its
/// operand node is typed with the error union itself.
fn typeInfoProvesNonNull(type_context: ?*TypeContext, node: u32) bool {
    const ctx = type_context orelse return false;
    const info = ctx.getExpressionTypeStrict(node) orelse return false;
    return switch (info.kind) {
        .unknown, .optional, .error_union => false,
        else => true,
    };
}

fn isEarlyExitNode(node: u32, tags: []const std.zig.Ast.Node.Tag) bool {
    if (node >= tags.len) return false;
    return switch (tags[node]) {
        .@"return", .@"break", .@"continue", .error_value => true,
        else => false,
    };
}

fn isOrelseWithEarlyExit(
    node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len or tags[node] != .@"orelse") return false;
    return isEarlyExitNode(@intFromEnum(datas[node].node_and_node[1]), tags);
}

fn statementHasPriorUnwrap(
    query: *const QueryContext,
    statement: u32,
    target_unwrap: u32,
    unwrapped_var: u32,
    limit_pos: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const tree = query.tree;
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);
    return hasUnconditionalPriorUnwrap(
        query,
        statement,
        target_unwrap,
        unwrapped_var,
        limit_pos,
        tags,
        datas,
        main_tokens,
        token_starts,
        0,
    );
}

fn hasUnconditionalPriorUnwrap(
    query: *const QueryContext,
    node: u32,
    target_unwrap: u32,
    unwrapped_var: u32,
    limit_pos: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
    depth: u32,
) bool {
    const tree = query.tree;
    if (node == 0 or node == target_unwrap or depth >= 64) return false;
    if (node >= tags.len or node >= main_tokens.len) return false;
    if (main_tokens[node] >= token_starts.len or token_starts[main_tokens[node]] >= limit_pos) return false;

    switch (tags[node]) {
        .unwrap_optional => {
            const operand = @intFromEnum(datas[node].node_and_token[0]);
            if (sameVariable(query, operand, unwrapped_var)) return true;
            return hasUnconditionalPriorUnwrap(
                query,
                operand,
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .grouped_expression, .field_access => {
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(datas[node].node_and_token[0]),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .address_of, .deref, .@"try", .bool_not, .negation, .bit_not, .negation_wrap => {
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(datas[node].node),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .@"orelse", .@"catch", .bool_and, .bool_or => {
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(datas[node].node_and_node[0]),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .@"if", .if_simple => {
            const full = tree.fullIf(@enumFromInt(node)) orelse return false;
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(full.ast.cond_expr),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .@"while", .while_simple, .while_cont => {
            const full = tree.fullWhile(@enumFromInt(node)) orelse return false;
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(full.ast.cond_expr),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .@"for", .for_simple => {
            const full = tree.fullFor(@enumFromInt(node)) orelse return false;
            for (full.ast.inputs) |input| {
                if (hasUnconditionalPriorUnwrap(
                    query,
                    @intFromEnum(input),
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                )) return true;
            }
            return false;
        },
        .@"switch", .switch_comma => {
            const full = tree.switchFull(@enumFromInt(node));
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(full.ast.condition),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .simple_var_decl, .local_var_decl, .global_var_decl, .aligned_var_decl => {
            const full = tree.fullVarDecl(@enumFromInt(node)) orelse return false;
            const init = full.ast.init_node.unwrap() orelse return false;
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(init),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .assign => {
            const pair = datas[node].node_and_node;
            if (hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(pair[0]),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            )) return true;
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(pair[1]),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .assign_destructure => {
            const full = tree.assignDestructure(@enumFromInt(node));
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(full.ast.value_expr),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .call, .call_comma, .call_one, .call_one_comma => {
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const full = tree.fullCall(&call_buf, @enumFromInt(node)) orelse return false;
            if (hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(full.ast.fn_expr),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            )) return true;
            for (full.ast.params) |param| {
                if (hasUnconditionalPriorUnwrap(
                    query,
                    @intFromEnum(param),
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                )) return true;
            }
            return false;
        },
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            var builtin_buf: [2]std.zig.Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&builtin_buf, @enumFromInt(node)) orelse return false;
            for (params) |param| {
                if (hasUnconditionalPriorUnwrap(
                    query,
                    @intFromEnum(param),
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                )) return true;
            }
            return false;
        },
        .array_init,
        .array_init_comma,
        .array_init_one,
        .array_init_one_comma,
        .array_init_dot,
        .array_init_dot_comma,
        .array_init_dot_two,
        .array_init_dot_two_comma,
        => {
            var array_buf: [2]std.zig.Ast.Node.Index = undefined;
            const array_init = tree.fullArrayInit(&array_buf, @enumFromInt(node)) orelse return false;
            for (array_init.ast.elements) |element| {
                if (hasUnconditionalPriorUnwrap(
                    query,
                    @intFromEnum(element),
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                )) return true;
            }
            return false;
        },
        .struct_init,
        .struct_init_comma,
        .struct_init_one,
        .struct_init_one_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        => {
            var struct_buf: [2]std.zig.Ast.Node.Index = undefined;
            const struct_init = tree.fullStructInit(&struct_buf, @enumFromInt(node)) orelse return false;
            for (struct_init.ast.fields) |field| {
                if (hasUnconditionalPriorUnwrap(
                    query,
                    @intFromEnum(field),
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                )) return true;
            }
            return false;
        },
        .slice, .slice_open, .slice_sentinel => {
            const slice = tree.fullSlice(@enumFromInt(node)) orelse return false;
            if (hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(slice.ast.sliced),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            )) return true;
            if (hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(slice.ast.start),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            )) return true;
            if (slice.ast.end.unwrap()) |end_node| {
                if (hasUnconditionalPriorUnwrap(
                    query,
                    @intFromEnum(end_node),
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                )) return true;
            }
            return false;
        },
        .array_access => {
            const pair = datas[node].node_and_node;
            if (hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(pair[0]),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            )) return true;
            return hasUnconditionalPriorUnwrap(
                query,
                @intFromEnum(pair[1]),
                target_unwrap,
                unwrapped_var,
                limit_pos,
                tags,
                datas,
                main_tokens,
                token_starts,
                depth + 1,
            );
        },
        .block, .block_semicolon => {
            const extra = datas[node].extra_range;
            const start = @intFromEnum(extra.start);
            const end = @intFromEnum(extra.end);
            for (start..end) |index| {
                if (hasUnconditionalPriorUnwrap(
                    query,
                    tree.extra_data[index],
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                )) return true;
            }
            return false;
        },
        else => {
            if (isStrictBinaryTag(tags[node])) {
                const pair = datas[node].node_and_node;
                if (hasUnconditionalPriorUnwrap(
                    query,
                    @intFromEnum(pair[0]),
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                )) return true;
                return hasUnconditionalPriorUnwrap(
                    query,
                    @intFromEnum(pair[1]),
                    target_unwrap,
                    unwrapped_var,
                    limit_pos,
                    tags,
                    datas,
                    main_tokens,
                    token_starts,
                    depth + 1,
                );
            }
            return false;
        },
    }
}

fn isStrictBinaryTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .bang_equal,
        .equal_equal,
        .less_than,
        .greater_than,
        .less_or_equal,
        .greater_or_equal,
        .merge_error_sets,
        .mul,
        .div,
        .mod,
        .array_mult,
        .mul_wrap,
        .mul_sat,
        .add,
        .sub,
        .array_cat,
        .add_wrap,
        .sub_wrap,
        .add_sat,
        .shl,
        .shl_sat,
        .shr,
        .bit_and,
        .bit_xor,
        .bit_or,
        .switch_range,
        => true,
        else => false,
    };
}

/// A `defer`/`errdefer` reached as a direct statement of `block` only runs when
/// that block's own scope exits. The unwrap this scan guards lives in a later
/// statement of the same block, so the scope cannot have exited yet: the
/// unwinding that would run the body can only begin after the statement holding
/// the unwrap has returned. A defer reached through any other node belongs to
/// an inner scope whose exit may already have happened on the path to the
/// unwrap, so it keeps invalidating the fact.
fn deferredBodyHasNotRun(
    tree: *const std.zig.Ast,
    statement: u32,
    block: u32,
    tags: []const std.zig.Ast.Node.Tag,
) bool {
    if (statement >= tags.len or block >= tags.len) return false;
    if (tags[statement] != .@"defer" and tags[statement] != .@"errdefer") return false;
    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;
    for (statements) |candidate| {
        if (candidate == statement) return true;
    }
    return false;
}

/// When a `defer`/`errdefer` reached while scanning a statement can still be
/// pending at the guarded statement.
const DeferredTiming = enum {
    /// The scan walks statements of the scope that holds the guarded statement,
    /// so a body registered there cannot have run yet.
    scope_open,
    /// The scan walks statements of a scope that already exited before the
    /// guarded statement, so every body it registered has run by then.
    scope_exited,
};

pub fn statementMayMutateStorage(
    query: *const QueryContext,
    statement: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    type_context: ?*TypeContext,
) bool {
    return storageWriteReachable(query, statement, target, tags, datas, block, null, .scope_open, type_context);
}

/// Mutation analysis for a statement of a scope that already exited before the
/// guarded statement, so a `defer` registered by one of its direct statements
/// runs before the guarded statement instead of after it.
fn statementMayMutateStorageAfterScopeExit(
    query: *const QueryContext,
    statement: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    type_context: ?*TypeContext,
) bool {
    return storageWriteReachable(query, statement, target, tags, datas, block, null, .scope_exited, type_context);
}

fn statementMayMutateStorageBefore(
    query: *const QueryContext,
    statement: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    before_node: ?u32,
    type_context: ?*TypeContext,
) bool {
    return storageWriteReachable(query, statement, target, tags, datas, block, before_node, .scope_open, type_context);
}

fn storageWriteReachable(
    query: *const QueryContext,
    statement: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    before_node: ?u32,
    deferred_timing: DeferredTiming,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    if (deferred_timing == .scope_open and deferredBodyHasNotRun(tree, statement, block, tags)) return false;
    const Visitor = struct {
        query: *const QueryContext,
        target: u32,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        block: u32,
        before_token: ?u32,
        type_context: ?*TypeContext,
        found: bool = false,
        stop: bool = false,

        const Self = @This();

        pub fn visit(self: *Self, _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
            if (self.before_token) |before| {
                if (self.query.firstToken(node) >= before) return;
                // Operands are evaluated left to right, so a node that reaches
                // past the target owns an operand the target's own evaluation
                // follows: its write lands, and its call runs, only after that
                // operand. It is therefore no storage effect before the
                // unwrap, while the operands ahead of the target still are
                // one. Descending keeps those, where pruning the whole node
                // hid a mutation ordered ahead of the unwrap inside it.
                if (self.query.lastToken(node) >= before) return;
            }
            if (isAssignmentTag(tag)) {
                if (tag == .assign_destructure) {
                    const full = self.query.tree.assignDestructure(@enumFromInt(node));
                    for (full.ast.variables) |variable| {
                        if (storageWriteMayAffect(
                            self.query,
                            @intFromEnum(variable),
                            self.target,
                            self.block,
                            self.type_context,
                        )) {
                            self.found = true;
                            self.stop = true;
                            return;
                        }
                    }
                } else {
                    const lhs = @intFromEnum(self.datas[node].node_and_node[0]);
                    if (storageWriteMayAffect(self.query, lhs, self.target, self.block, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                        return;
                    }
                }
            }
            switch (tag) {
                .call, .call_comma, .call_one, .call_one_comma => {
                    if (callMayMutateStorage(self.query, node, self.target, self.tags, self.datas, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                    }
                },
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (builtinCallMayMutateStorage(self.query, node, self.target, self.tags, self.datas, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                    }
                },
                else => {},
            }
        }
    };

    var visitor = Visitor{
        .query = query,
        .target = target,
        .tags = tags,
        .datas = datas,
        .block = block,
        .before_token = if (before_node) |node| tree.nodes.items(.main_token)[node] else null,
        .type_context = type_context,
    };
    ast_walk.walk(Visitor, tree, statement, &visitor) catch return true;
    return visitor.found;
}
fn isAssignmentTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .assign,
        .assign_destructure,
        .assign_mul,
        .assign_div,
        .assign_mod,
        .assign_add,
        .assign_sub,
        .assign_shl,
        .assign_shl_sat,
        .assign_shr,
        .assign_bit_and,
        .assign_bit_xor,
        .assign_bit_or,
        .assign_mul_wrap,
        .assign_add_wrap,
        .assign_sub_wrap,
        .assign_mul_sat,
        .assign_add_sat,
        .assign_sub_sat,
        => true,
        else => false,
    };
}

fn storageFieldsAreDisjoint(query: *const QueryContext, lhs: u32, target: u32, type_context: ?*TypeContext) bool {
    const tree = query.tree;
    const ctx = type_context orelse return false;
    if (tree.nodeTag(@enumFromInt(lhs)) != .field_access or
        tree.nodeTag(@enumFromInt(target)) != .field_access)
        return false;
    const left = tree.nodeData(@enumFromInt(lhs)).node_and_token;
    const right = tree.nodeData(@enumFromInt(target)).node_and_token;
    if (std.mem.eql(u8, tree.tokenSlice(left[1]), tree.tokenSlice(right[1]))) return false;
    return sameVariable(query, @intFromEnum(left[0]), @intFromEnum(right[0])) and
        ctx.isStructExpression(@intFromEnum(left[0]));
}

fn storageWriteMayAffect(query: *const QueryContext, lhs: u32, target: u32, block: u32, type_context: ?*TypeContext) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (lhs >= tags.len) return true;
    // Rebinding a pointer alias changes its local slot, not the object it
    // previously designated. The target changes only when its own root moves.
    if (tags[lhs] == .identifier) return storageRootMatches(query, lhs, target);
    if (storageFieldsAreDisjoint(query, lhs, target, type_context)) return false;
    if (storageRootsMayAlias(query, lhs, target, type_context)) return true;
    // A value copy owns new bytes for the members it holds by value, but a
    // member whose declared type is a pointer still designates what the
    // original designated.
    if (copiedMemberMayReach(query, lhs, target, type_context)) return true;
    // A place that only rewrites the value one local slot holds reaches nothing
    // else, so once the roots are known to be apart it cannot reach the target.
    if (writeStaysInLocalSlot(query, lhs, target, type_context)) return false;
    return switch (tags[lhs]) {
        .deref, .address_of, .field_access, .array_access => !localSlotHasNoAliases(query, target, block, type_context),
        else => true,
    };
}

fn localSlotHasNoAliases(query: *const QueryContext, target: u32, block: u32, type_context: ?*TypeContext) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (target >= tags.len or block >= tags.len) return false;
    var root = target;
    for (0..16) |_| {
        if (tags[root] != .field_access) break;
        const base = @intFromEnum(tree.nodeData(@enumFromInt(root)).node_and_token[0]);
        const ctx = type_context orelse return false;
        const info = ctx.getExpressionTypeStrict(base) orelse return false;
        if (info.kind != .@"struct") return false;
        root = base;
    }
    if (tags[root] != .identifier) return false;
    const binding = query.resolveIdentifierBinding(root) orelse return false;
    if (binding == 0) return false;
    const declaration_tag = tree.tokenTag(binding - 1);
    if (declaration_tag != .keyword_var and declaration_tag != .keyword_const) return false;
    const function = query.lexical.enclosingFunction(binding) orelse return false;
    const reference = tree.nodeMainToken(@enumFromInt(target));
    if (query.lexical.enclosingFunction(reference) != function) return false;
    if (query.lexical.enclosingFunction(query.firstToken(block)) != function) return false;
    const function_start = query.firstToken(function);

    for (tags, 0..) |tag, index| {
        switch (tag) {
            .@"asm",
            .asm_simple,
            .address_of,
            .call,
            .call_comma,
            .call_one,
            .call_one_comma,
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => {},
            else => continue,
        }
        const node: std.zig.Ast.Node.Index = @enumFromInt(index);
        const start = query.firstToken(@intCast(index));
        if (start < function_start or start >= reference) continue;
        if (tag == .@"asm" or tag == .asm_simple) return false;
        if (start <= binding) continue;
        if (tag == .address_of and storageRootsMayAlias(query, @intFromEnum(tree.nodeData(node).node), target, type_context)) return false;
        if (call_resolver.isCallNode(tag)) {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node) orelse return false;
            const callee = call.ast.fn_expr;
            if (tree.nodeTag(callee) == .field_access and
                storageRootsMayAlias(query, @intFromEnum(tree.nodeData(callee).node_and_token[0]), target, type_context))
                return false;
        }
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&buffer, node) orelse return false;
                for (params) |param| {
                    if (storageRootsMayAlias(query, @intFromEnum(param), target, type_context)) return false;
                }
            },
            else => {},
        }
    }
    return true;
}

/// Where the storage a place expression designates actually lives. A local
/// slot owns the bytes of the value it holds; a pointer held in one only
/// reaches memory the slot does not own.
const SlotStorage = enum { in_slot, in_slot_array, behind_pointer, unknown };

/// True when the write rewrites nothing but the value one function-local slot
/// holds, and the guarded storage is not somewhere inside that slot. Two such
/// slots never overlap, so once `storageRootsMayAlias` has ruled the roots
/// apart the write cannot reach the target: `out.len` rewrites the header the
/// parameter owns, and so does `sink.len` after `var sink = out;`. A place that
/// leaves the slot keeps the conservative answer: `out[0]` reaches the memory
/// the header points at, and `p.*` and `holder.state.value` dereference a
/// pointer the slot only carries.
fn writeStaysInLocalSlot(query: *const QueryContext, lhs: u32, target: u32, type_context: ?*TypeContext) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var node = lhs;
    for (0..16) |_| {
        if (node >= tags.len) return false;
        switch (tags[node]) {
            .field_access => {
                const base = @intFromEnum(datas[node].node_and_token[0]);
                if (slotStorage(query, base, type_context) != .in_slot) return false;
                node = base;
            },
            .array_access => {
                // An element of an array is part of the slot that holds it; an
                // element of a slice or through a pointer is not.
                const base = @intFromEnum(datas[node].node_and_node[0]);
                if (slotStorage(query, base, type_context) != .in_slot_array) return false;
                node = base;
            },
            .identifier => return slotIsOutsideTarget(query, node, lhs, target, type_context),
            else => return false,
        }
    }
    return false;
}

/// Does a write spelled through `lhs` reach memory the slot holding its root
/// does not own? The mirror of `writeStaysInLocalSlot`: a member the root holds
/// by value is part of that slot, so rewriting it reaches nothing else, while a
/// pointer or a slice member carries the original's storage into the slot.
fn writesOutsideLocalSlot(query: *const QueryContext, lhs: u32, type_context: ?*TypeContext) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var node = lhs;
    for (0..16) |_| {
        if (node >= tags.len) return false;
        switch (tags[node]) {
            .field_access => {
                const base = @intFromEnum(datas[node].node_and_token[0]);
                if (slotStorage(query, base, type_context) != .in_slot) return true;
                node = base;
            },
            .array_access => {
                // An element of an array is part of the slot that holds it; an
                // element of a slice or through a pointer is not.
                const base = @intFromEnum(datas[node].node_and_node[0]);
                if (slotStorage(query, base, type_context) != .in_slot_array) return true;
                node = base;
            },
            .identifier => return false,
            else => return false,
        }
    }
    return false;
}

/// The member names a place expression walks, and the root identifier they
/// hang off. The walk starts at the place and climbs to the root, so the names
/// are recorded leaf-first: `names[len - 1]` is the member adjacent to the
/// root and `names[0]` the deepest one. Two paths that name the same storage
/// therefore agree entry by entry, which is what the comparisons below use.
const MemberPath = struct {
    root: u32 = 0,
    len: usize = 0,
    names: [8][]const u8 = undefined,

    fn slice(self: *const MemberPath) []const []const u8 {
        return self.names[0..self.len];
    }
};

/// A spelling this file cannot reduce to an identifier plus member reads — an
/// element index, a dereference, a call — carries no comparable path.
fn storageMemberPath(query: *const QueryContext, node: u32, out: *MemberPath) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    out.len = 0;
    var current = node;
    var depth: usize = 0;
    while (depth < 16) : (depth += 1) {
        if (current >= tags.len) return false;
        switch (tags[current]) {
            .identifier => {
                out.root = current;
                return true;
            },
            .field_access => {
                if (out.len == out.names.len) return false;
                out.names[out.len] = import_resolver.normalizeIdentifier(tree.tokenSlice(datas[current].node_and_token[1]));
                out.len += 1;
                current = @intFromEnum(datas[current].node_and_token[0]);
            },
            .grouped_expression, .unwrap_optional => current = @intFromEnum(datas[current].node_and_token[0]),
            else => return false,
        }
    }
    return false;
}

/// Does a write through `lhs` reach the storage `target` names because both
/// places walk through the same copy?
///
/// `const copy = self.flags;` gives the copy its own `Flags` bytes, so
/// `copy.note = false` reaches nothing the receiver holds. The pointer member
/// the copy carried still designates what the original pointed at, so
/// `copy.cell.value = null` writes the very `?u8` `self.flags.cell.value` names.
/// From the copy's origin the two paths have to line up, and the write has to
/// leave the copy's own bytes.
fn copiedMemberMayReach(
    query: *const QueryContext,
    lhs: u32,
    target: u32,
    type_context: ?*TypeContext,
) bool {
    if (!copiedPlaceReachesTarget(query, lhs, target)) return false;
    return writesOutsideLocalSlot(query, lhs, type_context);
}

/// Does a place spelled below a by-value copy designate the storage `target`
/// names, by walking into the guarded object the copy was taken from?
///
/// The copy has to have been written as a member read of the guarded object —
/// `const copy = box.flags;` — or as the guarded object itself, so both places
/// are read from one origin: the origin's own members followed by the ones
/// `place` walks. Read from the root outward, that combined path has to be the
/// path `target` walks or a prefix of it, because a place that stops short
/// holds the object the target lives inside: writing it rewrites the target,
/// and a call placed on it reaches it. A place that walks past the target names
/// storage the target does not hold, which reaches nothing the guard covers.
///
/// That is what tells `copy.cell`, walked out of `self.flags`, apart from
/// `table.inner`, a pointer member of a table that carries nothing the target
/// was taken from.
fn copiedPlaceReachesTarget(
    query: *const QueryContext,
    place: u32,
    target: u32,
) bool {
    var place_path: MemberPath = undefined;
    var target_path: MemberPath = undefined;
    if (!storageMemberPath(query, place, &place_path)) return false;
    if (!storageMemberPath(query, target, &target_path)) return false;
    const place_members = place_path.slice();
    if (place_members.len == 0) return false;
    const target_binding = query.resolveIdentifierBinding(target_path.root) orelse return false;
    if (query.resolveIdentifierBinding(place_path.root) == target_binding) return false;

    const origin = bindingInitializerNode(query, place_path.root) orelse return false;
    var origin_path: MemberPath = undefined;
    if (!storageMemberPath(query, origin, &origin_path)) return false;
    if (query.resolveIdentifierBinding(origin_path.root) != target_binding) return false;

    // Leaf-first, the combined path reads as the members the place walks and
    // then the origin's own, because those are the deeper ones. It has to
    // start the guarded path, so the share begins where the place's deepest
    // member and the origin's deepest member meet.
    const target_members = target_path.slice();
    if (origin_path.len + place_members.len > target_members.len) return false;
    const combined_start = target_members.len - (origin_path.len + place_members.len);
    const origin_members = origin_path.slice();
    for (place_members, 0..) |name, index| {
        if (!std.mem.eql(u8, name, target_members[combined_start + index])) return false;
    }
    for (origin_members, 0..) |name, index| {
        if (!std.mem.eql(u8, name, target_members[combined_start + place_members.len + index])) return false;
    }
    return true;
}

/// The root has to be a slot of the guarded function itself: a container-level
/// variable is shared storage every call can rewrite, and a binding of another
/// function is not the storage this write reaches.
fn rootIsFunctionLocalSlot(query: *const QueryContext, root: u32, target: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (target >= tags.len) return false;
    const binding = query.resolveIdentifierBinding(root) orelse return false;
    if (binding == 0) return false;
    const function = query.lexical.enclosingFunction(binding) orelse return false;
    if (query.lexical.enclosingFunction(tree.nodeMainToken(@enumFromInt(target))) != function) return false;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(tree.nodeMainToken(@enumFromInt(root))));
    for (query.lexical.namedCandidates(name)) |candidate| {
        if (candidate.name_token != binding or candidate.kind == .function) continue;
        return !candidate.is_root;
    }
    return false;
}

/// The slot is only out of reach when the target does not read it back. A view
/// taken from the slot before the write — `&cells[0]`, `cells[0..]`, a call
/// that returns one, or a rebinding that names the slot — designates the very
/// bytes this write rewrites, so reaching the target means going through the
/// slot after all. A by-value copy of the slot's content is a different object
/// and keeps the guard.
fn slotIsOutsideTarget(
    query: *const QueryContext,
    root: u32,
    lhs: u32,
    target: u32,
    type_context: ?*TypeContext,
) bool {
    if (!rootIsFunctionLocalSlot(query, root, target)) return false;
    if (slotAddressEscapes(query, root, lhs)) return false;
    const slot_binding = query.resolveIdentifierBinding(root) orelse return false;
    const target_root = storageRootIdentifier(query, target) orelse return false;
    return !bindingDerivedFrom(query, target_root, slot_binding, query.firstToken(lhs), type_context);
}

/// The slot has to be private to this function. Its address handed out before
/// the write — `&copy` in any argument, or an `@asm` block, which can reach
/// anything — leaves a pointer the checker never sees, and a callee that was
/// given both the slot and the guarded storage can make the two the same
/// object. A by-value copy of the slot is not an escape.
fn slotAddressEscapes(query: *const QueryContext, root: u32, lhs: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const binding = query.resolveIdentifierBinding(root) orelse return true;
    const window_end = query.firstToken(lhs);
    for (tags, 0..) |tag, index| {
        switch (tag) {
            .@"asm", .asm_simple, .address_of => {},
            else => continue,
        }
        const node: std.zig.Ast.Node.Index = @enumFromInt(index);
        const start = query.firstToken(@intCast(index));
        if (start < binding or start >= window_end) continue;
        if (tag == .address_of and
            !expressionMentionsBinding(query, @intFromEnum(tree.nodeData(node).node), binding)) continue;
        return true;
    }
    return false;
}

/// The storage the value of `expr` occupies. A declaration written in the
/// source decides it wherever one exists — a parameter, a typed `var`, or a
/// member read from its owner's own declaration — and an inferred `var` takes
/// the shape of the value it was initialised from.
fn slotStorage(query: *const QueryContext, expr: u32, type_context: ?*TypeContext) SlotStorage {
    return slotStorageWithin(query, expr, type_context, 0);
}

/// The same reading, following an initializer chain far enough to shape an
/// inferred `var`. A resolved type settles only what the declaration leaves
/// unread.
fn slotStorageWithin(query: *const QueryContext, expr: u32, type_context: ?*TypeContext, depth: u8) SlotStorage {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (expr >= tags.len or depth > 4) return .unknown;
    var written: SlotStorage = .unknown;
    switch (tags[expr]) {
        .identifier => {
            if (bindingTypeExprNode(query, expr)) |type_node| {
                written = typeNodeSlotStorage(query, tree, type_node);
            } else if (bindingInitializerNode(query, expr)) |initializer| {
                written = slotStorageWithin(query, initializer, type_context, depth + 1);
            }
        },
        .field_access => {
            if (fieldTypeNode(query, expr)) |type_node| written = typeNodeSlotStorage(query, tree, type_node);
        },
        .unwrap_optional => {
            written = removalSlotStorage(query, expr);
        },
        else => {},
    }
    // A declaration written in the source is the storage's own spelling; a
    // resolved type only settles what it leaves open.
    if (written != .unknown) return written;
    return resolvedSlotStorage(type_context, expr);
}

/// Where a verified removal leaves the value it hands back. `pop()` copies the
/// element out of the list into the caller's own slot, so a container or a
/// primitive leaves that slot owning the bytes it received, while a pointer
/// still designates what the list held.
fn removalSlotStorage(query: *const QueryContext, expr: u32) SlotStorage {
    const removal = removalCallIn(query, expr) orelse return .unknown;
    const receiver = removalCallReceiver(query, removal) orelse return .unknown;
    return if (removalElementDesignatesSharedStorage(query, receiver))
        .behind_pointer
    else
        .in_slot;
}

/// The value a `var` was initialised from, so an inferred type reads off the
/// expression that gave the slot its shape.
fn bindingInitializerNode(query: *const QueryContext, identifier: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (identifier >= tags.len or tags[identifier] != .identifier) return null;
    const binding = query.resolveIdentifierBinding(identifier) orelse return null;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(tree.nodeMainToken(@enumFromInt(identifier))));
    for (query.lexical.namedCandidates(name)) |candidate| {
        // A parameter is filled by its caller, never by an initializer here.
        if (candidate.name_token != binding or candidate.kind != .variable) continue;
        const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return null;
        return @intFromEnum(full.ast.init_node.unwrap() orelse return null);
    }
    return null;
}

/// The storage a written type node carries. `*T` designates memory the slot
/// does not own, `[]T` and `[N]T` own their bytes inside it, and a bare name
/// is read at the container this file declares it with, or at what that name
/// is itself a `const` for: `const Owned = OwnedCell;` carries the container
/// `OwnedCell` names, so a slot declared `Owned` owns the same bytes one
/// declared `OwnedCell` does. A name no spelling of this file settles stays
/// unknown, which is what leaves the question to the type context.
fn typeNodeSlotStorage(query: *const QueryContext, tree: *const std.zig.Ast, type_node: u32) SlotStorage {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var node = type_node;
    for (0..8) |_| {
        if (node >= tags.len) return .unknown;
        switch (tags[node]) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                const pointer = tree.fullPtrType(@enumFromInt(node)) orelse return .unknown;
                return if (pointer.size == .slice) .in_slot else .behind_pointer;
            },
            .slice, .slice_open, .slice_sentinel => return .in_slot,
            .array_type, .array_type_sentinel => return .in_slot_array,
            .optional_type => node = @intFromEnum(datas[node].node),
            .error_union => node = @intFromEnum(datas[node].node_and_node[1]),
            .grouped_expression, .@"comptime" => node = @intFromEnum(datas[node].node),
            .identifier => {
                // A name the file never spells out as a container may still be
                // an alias to a pointer, so it is read at what this file gives
                // the name before it stays unknown.
                if (containerDeclForTypeName(tree, node, tags, datas)) |_| return .in_slot;
                node = typeAliasInitializerNode(query, tree, node) orelse return .unknown;
            },
            .container_decl,
            .container_decl_trailing,
            .container_decl_two,
            .container_decl_two_trailing,
            .container_decl_arg,
            .container_decl_arg_trailing,
            .tagged_union,
            .tagged_union_trailing,
            .tagged_union_enum_tag,
            .tagged_union_enum_tag_trailing,
            .tagged_union_two,
            .tagged_union_two_trailing,
            => return .in_slot,
            else => return .unknown,
        }
    }
    return .unknown;
}

fn resolvedSlotStorage(type_context: ?*TypeContext, expr: u32) SlotStorage {
    const ctx = type_context orelse return .unknown;
    const info = ctx.getExpressionTypeStrict(expr) orelse return .unknown;
    return switch (info.kind) {
        .pointer => .behind_pointer,
        .slice => .in_slot,
        .array => .in_slot_array,
        .@"struct", .@"union", .@"enum" => .in_slot,
        else => .unknown,
    };
}

fn callMayMutateStorage(
    query: *const QueryContext,
    call_node: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
    const full = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return true;
    const callee = @intFromEnum(full.ast.fn_expr);
    if (callee >= tags.len) return true;

    if (tags[callee] == .field_access) {
        const receiver = @intFromEnum(datas[callee].node_and_token[0]);
        if (receiver >= tags.len) return true;
        if (tags[receiver] != .unwrap_optional) {
            // A call placed on a pointer- or slice-typed place reaches memory
            // the receiver's own slot does not own, so a by-value copy of that
            // slot does not make the call safe: `var copy = self.flags;
            // copy.cell.clear();` writes the pointee the guarded field also
            // names. A receiver that is one whole by-value slot —
            // `copy.clearRetainingCapacity()` — writes only that slot.
            if (storageRootsMayAlias(query, receiver, target, type_context) or
                receiverDesignatesSharedStorage(query, receiver, target)) return true;
        }
    }

    for (full.ast.params) |param| {
        if (argumentMayMutateStorage(query, @intFromEnum(param), target, tags, datas, type_context)) return true;
    }
    return targetMayBeGlobal(query, target);
}

/// Is the receiver a place whose own declared type designates memory outside the
/// slot that holds it, and does that memory hold what the target names? Only a
/// member read is such a place: one whole local or parameter is a slot, and a
/// field whose declared type is a value stays one. Reaching storage is not by
/// itself reaching the guarded field, so a member the target was not taken from
/// is ruled out as well — `table.inner.clear()` writes the `Leaf` the table
/// points at, and a `Leaf` holds no `State.cursor` for a guard to have read.
fn receiverDesignatesSharedStorage(
    query: *const QueryContext,
    receiver: u32,
    target: u32,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (receiver >= tags.len or tags[receiver] != .field_access) return false;
    // Whether the walk out of the copy reaches the guarded field at all is the
    // relation between the two paths, so it is settled before the member's own
    // declared type is read: that type only says where the walk lands.
    if (!copiedPlaceReachesTarget(query, receiver, target)) return false;
    const declared = fieldTypeNode(query, receiver) orelse return true;
    return memberTypeDesignatesSharedStorage(query, tree, declared, 0);
}

/// Does a written type node designate memory the slot carrying it does not own?
/// `*T` and `[]T` do; `?T` and `E!T` hand the question to the value they carry.
fn designatesStorageOutsideSlot(
    tree: *const std.zig.Ast,
    type_node: u32,
    depth: u8,
) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var node = type_node;
    for (0..8) |_| {
        if (depth > 8 or node >= tags.len) return false;
        switch (tags[node]) {
            .ptr_type,
            .ptr_type_aligned,
            .ptr_type_bit_range,
            .ptr_type_sentinel,
            .slice,
            .slice_open,
            .slice_sentinel,
            => return true,
            .optional_type => node = @intFromEnum(datas[node].node),
            .error_union => node = @intFromEnum(datas[node].node_and_node[1]),
            .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
            else => return false,
        }
    }
    return false;
}

/// Does a written type node designate memory the slot carrying it does not
/// own, with the names it is spelled through peeled away first? A name this
/// file gives its type with a `const` designates whatever that type
/// designates, so `cell: Ptr` written for `const Ptr = *Cell;`, and the
/// namespace member `handles.Ptr`, reach what `cell: *Cell` reaches. A name
/// given a container designates a value the slot owns, and a name nothing
/// here resolves may still name a pointer, so it keeps the conservative
/// reading.
fn memberTypeDesignatesSharedStorage(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    type_node: u32,
    depth: u8,
) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (depth > 4 or type_node >= tags.len) return true;
    if (designatesStorageOutsideSlot(tree, type_node, 0)) return true;
    switch (tags[type_node]) {
        .optional_type => return memberTypeDesignatesSharedStorage(
            query,
            tree,
            @intFromEnum(datas[type_node].node),
            depth + 1,
        ),
        .error_union => return memberTypeDesignatesSharedStorage(
            query,
            tree,
            @intFromEnum(datas[type_node].node_and_node[1]),
            depth + 1,
        ),
        .grouped_expression => return memberTypeDesignatesSharedStorage(
            query,
            tree,
            @intFromEnum(datas[type_node].node_and_token[0]),
            depth + 1,
        ),
        .identifier, .field_access => {
            if (typeAliasInitializerNode(query, tree, type_node)) |aliased| {
                return memberTypeDesignatesSharedStorage(query, tree, aliased, depth + 1);
            }
        },
        else => {},
    }
    return !isByValueTypeNode(query, tree, type_node, tags, datas, 0);
}

/// The type this file gives a name written in a type position, when a `const`
/// spells it out. The resolver only ever sees this file, so what it reports is
/// an index into `tree`.
fn typeAliasInitializerNode(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    type_node: u32,
) ?u32 {
    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    const alias = resolver.resolveTypeAliasNode(type_node) orelse return null;
    if (alias.file_index != 0) return null;
    return alias.node_index;
}

fn builtinCallMayMutateStorage(
    query: *const QueryContext,
    call_node: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    var builtin_buf: [2]std.zig.Ast.Node.Index = undefined;
    const params = tree.builtinCallParams(&builtin_buf, @enumFromInt(call_node)) orelse return true;
    for (params) |param| {
        if (argumentMayMutateStorage(query, @intFromEnum(param), target, tags, datas, type_context)) return true;
    }
    return targetMayBeGlobal(query, target);
}

// Unknown calls may mutate globals. This is invalidation only, not a name-based proof.
fn targetMayBeGlobal(query: *const QueryContext, target: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    var root = target;
    while (root < tags.len) {
        switch (tags[root]) {
            .grouped_expression, .unwrap_optional, .field_access => {
                root = @intFromEnum(datas[root].node_and_token[0]);
            },
            .deref, .address_of => root = @intFromEnum(datas[root].node),
            .array_access => root = @intFromEnum(datas[root].node_and_node[0]),
            else => break,
        }
    }
    if (root >= tags.len or tags[root] != .identifier or root >= main_tokens.len) return false;
    const root_name = tree.tokenSlice(main_tokens[root]);
    for (query.lexical.namedCandidates(import_resolver.normalizeIdentifier(root_name))) |candidate| {
        if (candidate.kind != .variable or !candidate.is_root) continue;
        if (std.mem.eql(u8, tree.tokenSlice(candidate.name_token), root_name)) return true;
    }
    return false;
}

fn argumentMayMutateStorage(
    query: *const QueryContext,
    node: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    if (node >= tags.len) return true;
    var argument = node;
    while (argument < tags.len) {
        switch (tags[argument]) {
            .grouped_expression, .unwrap_optional => {
                argument = @intFromEnum(datas[argument].node_and_token[0]);
            },
            .identifier => {
                if (!storageRootsMayAlias(query, argument, target, type_context)) return false;
                return argumentExpressionMayEscape(type_context, argument);
            },
            .address_of => {
                const pointee = @intFromEnum(datas[argument].node);
                if (storageFieldsAreDisjoint(query, pointee, target, type_context)) return false;
                return storageRootsMayAlias(query, argument, target, type_context);
            },
            .deref => return storageRootsMayAlias(query, argument, target, type_context),
            .array_access => {
                const base = @intFromEnum(datas[argument].node_and_node[0]);
                if (storageRootsMayAlias(query, base, target, type_context)) return true;
                argument = base;
            },
            .call, .call_comma, .call_one, .call_one_comma => {
                var call_buf: [1]std.zig.Ast.Node.Index = undefined;
                const full = tree.fullCall(&call_buf, @enumFromInt(argument)) orelse return true;
                const callee = @intFromEnum(full.ast.fn_expr);
                if (callee < tags.len and tags[callee] == .field_access) {
                    const receiver = @intFromEnum(datas[callee].node_and_token[0]);
                    if (storageRootsMayAlias(query, receiver, target, type_context)) return true;
                }
                for (full.ast.params) |param| {
                    if (argumentMayMutateStorage(query, @intFromEnum(param), target, tags, datas, type_context)) return true;
                }
                return false;
            },
            else => return false,
        }
    }
    return true;
}

fn argumentExpressionMayEscape(type_context: ?*TypeContext, node: u32) bool {
    const ctx = type_context orelse return true;
    var info = ctx.getExpressionTypeStrict(node) orelse return true;
    for (0..8) |_| {
        switch (info.kind) {
            .pointer, .slice => return true,
            .optional, .error_union => {
                info.kind = info.payload_kind orelse return true;
                info.payload_kind = null;
            },
            else => return false,
        }
    }
    return true;
}

fn storageRootMatches(query: *const QueryContext, node: u32, target: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= tags.len or target >= tags.len) return false;

    var left = node;
    var right = target;
    var depth: u32 = 0;
    while (left < tags.len and right < tags.len and depth < 32) : (depth += 1) {
        if (tags[left] == .grouped_expression) {
            left = @intFromEnum(datas[left].node_and_token[0]);
            continue;
        }
        if (tags[right] == .grouped_expression) {
            right = @intFromEnum(datas[right].node_and_token[0]);
            continue;
        }
        if (tags[left] == .unwrap_optional or tags[left] == .field_access) {
            left = @intFromEnum(datas[left].node_and_token[0]);
            continue;
        }
        if (tags[right] == .unwrap_optional or tags[right] == .field_access) {
            right = @intFromEnum(datas[right].node_and_token[0]);
            continue;
        }
        if (tags[left] == .deref or tags[left] == .address_of) {
            left = @intFromEnum(datas[left].node);
            continue;
        }
        if (tags[right] == .deref or tags[right] == .address_of) {
            right = @intFromEnum(datas[right].node);
            continue;
        }
        if (tags[left] == .array_access) {
            left = @intFromEnum(datas[left].node_and_node[0]);
            continue;
        }
        if (tags[right] == .array_access) {
            right = @intFromEnum(datas[right].node_and_node[0]);
            continue;
        }
        if (tags[left] != .identifier or tags[right] != .identifier) return false;
        if (left >= main_tokens.len or right >= main_tokens.len) return false;
        return sameIdentifierBinding(query, left, right);
    }
    return false;
}

fn sameIdentifierBinding(query: *const QueryContext, left: u32, right: u32) bool {
    const left_binding = query.resolveIdentifierBinding(left) orelse return false;
    const right_binding = query.resolveIdentifierBinding(right) orelse return false;
    return left_binding == right_binding;
}

/// `storageRootMatches` plus the locals that reach the target root through a
/// pointer view: a pointer copy such as `const alias = holder;`, however many
/// hops or rebindings deep, still designates the same object, so a different
/// name never proves non-aliasing.
fn storageRootsMayAlias(
    query: *const QueryContext,
    node: u32,
    target: u32,
    type_context: ?*TypeContext,
) bool {
    if (storageRootMatches(query, node, target)) return true;
    const left = storageRootIdentifier(query, node) orelse return false;
    const right = storageRootIdentifier(query, target) orelse return false;
    if (left == right) return true;
    const target_binding = query.resolveIdentifierBinding(right) orelse return false;
    // Only initialisation that already reached the mutation under test can
    // have made the left binding designate the target object there. A
    // rebinding written between the mutation and the target site shapes the
    // target's own receiver, not the value the mutation read.
    return bindingDerivedFrom(query, left, target_binding, query.firstToken(node), type_context);
}

fn storageRootIdentifier(query: *const QueryContext, node: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var current = node;
    var depth: u32 = 0;
    while (depth < 32) : (depth += 1) {
        if (current >= tags.len) return null;
        switch (tags[current]) {
            .grouped_expression, .unwrap_optional, .field_access => current = @intFromEnum(datas[current].node_and_token[0]),
            .deref, .address_of => current = @intFromEnum(datas[current].node),
            .array_access => current = @intFromEnum(datas[current].node_and_node[0]),
            .identifier => return current,
            else => return null,
        }
    }
    return null;
}

/// A binding reaches the target object when one of the expressions that give
/// it a value re-reads an already known alias through a pointer view. Chains
/// are followed to a fixpoint and a rebinding counts like a declaration, so
/// `var p = holder; const q = p; const r = q;` and `alias = holder;` still
/// designate the same object, while a plain value copy (`const copy =
/// holder.list;`) initialises an independent one. Only initialisation
/// written before the use site counts. The discriminator is always the
/// alias's own initializer, never the target's type: `&root` shares the
/// object, a struct copy does not.
fn bindingDerivedFrom(
    query: *const QueryContext,
    node: u32,
    target_binding: u32,
    use_token: u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const binding = query.resolveIdentifierBinding(node) orelse return false;
    if (binding == target_binding) return true;

    // Bindings already known to designate the target object. Chains grow it
    // one hop at a time; more than the worklist holds is reported as aliasing
    // because claiming independence would hide a real mutation.
    var known: [32]u32 = undefined;
    var known_len: usize = 1;
    known[0] = target_binding;
    var next: usize = 0;
    while (next < known_len) : (next += 1) {
        const source = known[next];
        for (tags, 0..) |tag, index| {
            var destination: u32 = 0;
            var value_expr: u32 = 0;
            switch (tag) {
                .assign => {
                    value_expr = @intFromEnum(datas[index].node_and_node[1]);
                },
                else => {
                    if (!import_resolver.isVarDeclTag(tag)) continue;
                    const full = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
                    destination = full.ast.mut_token + 1;
                    value_expr = @intFromEnum(full.ast.init_node.unwrap() orelse {
                        // A declaration with no value at all still names the slot.
                        if (destination == binding) return true;
                        continue;
                    });
                },
            }
            // A declaration or rebinding written after the use site cannot
            // have shaped the value that site reads.
            if (query.firstToken(@intCast(index)) >= use_token) continue;
            if (value_expr == 0 or value_expr >= tags.len) continue;
            // A removal names the list, not the object it hands back, so the
            // spelling alone cannot carry the relation: what decides is the
            // element's own type and what the list was given beforehand.
            const removal = removalCallIn(query, value_expr);
            if (!expressionNamesBinding(query, value_expr, source) or
                !expressionMentionsBinding(query, value_expr, source))
            {
                if (removal == null) continue;
                if (!removalYieldsBinding(query, removal.?, source, use_token)) continue;
            }
            if (!initializerCarriesPointer(query, value_expr, type_context)) continue;
            if (destination == 0) {
                const lhs = @intFromEnum(datas[index].node_and_node[0]);
                if (lhs >= tags.len or tags[lhs] != .identifier) continue;
                destination = query.resolveIdentifierBinding(lhs) orelse continue;
            }
            if (destination == binding) return true;
            if (std.mem.indexOfScalar(u32, known[0..known_len], destination) == null) {
                if (known_len == known.len) return true;
                known[known_len] = destination;
                known_len += 1;
            }
        }
    }
    return false;
}

/// True when the new slot may still designate the object the target names.
/// `&root` and `root.*` always do, and a declared by-value copy never does. A
/// `.field_access` initializer is decided by the member's own declared type
/// alone: expression-type resolution cannot tell a pointer-typed field from a
/// value one, and a member whose type cannot be read stays a pointer view. An
/// unresolved (`.unknown`) expression type is no evidence either, so it keeps
/// the conservative reading.
fn initializerCarriesPointer(
    query: *const QueryContext,
    init: u32,
    type_context: ?*TypeContext,
) bool {
    const tags = query.tree.nodes.items(.tag);
    if (init >= tags.len) return true;
    switch (tags[init]) {
        .address_of, .deref => return true,
        .field_access => return !declaredByValueCopy(query, init),
        // `pop()` hands the removed element back by value, so unwrapping it
        // into a local slot copies the element out of the list. The element's
        // own declared type still decides: a `std.ArrayList(*Cell)` removal
        // hands back a pointer, and that slot designates what it names.
        .unwrap_optional => {
            const removal = @intFromEnum(query.tree.nodes.items(.data)[init].node_and_token[0]);
            if (!isRemovalResult(query, removal)) return true;
            const receiver = removalCallReceiver(query, removal) orelse return true;
            return removalElementDesignatesSharedStorage(query, receiver);
        },
        else => {},
    }
    if (declaredByValueCopy(query, init)) return false;
    const ctx = type_context orelse return true;
    var info = ctx.getExpressionTypeStrict(init) orelse return true;
    for (0..8) |_| {
        switch (info.kind) {
            .pointer, .slice => return true,
            .optional, .error_union => {
                info.kind = info.payload_kind orelse return true;
                info.payload_kind = null;
            },
            .unknown => return true,
            else => return false,
        }
    }
    return true;
}

/// The removal call an initializer reads through, when the expression is one.
fn removalCallIn(query: *const QueryContext, expr: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (expr >= tags.len or tags[expr] != .unwrap_optional) return null;
    const removal = @intFromEnum(tree.nodes.items(.data)[expr].node_and_token[0]);
    return if (isRemovalResult(query, removal)) removal else null;
}

/// A removal hands back one element of the list it read from, so the new slot
/// designates whatever that element designated. For the removed element to be
/// the object the guard named, the list has to have been given that object's
/// own address first: a call that stored `&object` — or the object itself — on
/// the very list the removal reads is the only way that can happen, and it has
/// to be written before the removal.
fn removalYieldsBinding(
    query: *const QueryContext,
    removal: u32,
    binding: u32,
    use_token: u32,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const list = removalCallReceiver(query, removal) orelse return false;
    const deadline = @min(use_token, query.firstToken(removal));
    var node: usize = 1;
    while (node < tags.len) : (node += 1) {
        if (!call_resolver.isCallNode(tags[node])) continue;
        if (query.firstToken(@intCast(node)) >= deadline) continue;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse continue;
        const callee = @intFromEnum(call.ast.fn_expr);
        if (callee >= tags.len or tags[callee] != .field_access) continue;
        const receiver = @intFromEnum(datas[callee].node_and_token[0]);
        if (!sameStoragePath(query, tree, receiver, list, tags, datas)) continue;
        for (call.ast.params) |param| {
            if (expressionDesignatesBinding(query, @intFromEnum(param), binding)) return true;
        }
    }
    return false;
}

/// Does `expr` hand the object the binding names to a callee? `&object` and
/// `object` both do; a value the binding holds by copy does not.
fn expressionDesignatesBinding(query: *const QueryContext, expr: u32, binding: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (expr >= tags.len) return false;
    switch (tags[expr]) {
        .identifier => return query.resolveIdentifierBinding(expr) == binding,
        .address_of => return expressionDesignatesBinding(
            query,
            @intFromEnum(tree.nodes.items(.data)[expr].node),
            binding,
        ),
        else => return false,
    }
}

/// True when the initializer's *declared* type owns the bytes it is copied
/// into, so the new slot is an independent object instead of a view on the
/// original one. A bare identifier is read through the declared type of the
/// binding it names, a `holder.field` access through the member's own
/// declared type.
fn declaredByValueCopy(query: *const QueryContext, expr: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (expr >= tags.len) return false;
    const declared = switch (tags[expr]) {
        .identifier => bindingTypeExprNode(query, expr) orelse return false,
        .field_access => fieldTypeNode(query, expr) orelse return false,
        else => return false,
    };
    return isByValueTypeNode(query, tree, declared, tags, tree.nodes.items(.data), 0);
}

/// A type this file can spell out, resolved far enough to tell a value from a
/// view: a struct, a union or an array owns its own bytes, and so does one of
/// those behind the optional and error-union layers, as does the verified
/// by-value `std` container. `*T` and `[]T` designate memory the slot does not
/// own, so a copy of one still reaches the original. Anything this file
/// cannot resolve keeps the conservative reading.
fn isByValueTypeNode(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    type_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    depth: u8,
) bool {
    if (type_node >= tags.len or depth > 8) return false;
    return switch (tags[type_node]) {
        // `*T` and `[]T` keep designating the original storage.
        .ptr_type,
        .ptr_type_aligned,
        .ptr_type_bit_range,
        .ptr_type_sentinel,
        .slice,
        .slice_open,
        .slice_sentinel,
        => false,
        // An array element lives inside the slot that holds the array, and a
        // struct or union member is part of the value that carries it.
        .array_type,
        .array_type_sentinel,
        .container_decl,
        .container_decl_trailing,
        .container_decl_two,
        .container_decl_two_trailing,
        .container_decl_arg,
        .container_decl_arg_trailing,
        .tagged_union,
        .tagged_union_trailing,
        .tagged_union_enum_tag,
        .tagged_union_enum_tag_trailing,
        .tagged_union_two,
        .tagged_union_two_trailing,
        => true,
        // `?T` and `E!T` carry the value itself; `(T)` wraps nothing new.
        .optional_type => isByValueTypeNode(query, tree, @intFromEnum(datas[type_node].node), tags, datas, depth + 1),
        .error_union => isByValueTypeNode(query, tree, @intFromEnum(datas[type_node].node_and_node[1]), tags, datas, depth + 1),
        .grouped_expression => isByValueTypeNode(query, tree, @intFromEnum(datas[type_node].node_and_token[0]), tags, datas, depth + 1),
        // A name is read through the container this file declares it with, and
        // through whatever that name is itself a `const` for: `const Owned =
        // OwnedCell;` carries the container `OwnedCell` names, so a slot
        // declared `Owned` owns the bytes one declared `OwnedCell` does and the
        // two spellings cannot disagree. An alias of a pointer, of a slice or
        // of a spelling this file cannot read reaches that spelling instead,
        // which keeps the reading it already had.
        .identifier => blk: {
            if (containerDeclForTypeName(tree, type_node, tags, datas) != null) break :blk true;
            const aliased = typeAliasInitializerNode(query, tree, type_node) orelse break :blk false;
            break :blk isByValueTypeNode(query, tree, aliased, tags, datas, depth + 1);
        },
        // `std.ArrayList(T)` is spelled as a call; any other call type is only
        // known through its verified import provenance.
        else => isVerifiedStdArrayListValueTypeNode(query, tree, type_node, tags, datas),
    };
}

fn expressionMentionsBinding(query: *const QueryContext, expression: u32, binding: u32) bool {
    const tree = query.tree;
    const Visitor = struct {
        query: *const QueryContext,
        binding: u32,
        found: bool = false,
        stop: bool = false,

        const Self = @This();

        pub fn visit(self: *Self, _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
            if (tag != .identifier) return;
            if (self.query.resolveIdentifierBinding(node) != self.binding) return;
            self.found = true;
            self.stop = true;
        }
    };

    var visitor = Visitor{ .query = query, .binding = binding };
    ast_walk.walk(Visitor, tree, expression, &visitor) catch return true;
    return visitor.found;
}

/// Cheap pre-filter for the exact resolution in `expressionMentionsBinding`:
/// the binding's own name has to occur in the expression's tokens, so the
/// unrelated declarations of a file cost one substring search each.
fn expressionNamesBinding(query: *const QueryContext, expression: u32, name_token: u32) bool {
    const tree = query.tree;
    if (expression >= tree.nodes.len or name_token >= tree.tokens.len) return true;
    const first = query.firstToken(expression);
    const last = query.lastToken(expression);
    if (first > last or last >= tree.tokens.len) return true;
    const starts = tree.tokens.items(.start);
    const bytes = tree.source[starts[first] .. starts[last] + tree.tokenSlice(last).len];
    return std.mem.indexOf(u8, bytes, tree.tokenSlice(name_token)) != null;
}

/// A call to a `self` method whose own body leaves `self.<field>` non-null
/// wherever it returns successfully, so reaching the statement after the call
/// carries that postcondition. The proof comes from the callee's declaration,
/// never from the method's name: a method that assigns the field on only one
/// branch, or not at all, proves nothing. It lasts until a later statement
/// writes the storage or passes it to a call that may.
pub fn isGuardedBySelfMethodPostcondition(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    fn_node: ids.AstNodeId,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    // First, check if the unwrapped variable is a field access on self (e.g., self.texture)
    if (unwrapped_var >= tags.len) return false;
    if (tags[unwrapped_var] != .field_access) return false;

    // Get the object being accessed and the field name
    const obj = @intFromEnum(datas[unwrapped_var].node_and_token[0]);
    const field_token = datas[unwrapped_var].node_and_token[1];
    const field_name = tree.tokenSlice(field_token);

    // Match the receiver by lexical declaration, not by the spelling `self`.
    if (!isSelfReceiver(query, obj, ids.astIndex(fn_node))) return false;

    // Find the containing block
    var node = unwrap_node;
    var block_node: ?u32 = null;
    var depth: u32 = 0;

    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;

        if (tags[parent] == .block or tags[parent] == .block_two or
            tags[parent] == .block_semicolon or tags[parent] == .block_two_semicolon)
        {
            block_node = parent;
            break;
        }
        node = parent;
    }

    const block = block_node orelse return false;

    // Scan for completed self method calls before the unwrap.
    return scanBlockForSelfMethodPostcondition(
        query,
        block,
        unwrap_node,
        unwrapped_var,
        field_name,
        type_context,
        tags,
        datas,
        main_tokens,
        token_starts,
        fn_node,
    );
}

/// The `self` method call a statement performs, when reaching the next
/// statement means the call completed. A bare `self.ensure();` always does,
/// `try self.ensure();` does because the error path leaves the function, and
/// `self.ensure() catch ...` does only when the handler itself leaves.
fn completedSelfMethodCall(
    query: *const QueryContext,
    statement: u32,
    fn_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) ?u32 {
    if (statement >= tags.len) return null;
    const operand: ?u32 = switch (tags[statement]) {
        .@"try" => @intFromEnum(datas[statement].node),
        .@"catch" => blk: {
            const handler = @intFromEnum(datas[statement].node_and_node[1]);
            if (!handlerPreventsCompletion(query.tree, handler, tags, datas)) break :blk null;
            break :blk @intFromEnum(datas[statement].node_and_node[0]);
        },
        .call, .call_comma, .call_one, .call_one_comma => statement,
        else => null,
    };
    const call_node = operand orelse return null;
    if (!isMethodCallOnSelf(query, call_node, tags, datas, fn_node)) return null;
    return call_node;
}

fn scanBlockForSelfMethodPostcondition(
    query: *const QueryContext,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    field_name: []const u8,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
    fn_node: ids.AstNodeId,
) bool {
    const tree = query.tree;
    if (block >= tags.len) return false;

    // Get position of the unwrap node.
    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    // A successful method guard remains valid only until a later storage write.
    var fact = false;
    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return false;

    for (statements) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) continue;
        if (isInSubtree(tree, stmt, unwrap_node)) {
            // The statement holding the unwrap completes no call of its own,
            // but what it evaluates ahead of the unwrap still runs first and
            // ends the fact an earlier call established.
            if (statementMayMutateStorageBefore(query, stmt, unwrapped_var, tags, datas, block, unwrap_node, type_context))
                fact = false;
            continue;
        }

        if (completedSelfMethodCall(query, stmt, ids.astIndex(fn_node), tags, datas)) |call_node| {
            if (methodAssignsToField(query, call_node, field_name, fn_node, type_context)) {
                fact = true;
                continue;
            }
        }

        if (statementMayMutateStorage(query, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
        }
    }
    return fact;
}

fn isMethodCallOnSelf(
    query: *const QueryContext,
    call_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    fn_node: u32,
) bool {
    const tree = query.tree;
    if (call_node >= tags.len or !call_utils.isCallNode(tags[call_node])) return false;

    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
    const full_call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return false;
    const callee = @intFromEnum(full_call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return false;

    const receiver = @intFromEnum(datas[callee].node_and_token[0]);
    return isSelfReceiver(query, receiver, fn_node);
}

fn isSelfReceiver(query: *const QueryContext, receiver: u32, fn_node: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (receiver >= tags.len or tags[receiver] != .identifier) return false;
    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    const receiver_decl = resolver.resolveDeclarationNode(receiver) orelse return false;
    const self_param = firstParameterNode(tree, fn_node) orelse return false;
    return receiver_decl == self_param;
}

fn firstParameterNode(tree: *const std.zig.Ast, fn_node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (fn_node >= tags.len) return null;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&buffer, @enumFromInt(fn_node)) orelse return null;
    if (proto.ast.params.len == 0) return null;
    return @intFromEnum(proto.ast.params[0]);
}

fn methodAssignsToField(
    query: *const QueryContext,
    call_node: u32,
    field_name: []const u8,
    fn_node: ids.AstNodeId,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (call_node >= tags.len or !call_utils.isCallNode(tags[call_node])) return false;

    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return false;
    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return false;
    const access = datas[callee].node_and_token;
    const receiver = @intFromEnum(access[0]);
    const method_name = tree.tokenSlice(access[1]);

    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    const receiver_type = resolver.resolveExprType(receiver) orelse return false;

    // Resolve the receiver type before matching a method.  A method name is
    // not a callable identity: same-spelled methods on another type cannot
    // establish this field's invariant.
    for (query.lexical.namedCandidates(import_resolver.normalizeIdentifier(method_name))) |candidate| {
        if (candidate.kind != .function) continue;
        const i = query.lexical.enclosingFunction(candidate.name_token) orelse continue;
        if (i == ids.astIndex(fn_node)) continue;

        const fn_proto_idx = candidate.node;
        if (fn_proto_idx >= tags.len) continue;
        var proto_buf: [1]std.zig.Ast.Node.Index = undefined;
        const proto = switch (tags[fn_proto_idx]) {
            .fn_proto => tree.fnProto(@enumFromInt(fn_proto_idx)),
            .fn_proto_simple => tree.fnProtoSimple(&proto_buf, @enumFromInt(fn_proto_idx)),
            .fn_proto_one => tree.fnProtoOne(&proto_buf, @enumFromInt(fn_proto_idx)),
            .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(fn_proto_idx)),
            else => null,
        } orelse continue;
        const name_token = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), method_name)) continue;
        if (proto.ast.params.len == 0) continue;

        const first_param = @intFromEnum(proto.ast.params[0]);
        const first_type = if (first_param < tags.len and import_resolver.isVarDeclTag(tags[first_param]))
            (tree.fullVarDecl(@enumFromInt(first_param)) orelse continue).ast.type_node.unwrap()
        else
            @as(?std.zig.Ast.Node.Index, @enumFromInt(first_param));
        const first_type_node = first_type orelse continue;
        const candidate_type = resolver.resolveTypeNode(@intFromEnum(first_type_node)) orelse continue;
        if (!call_resolver.resolvedTypesEqual(receiver_type, candidate_type)) continue;

        if (methodProvesFieldAtSuccessfulExit(
            query,
            @intCast(i),
            field_name,
            type_context,
            tags,
            datas,
        )) {
            return true;
        }
    }

    return false;
}

/// Is `self.field` non-null at every exit of `fn_decl` that the caller can
/// still be running after `self.method() catch ...`? A first assignment is not
/// that proof: the field can be left null by a later write, by a branch that
/// never assigns, by an early `return`, or by a `defer` body running while the
/// method's own scope exits. The caller only reaches the unwrap when the call
/// did not fail, so error-only exits — and the `errdefer` bodies that run on
/// exactly those exits — are outside the proof.
fn methodProvesFieldAtSuccessfulExit(
    query: *const QueryContext,
    fn_decl: u32,
    field_name: []const u8,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (fn_decl >= tags.len) return false;

    const body = @intFromEnum(datas[fn_decl].node_and_node[1]);
    if (body == 0 or body >= tags.len) return false;

    const field_node = findSelfFieldAccess(query, body, field_name, fn_decl, tags, datas) orelse
        return false;

    const proof = MethodExitProof{
        .query = query,
        .fn_decl = fn_decl,
        .field_name = field_name,
        .field_node = field_node,
        .type_context = type_context,
        .tags = tags,
        .datas = datas,
    };
    const result = proof.analyzeScope(body, false, false);
    return result.returns_proven and (!result.falls_through or result.fall_fact);
}

/// One representative `self.field` access from a method body. The storage and
/// identity helpers compare a root binding and a field name rather than node
/// identity, so a single representative compares every statement against it.
fn findSelfFieldAccess(
    query: *const QueryContext,
    root: u32,
    field_name: []const u8,
    fn_decl: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) ?u32 {
    const Visitor = struct {
        query: *const QueryContext,
        field_name: []const u8,
        fn_decl: u32,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        found: ?u32 = null,
        stop: bool = false,

        const Self = @This();

        pub fn visit(self: *Self, _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
            if (tag != .field_access) return;
            if (!isSelfFieldAccess(self.query, node, self.field_name, self.fn_decl, self.tags, self.datas)) {
                return;
            }
            self.found = node;
            self.stop = true;
        }
    };

    var visitor = Visitor{
        .query = query,
        .field_name = field_name,
        .fn_decl = fn_decl,
        .tags = tags,
        .datas = datas,
    };
    ast_walk.walk(Visitor, query.tree, root, &visitor) catch return null;
    return visitor.found;
}

/// Flow-sensitive proof that `self.field` is non-null wherever the caller can
/// still be running after the analysed method returned successfully. The entry
/// fact is "unknown": the field is non-null at an exit only because a
/// dominating write says so, never because of what it held when the method was
/// entered.
const MethodExitProof = struct {
    query: *const QueryContext,
    fn_decl: u32,
    field_name: []const u8,
    /// One representative `self.field` access from the body, used as the target
    /// of every storage comparison.
    field_node: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,

    /// What a node hands back to the scope that encloses it. A method return
    /// and a fallthrough into the next statement are different questions about
    /// the field, which is why both are reported instead of one combined flag.
    const ExitProof = struct {
        /// Every reachable successful method return under this node carries a
        /// proven non-null field. Vacuously true when the node contains no
        /// reachable successful method return at all.
        returns_proven: bool,
        /// Control can reach the end of the node.
        falls_through: bool,
        /// The field is proven non-null where control reaches the end.
        fall_fact: bool,

        /// The reading of a node this analysis cannot decode: it proves nothing
        /// and no fact reaches past it.
        const unproven = ExitProof{
            .returns_proven = false,
            .falls_through = true,
            .fall_fact = false,
        };
    };

    /// `pending` records that a scope enclosing this one already registered a
    /// `defer` body that may clobber the field. That body runs when control
    /// leaves the enclosing scope, so it is charged to a method return taken
    /// here and to nothing else: a nested scope that merely falls through does
    /// not run it, so an intermediate fact must never be poisoned by it.
    fn analyze(
        self: *const MethodExitProof,
        node: u32,
        entry_fact: bool,
        pending: bool,
        scope: u32,
    ) ExitProof {
        // The syntax tree is acyclic, so the descent always terminates. No
        // depth cap stands in for a proof it cannot make.
        if (node == 0 or node >= self.tags.len) return .unproven;

        switch (self.tags[node]) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                return self.analyzeScope(node, entry_fact, pending);
            },
            .@"if", .if_simple => {
                return self.analyzeIf(node, entry_fact, pending, scope);
            },
            .@"while", .while_simple, .while_cont => {
                return self.analyzeWhile(node, entry_fact, pending, scope);
            },
            .@"for", .for_simple => {
                return self.analyzeFor(node, entry_fact, pending, scope);
            },
            .@"switch", .switch_comma => {
                return self.analyzeSwitch(node, entry_fact, pending, scope);
            },
            .@"return" => {
                return self.analyzeReturn(node, entry_fact, pending, scope);
            },
            .@"break", .@"continue" => {
                // A labeled transfer targets a scope this analysis does not
                // track, so no fact survives it: `break :outer` can step over an
                // initializer the rest of the method reads.
                if (self.datas[node].opt_token_and_opt_node[0] != .none) return .unproven;
                // A bare one leaves the innermost loop or switch, not the
                // method. It is no method return, and it cannot fall through
                // either, so it neither hides a mutation nor revives a fact.
                return .{ .returns_proven = true, .falls_through = false, .fall_fact = false };
            },
            // `analyzeScope` owns the clobbering check for a `defer`/`errdefer`
            // statement; neither body has run at this point.
            .@"defer", .@"errdefer" => {
                return .{ .returns_proven = true, .falls_through = true, .fall_fact = entry_fact };
            },
            else => {},
        }

        // A direct write of a definitely non-null value is the only statement
        // that establishes the fact. Anything else either leaves the field
        // alone or destroys it, a write through an alias included.
        //
        // The right-hand side is evaluated before the write stores anything,
        // so a `catch`/`orelse` payload that leaves the method there hands
        // back the state this statement was entered with: it is charged the
        // entry fact, never the value the write would have established. Such
        // an exit is successful, so it is one this proof has to cover.
        if (self.tags[node] == .assign and self.assignsNonNullToField(node)) {
            return .{
                .returns_proven = self.payloadReturnsProven(node, entry_fact, pending, scope),
                .falls_through = true,
                .fall_fact = true,
            };
        }

        const clobbers = statementMayMutateStorage(
            self.query,
            node,
            self.field_node,
            self.tags,
            self.datas,
            scope,
            self.type_context,
        );
        const rest_fact = if (clobbers) false else entry_fact;
        return .{
            .returns_proven = self.payloadReturnsProven(node, rest_fact, pending, scope),
            .falls_through = true,
            .fall_fact = rest_fact,
        };
    }

    /// Folds the statements of one scope. `local_clobbered` records the `defer`
    /// bodies THIS scope registered: they run when it exits, so they are
    /// charged here and to any method return taken inside, while an inherited
    /// `pending` body belongs to an outer scope and is not.
    fn analyzeScope(
        self: *const MethodExitProof,
        block: u32,
        entry_fact: bool,
        pending: bool,
    ) ExitProof {
        var inline_statements: [2]u32 = undefined;
        const statements = ast_walk.getBlockStatements(self.query.tree, block, &inline_statements) orelse
            return .unproven;

        var fact = entry_fact;
        var local_clobbered = false;
        var returns_proven = true;

        for (statements) |statement| {
            if (statement >= self.tags.len) continue;

            switch (self.tags[statement]) {
                // A `defer` body runs when this scope exits, on every path that
                // leaves it, so once such a body may clobber the field no fact
                // this scope holds can reach the caller.
                .@"defer" => {
                    if (self.deferMayClobberField(statement, block)) local_clobbered = true;
                    continue;
                },
                // An `errdefer` body runs only when the scope exits with an
                // error, and no error exit reaches the caller's unwrap.
                .@"errdefer" => continue,
                else => {},
            }

            const proof = self.analyze(statement, fact, pending or local_clobbered, block);
            if (!proof.returns_proven) returns_proven = false;
            // A statement that cannot fall through leaves the scope outright,
            // so no successor is reachable from this path.
            if (!proof.falls_through) {
                return .{
                    .returns_proven = returns_proven,
                    .falls_through = false,
                    .fall_fact = false,
                };
            }
            fact = proof.fall_fact;
        }

        return .{
            .returns_proven = returns_proven,
            .falls_through = true,
            .fall_fact = fact and !local_clobbered,
        };
    }

    fn analyzeIf(
        self: *const MethodExitProof,
        node: u32,
        entry_fact: bool,
        pending: bool,
        scope: u32,
    ) ExitProof {
        const full = self.query.tree.fullIf(@enumFromInt(node)) orelse return .unproven;
        const cond = @intFromEnum(full.ast.cond_expr);

        // The condition runs before either branch, so whatever it does to the
        // field is charged before either branch's entry fact is derived.
        var cond_fact = entry_fact;
        if (self.mayMutateField(cond, scope)) cond_fact = false;
        // A null check on the field itself hands the fact to the branch that
        // does not see the null. That is what makes
        // `if (self.f == null) { self.f = ...; }` a proof even though the
        // field starts out unknown.
        const then_fact = cond_fact or conditionImpliesNotNull(self.query, cond, self.field_node);
        const else_fact = cond_fact or
            conditionImpliesNullnessOnFalse(self.query, cond, self.field_node, false);

        const then_proof = self.analyze(
            @intFromEnum(full.ast.then_expr),
            then_fact,
            pending,
            scope,
        );
        const else_proof = if (full.ast.else_expr.unwrap()) |else_node|
            self.analyze(@intFromEnum(else_node), else_fact, pending, scope)
        else
            ExitProof{ .returns_proven = true, .falls_through = true, .fall_fact = else_fact };

        return .{
            .returns_proven = then_proof.returns_proven and else_proof.returns_proven,
            .falls_through = then_proof.falls_through or else_proof.falls_through,
            // A branch that does not fall through adds no requirement to the
            // join, because it never reaches it.
            .fall_fact = (!then_proof.falls_through or then_proof.fall_fact) and
                (!else_proof.falls_through or else_proof.fall_fact),
        };
    }

    /// A loop can only keep the fact, never establish it: its body runs zero or
    /// more times, under a condition, a continuation and an `else` continuation
    /// that may each write the field, and both the body and that `else`
    /// continuation may leave the method as well.
    fn analyzeWhile(
        self: *const MethodExitProof,
        node: u32,
        entry_fact: bool,
        pending: bool,
        scope: u32,
    ) ExitProof {
        const full = self.query.tree.fullWhile(@enumFromInt(node)) orelse return .unproven;
        const body = self.analyze(@intFromEnum(full.ast.then_expr), entry_fact, pending, scope);

        var returns_proven = body.returns_proven;
        var preserved = entry_fact and body.falls_through and body.fall_fact;
        if (self.mayMutateField(@intFromEnum(full.ast.cond_expr), scope)) preserved = false;
        if (full.ast.cont_expr.unwrap()) |cont| {
            if (self.mayMutateField(@intFromEnum(cont), scope)) preserved = false;
        }
        // The `else` continuation runs once the condition turns false, even when
        // the body never ran at all, so it may both clobber and return.
        if (full.ast.else_expr.unwrap()) |else_node| {
            if (!self.analyze(@intFromEnum(else_node), entry_fact, pending, scope).returns_proven) {
                returns_proven = false;
            }
            if (self.mayMutateField(@intFromEnum(else_node), scope)) preserved = false;
        }

        return .{
            .returns_proven = returns_proven,
            .falls_through = true,
            .fall_fact = preserved,
        };
    }

    fn analyzeFor(
        self: *const MethodExitProof,
        node: u32,
        entry_fact: bool,
        pending: bool,
        scope: u32,
    ) ExitProof {
        const full = self.query.tree.fullFor(@enumFromInt(node)) orelse return .unproven;
        const body = self.analyze(@intFromEnum(full.ast.then_expr), entry_fact, pending, scope);

        var returns_proven = body.returns_proven;
        var preserved = entry_fact and body.falls_through and body.fall_fact;
        for (full.ast.inputs) |input| {
            if (self.mayMutateField(@intFromEnum(input), scope)) preserved = false;
        }
        // The `else` continuation runs once the inputs are exhausted, even when
        // the body never ran at all, so it may both clobber and return.
        if (full.ast.else_expr.unwrap()) |else_node| {
            if (!self.analyze(@intFromEnum(else_node), entry_fact, pending, scope).returns_proven) {
                returns_proven = false;
            }
            if (self.mayMutateField(@intFromEnum(else_node), scope)) preserved = false;
        }

        return .{
            .returns_proven = returns_proven,
            .falls_through = true,
            .fall_fact = preserved,
        };
    }

    /// A valid Zig switch is exhaustive. Join every reachable prong without
    /// adding a fictitious path that skips all of them.
    fn analyzeSwitch(
        self: *const MethodExitProof,
        node: u32,
        entry_fact: bool,
        pending: bool,
        scope: u32,
    ) ExitProof {
        const full = self.query.tree.switchFull(@enumFromInt(node));
        if (full.ast.cases.len == 0) return .unproven;
        var cond_fact = entry_fact;
        if (self.mayMutateField(@intFromEnum(full.ast.condition), scope)) cond_fact = false;

        var returns_proven = true;
        var fall_fact = true;
        var falls_through = false;

        for (full.ast.cases) |case_node| {
            const full_case = self.query.tree.fullSwitchCase(case_node) orelse return .unproven;
            const proof = self.analyze(
                @intFromEnum(full_case.ast.target_expr),
                cond_fact,
                pending,
                scope,
            );
            if (!proof.returns_proven) returns_proven = false;
            falls_through = falls_through or proof.falls_through;
            if (proof.falls_through and !proof.fall_fact) fall_fact = false;
        }

        return .{
            .returns_proven = returns_proven,
            .falls_through = falls_through,
            .fall_fact = fall_fact,
        };
    }

    /// `return error.X` leaves the callee only through the caller's `catch`
    /// handler, which cannot reach the guarded unwrap, so it is excluded from
    /// the proof. Every other `return` is a successful exit the caller does
    /// observe: it runs the `defer` bodies of every scope it leaves, and its
    /// operand is evaluated first, so `return self.reset();` clears the field
    /// before the caller ever sees it.
    fn analyzeReturn(
        self: *const MethodExitProof,
        node: u32,
        entry_fact: bool,
        pending: bool,
        scope: u32,
    ) ExitProof {
        const successful = ExitProof{
            .returns_proven = entry_fact and !pending,
            .falls_through = false,
            .fall_fact = false,
        };
        const operand = self.datas[node].opt_node.unwrap() orelse return successful;
        const value = @intFromEnum(operand);
        if (value >= self.tags.len) return successful;
        if (self.tags[value] == .error_value) {
            return .{ .returns_proven = true, .falls_through = false, .fall_fact = false };
        }
        if (self.mayMutateField(value, scope)) {
            return .{ .returns_proven = false, .falls_through = false, .fall_fact = false };
        }
        return successful;
    }

    /// A `catch`/`orelse` payload that leaves the method is a successful method
    /// return the statement's own fallthrough fact does not describe, and it
    /// hides inside any wrapper: `f() catch return;`,
    /// `const n = f() orelse return;`, `x = f() catch return;`. The payload
    /// runs once its operand has been evaluated, so its entry fact is whatever
    /// state the operand left behind.
    fn payloadReturnsProven(
        self: *const MethodExitProof,
        statement: u32,
        fact: bool,
        pending: bool,
        scope: u32,
    ) bool {
        const Visitor = struct {
            proof: *const MethodExitProof,
            fact: bool,
            pending: bool,
            scope: u32,
            returns_proven: bool = true,
            stop: bool = false,

            const Self = @This();

            pub fn visit(collector: *Self, tree: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
                if (tag != .@"catch" and tag != .@"orelse") return;
                const payload = @intFromEnum(collector.proof.datas[node].node_and_node[1]);
                if (payload == 0 or payload >= collector.proof.tags.len) return;
                if (!isEarlyExitExpr(tree, payload, collector.proof.tags, collector.proof.datas)) return;
                const proof = collector.proof.analyze(payload, collector.fact, collector.pending, collector.scope);
                if (!proof.returns_proven) {
                    collector.returns_proven = false;
                    collector.stop = true;
                }
            }
        };

        var visitor = Visitor{ .proof = self, .fact = fact, .pending = pending, .scope = scope };
        ast_walk.walk(Visitor, self.query.tree, statement, &visitor) catch return false;
        return visitor.returns_proven;
    }

    fn mayMutateField(self: *const MethodExitProof, node: u32, scope: u32) bool {
        if (node == 0 or node >= self.tags.len) return true;
        return statementMayMutateStorage(
            self.query,
            node,
            self.field_node,
            self.tags,
            self.datas,
            scope,
            self.type_context,
        );
    }

    /// True when a `defer` body may clobber the field once the scope that
    /// registered it exits.
    fn deferMayClobberField(self: *const MethodExitProof, statement: u32, block: u32) bool {
        return statementMayMutateStorageAfterScopeExit(
            self.query,
            statement,
            self.field_node,
            self.tags,
            self.datas,
            block,
            self.type_context,
        );
    }

    /// True for `self.field = <definitely non-null>`, the one write that
    /// establishes the fact. A compound assignment keeps the old value and is
    /// therefore only ever a possible clobber.
    fn assignsNonNullToField(self: *const MethodExitProof, node: u32) bool {
        const pair = self.datas[node].node_and_node;
        const lhs = @intFromEnum(pair[0]);
        if (!isSelfFieldAccess(self.query, lhs, self.field_name, self.fn_decl, self.tags, self.datas)) {
            return false;
        }
        const rhs = @intFromEnum(pair[1]);
        return isDefinitelyNonNullExpression(
            self.query.tree,
            rhs,
            self.type_context,
            self.tags,
            self.datas,
        );
    }
};

fn isSelfFieldAccess(
    query: *const QueryContext,
    node: u32,
    field_name: []const u8,
    fn_decl: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const tree = query.tree;
    if (node >= tags.len or tags[node] != .field_access) return false;

    const obj = @intFromEnum(datas[node].node_and_token[0]);
    const field_token = datas[node].node_and_token[1];
    if (!isSelfReceiver(query, obj, fn_decl)) return false;
    return std.mem.eql(u8, tree.tokenSlice(field_token), field_name);
}

pub fn isGuardedByLabeledBlockInvariant(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    const if_node = findEnclosingIfForUnwrap(tree, unwrap_node, parent_map, tags) orelse return false;
    const full_if = tree.fullIf(@enumFromInt(if_node)) orelse return false;
    const cond_node = @intFromEnum(full_if.ast.cond_expr);
    if (cond_node >= tags.len or tags[cond_node] != .identifier) return false;

    const cond_token = main_tokens[cond_node];
    const cond_name = tree.tokenSlice(cond_token);

    const block_node = findContainingBlock(tree, if_node, parent_map, tags) orelse return false;
    const if_pos = token_starts[main_tokens[if_node]];

    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block_node, &inline_statements) orelse return false;

    var fact = false;
    for (statements) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= if_pos) break;

        if (isGuardFlagAssignment(query, stmt, cond_name, unwrapped_var, tags, datas, main_tokens)) {
            fact = true;
            continue;
        }
        if (statementMayMutateStorage(query, stmt, unwrapped_var, tags, datas, block_node, type_context)) {
            fact = false;
        }
    }

    if (!fact) return false;
    const then_expr = @intFromEnum(full_if.ast.then_expr);
    return !statementMayMutateStorage(query, then_expr, unwrapped_var, tags, datas, block_node, type_context);
}

/// `std.ArrayList.pop` and `std.ArrayListUnmanaged.pop` yield null exactly
/// when the list is empty, so a condition that proves a lower bound on the
/// list length proves the removal's payload. The contract is bound to the
/// *verified* generic type: a same-spelled `pop` on a project type, or a
/// shadowed `std`, keeps its diagnostic. The bound is spent one element per
/// removal the guarded region performs first, so `len > 2` still proves a
/// third pop. Any other statement evaluated before the unwrap — including one
/// written into the guard's own condition, which runs ahead of the body on
/// every pass, and one nested in the `if`, `switch` prong or
/// `while (cond) : (payload)` payload that encloses it — may empty the list
/// first and cancels the proof, and so does a removal a loop nested in that
/// region can reach again, and so does a loop that can reach the unwrap again
/// on a later iteration.
pub fn isGuardedByContainerLength(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (unwrapped_var >= tags.len) return false;
    if (!call_resolver.isCallNode(tags[unwrapped_var])) return false;

    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(unwrapped_var)) orelse return false;
    if (call.ast.params.len != 0) return false;
    const receiver = removalReceiver(query, @intFromEnum(call.ast.fn_expr)) orelse return false;
    if (!isVerifiedStdArrayListExpression(query, receiver)) return false;

    // A nearer `if` may bound nothing while the `while` around it does, so
    // every enclosing condition is offered the proof and the first one that
    // carries a bound decides.
    var ancestor = unwrap_node;
    var depth: u32 = 0;
    while (depth < 64 and ancestor < parent_map.len) : (depth += 1) {
        const parent = parent_map[ancestor];
        if (parent == 0 or parent >= tags.len) return false;
        ancestor = parent;

        const guard: LengthGuard = switch (tags[parent]) {
            .@"while", .while_simple, .while_cont => blk: {
                const loop = tree.fullWhile(@enumFromInt(parent)) orelse return false;
                break :blk .{
                    .node = parent,
                    .condition = @intFromEnum(loop.ast.cond_expr),
                    .body = @intFromEnum(loop.ast.then_expr),
                    .continue_payload = if (loop.ast.cont_expr.unwrap()) |cont| @intFromEnum(cont) else null,
                    .else_branch = if (loop.ast.else_expr.unwrap()) |else_node| @intFromEnum(else_node) else null,
                };
            },
            .@"if", .if_simple => blk: {
                const branch = tree.fullIf(@enumFromInt(parent)) orelse return false;
                break :blk .{
                    .node = parent,
                    .condition = @intFromEnum(branch.ast.cond_expr),
                    .body = @intFromEnum(branch.ast.then_expr),
                    .continue_payload = null,
                    .else_branch = if (branch.ast.else_expr.unwrap()) |else_node| @intFromEnum(else_node) else null,
                };
            },
            else => continue,
        };
        if (guard.body >= tags.len) continue;
        if (!guardDominatesUnwrap(tree, guard, unwrap_node)) continue;
        const bound = lengthLowerBound(query, tree, guard.condition, receiver, tags, datas, 0) orelse continue;
        // A nested loop can reach the unwrap on a later iteration, after an
        // earlier removal consumed the length this guard proved.
        if (nestedLoopEncloses(unwrap_node, guard.node, parent_map, tags)) continue;

        var removals: u32 = 0;
        // The condition is evaluated again before the body on every pass, so a
        // removal or a mutation written into it spends or empties the list
        // before the guarded region starts: the same budget, the same reading.
        if (containerBodyMayDisturb(query, guard.condition, receiver, unwrap_node, &removals, type_context, false)) continue;
        // `while (cond) : (payload)` writes its payload before its body and runs
        // it after, so a body whose unwrap is the payload's runs in full ahead
        // of that unwrap however the two are spelled. Token order is not
        // evaluation order there, and cutting the body at the unwrap on token
        // order spends nothing of the bound the loop empties with.
        const unwrap_in_payload = if (guard.continue_payload) |cont|
            isInSubtree(tree, cont, unwrap_node)
        else
            false;
        if (containerBodyMayDisturb(
            query,
            guard.body,
            receiver,
            unwrap_node,
            &removals,
            type_context,
            unwrap_in_payload,
        )) continue;
        // The `while (cond) : (payload)` payload runs after the body, so it
        // only precedes the removal when the removal is inside the payload.
        if (guard.continue_payload) |cont| {
            if (unwrap_in_payload and
                containerBodyMayDisturb(query, cont, receiver, unwrap_node, &removals, type_context, false)) continue;
        }
        // The guarded removal is the `(removals + 1)`-th, so the bound has to
        // cover it: `len > 1` proves two elements and therefore two pops.
        if (removals >= bound) continue;
        return true;
    }
    return false;
}

/// One `while` or `if` whose condition is re-evaluated before the guarded
/// removal runs, so a length bound it proves holds at the removal.
const LengthGuard = struct {
    node: u32,
    condition: u32,
    body: u32,
    continue_payload: ?u32,
    else_branch: ?u32,
};

/// The condition decides whether the body runs, and the `else` continuation
/// runs precisely when it does not. The removal therefore has to live in the
/// body or in the `while (cond) : (payload)` continue payload that follows
/// it, never in the condition itself.
fn guardDominatesUnwrap(tree: *const std.zig.Ast, guard: LengthGuard, unwrap_node: u32) bool {
    if (isInSubtree(tree, guard.condition, unwrap_node)) return false;
    if (guard.else_branch) |else_node| {
        if (isInSubtree(tree, else_node, unwrap_node)) return false;
    }
    if (isInSubtree(tree, guard.body, unwrap_node)) return true;
    if (guard.continue_payload) |cont| return isInSubtree(tree, cont, unwrap_node);
    return false;
}

/// `<receiver>.pop()`, the removal the standard-library contract is stated
/// for. The receiver's *declared* type decides whether that contract applies,
/// never the spelling of the method.
fn removalReceiver(query: *const QueryContext, callee: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (callee >= tags.len or tags[callee] != .field_access) return null;
    const access = datas[callee].node_and_token;
    if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(access[1])), "pop")) return null;
    return @intFromEnum(access[0]);
}

/// A loop strictly between the guarded `while` and the unwrap can iterate again
/// after an earlier removal, so the condition no longer bounds the list.
fn nestedLoopEncloses(
    unwrap_node: u32,
    boundary: u32,
    parent_map: []const u32,
    tags: []const std.zig.Ast.Node.Tag,
) bool {
    if (unwrap_node >= parent_map.len) return false;
    var ancestor = parent_map[unwrap_node];
    var depth: u32 = 0;
    while (depth < 64 and ancestor != 0 and ancestor < tags.len and ancestor != boundary) : (depth += 1) {
        if (isLoopTag(tags[ancestor])) return true;
        ancestor = parent_map[ancestor];
    }
    return false;
}

/// A loop the tree spells as `while` or `for`: both may run their body again
/// after the removal they hold has already spent its unit.
fn isLoopTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .@"for", .for_simple, .@"while", .while_simple, .while_cont => true,
        else => false,
    };
}

fn isLoopNode(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;
    return isLoopTag(tags[node]);
}

/// Everything the guarded region evaluates before the unwrap — the guard's own
/// condition first, then its body — must leave the container's length alone,
/// except for removals: each one written outside a loop takes exactly one
/// element of the guarded list, so it spends a unit of the proved bound instead
/// of cancelling the proof. A loop *inside* the scanned region reaches its
/// removals once per iteration, so one of those spends an unbounded number of
/// units and cancels the proof outright.
/// `removals` accumulates across the scanned regions. A node that merely
/// *spans* the unwrap — the `if`, `switch` prong or block that encloses it —
/// is descended into so the statements preceding the unwrap inside it are
/// still inspected. The unwrap subtree is pruned
/// before descending: its operand is the very removal the guard proved, not a
/// competing mutation. Everything tokenised after the unwrap is skipped as
/// well, because a region that holds the unwrap runs its later statements
/// after it. `region_precedes_unwrap` names the regions where that reading is
/// wrong: the body of a `while (cond) : (payload)` the unwrap sits in is
/// written after the unwrap and run before it, so it is spent in full.
fn containerBodyMayDisturb(
    query: *const QueryContext,
    root: u32,
    target: u32,
    unwrap_node: u32,
    removals: *u32,
    type_context: ?*TypeContext,
    region_precedes_unwrap: bool,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    // An unwrap's first and last token are both the `.?`, so the guarded
    // region starts at the operand the removal produces.
    const unwrap_first = if (unwrap_node < tags.len and tags[unwrap_node] == .unwrap_optional)
        query.firstToken(@intFromEnum(datas[unwrap_node].node_and_token[0]))
    else
        query.firstToken(unwrap_node);
    const unwrap_last = query.lastToken(unwrap_node);

    const Scan = struct {
        query: *const QueryContext,
        target: u32,
        unwrap_node: u32,
        unwrap_first: u32,
        unwrap_last: u32,
        block: u32,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        removals: *u32,
        type_context: ?*TypeContext,
        region_precedes_unwrap: bool,
        found: bool = false,
        stop: bool = false,
        loop_depth: u32 = 0,

        const Self = @This();

        pub fn visit(self: *Self, _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
            if (isAssignmentTag(tag)) {
                if (tag == .assign_destructure) {
                    const destruct = self.query.tree.assignDestructure(@enumFromInt(node));
                    for (destruct.ast.variables) |variable| {
                        if (storageWriteMayAffect(
                            self.query,
                            @intFromEnum(variable),
                            self.target,
                            self.block,
                            self.type_context,
                        )) {
                            self.found = true;
                            self.stop = true;
                            return;
                        }
                    }
                } else {
                    const lhs = @intFromEnum(self.datas[node].node_and_node[0]);
                    if (storageWriteMayAffect(self.query, lhs, self.target, self.block, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                        return;
                    }
                }
            }
            switch (tag) {
                .call, .call_comma, .call_one, .call_one_comma => {
                    // A removal of the very list the guard bounded spends one
                    // element of the bound instead of cancelling the proof --
                    // unless a loop around it reaches it again, for then no
                    // bound covers how often it runs.
                    if (isRemovalOf(self.query, node, self.target)) {
                        if (self.loop_depth > 0) {
                            self.found = true;
                            self.stop = true;
                            return;
                        }
                        self.removals.* += 1;
                        return;
                    }
                    if (callMayMutateStorage(self.query, node, self.target, self.tags, self.datas, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                    }
                },
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (builtinCallMayMutateStorage(self.query, node, self.target, self.tags, self.datas, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                    }
                },
                else => {},
            }
        }

        /// Children are filtered before the walk descends, so a pruned node
        /// leaves its whole subtree unvisited rather than merely unexamined.
        /// A loop among them is counted, because everything its body holds
        /// runs once per iteration rather than once per pass.
        fn step(inner_tree: *const std.zig.Ast, node: u32, self: *Self) anyerror!void {
            if (self.stop) return;
            if (self.pruned(node)) return;
            if (!isLoopNode(inner_tree, node)) return self.scan(inner_tree, node);
            self.loop_depth += 1;
            defer self.loop_depth -= 1;
            return self.scan(inner_tree, node);
        }

        fn scan(self: *Self, inner_tree: *const std.zig.Ast, node: u32) !void {
            if (self.stop) return;
            const inner_tags = inner_tree.nodes.items(.tag);
            if (node >= inner_tags.len) return;
            try self.visit(inner_tree, node, inner_tags[node]);
            if (self.stop) return;
            ast_walk.walkChildren(Self, inner_tree, node, self, Self.step) catch unreachable;
        }

        /// The unwrap node, its operand and everything the `.?` closes over
        /// start at or after the operand's first token and end at or before the
        /// `.?`; a node that merely spans the unwrap starts before it.
        fn pruned(self: *Self, node: u32) bool {
            if (node == self.unwrap_node) return true;
            // Nothing in a region that runs before the unwrap as a whole
            // follows the removal, so no token cut applies to it.
            if (self.region_precedes_unwrap) return false;
            const first = self.query.firstToken(node);
            if (first > self.unwrap_last) return true;
            if (first < self.unwrap_first) return false;
            return self.query.lastToken(node) <= self.unwrap_last;
        }
    };

    var scan = Scan{
        .query = query,
        .target = target,
        .unwrap_node = unwrap_node,
        .unwrap_first = unwrap_first,
        .unwrap_last = unwrap_last,
        .block = root,
        .tags = tags,
        .datas = datas,
        .removals = removals,
        .type_context = type_context,
        .region_precedes_unwrap = region_precedes_unwrap,
    };
    // The walk is entered straight on the region root, so `Scan.step` never
    // sees it and a root that is itself a loop would still charge the removals
    // it holds one bound unit each. `while (cond) : (payload) while (...) ...`
    // spells its body as a bare loop, so raise the depth here to give that root
    // the same reading a nested loop gets.
    if (isLoopNode(tree, root)) scan.loop_depth += 1;
    scan.scan(tree, root) catch unreachable;
    return scan.found;
}

/// A verified standard-library removal call. `pop()` is the only one the
/// length bound is read from, and the value it hands back is what can make the
/// removed element an independent copy in the caller's own slot.
fn isRemovalResult(query: *const QueryContext, call_node: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (call_node >= tags.len or !call_resolver.isCallNode(tags[call_node])) return false;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse return false;
    if (call.ast.params.len != 0) return false;
    const receiver = removalReceiver(query, @intFromEnum(call.ast.fn_expr)) orelse return false;
    return isVerifiedStdArrayListExpression(query, receiver);
}

/// The list a verified removal was taken from, the receiver the method was
/// called on.
fn removalCallReceiver(query: *const QueryContext, call_node: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (call_node >= tags.len or !call_resolver.isCallNode(tags[call_node])) return null;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse return null;
    return removalReceiver(query, @intFromEnum(call.ast.fn_expr));
}

/// A removed element the new slot can write through. The element is whatever
/// the receiver's declared `std.ArrayList(T)` carries: a pointer or a slice
/// shares storage with whatever the list held, so `var first = list.pop().?;`
/// still designates that pointer, while a container or a primitive is copied
/// out of the list and designates nothing the list owns.
fn removalElementDesignatesSharedStorage(query: *const QueryContext, receiver: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (receiver >= tags.len) return true;
    const declared = switch (tags[receiver]) {
        .identifier => bindingTypeExprNode(query, receiver) orelse return true,
        .field_access => fieldTypeNode(query, receiver) orelse return true,
        .deref => bindingTypeExprNode(query, @intFromEnum(datas[receiver].node)) orelse return true,
        else => return true,
    };
    const element = arrayListElementTypeNode(query, tree, declared, tags, datas, 0) orelse return true;
    if (designatesStorageOutsideSlot(tree, element, 0)) return true;
    if (element >= tags.len or tags[element] != .identifier) return false;
    if (containerDeclForTypeName(tree, element, tags, datas) != null) return false;
    return !isPrimitiveTypeName(tree, element, tags);
}

/// The type argument of a verified `std.ArrayList(T)` / `std.ArrayListUnmanaged(T)`
/// declaration, with the pointer layers peeled off the container itself.
fn arrayListElementTypeNode(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    type_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    depth: u8,
) ?u32 {
    if (depth > 8 or type_node >= tags.len) return null;
    switch (tags[type_node]) {
        .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
            const pointer = tree.fullPtrType(@enumFromInt(type_node)) orelse return null;
            return arrayListElementTypeNode(query, tree, @intFromEnum(pointer.ast.child_type), tags, datas, depth + 1);
        },
        .optional_type => return arrayListElementTypeNode(query, tree, @intFromEnum(datas[type_node].node), tags, datas, depth + 1),
        .error_union => return arrayListElementTypeNode(query, tree, @intFromEnum(datas[type_node].node_and_node[1]), tags, datas, depth + 1),
        .grouped_expression => return arrayListElementTypeNode(query, tree, @intFromEnum(datas[type_node].node_and_token[0]), tags, datas, depth + 1),
        else => {},
    }

    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, @enumFromInt(type_node)) orelse return null;
    if (call.ast.params.len != 1) return null;
    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return null;
    const access = datas[callee].node_and_token;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
    if (!std.mem.eql(u8, name, "ArrayList") and !std.mem.eql(u8, name, "ArrayListUnmanaged")) return null;
    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    if (!resolver.isVerifiedImportBinding(@intFromEnum(access[0]), "std")) return null;
    return @intFromEnum(call.ast.params[0]);
}

/// A primitive type name the tree spells as an identifier. Anything else that
/// is not a container this file declares stays unknown, and unknown keeps the
/// conservative reading.
fn isPrimitiveTypeName(
    tree: *const std.zig.Ast,
    node: u32,
    tags: []const std.zig.Ast.Node.Tag,
) bool {
    if (node >= tags.len or tags[node] != .identifier) return false;
    const token = tree.nodes.items(.main_token)[node];
    if (token >= tree.tokens.len) return false;
    const name = tree.tokenSlice(token);
    if (name.len >= 2 and (name[0] == 'i' or name[0] == 'u')) {
        for (name[1..]) |c| {
            if (!std.ascii.isDigit(c)) return false;
        }
        return true;
    }
    const primitives = [_][]const u8{
        "bool", "void", "usize",  "isize", "f16",    "f32",       "f64",
        "f80",  "f128", "c_char", "c_int", "c_uint", "anyopaque",
    };
    for (primitives) |candidate| {
        if (std.mem.eql(u8, name, candidate)) return true;
    }
    return false;
}

/// A removal of the guarded list itself: `pop()` on the same receiver takes
/// exactly one element. A removal of another list, or of this one through an
/// alias, is not one and stays with the mutation checks.
fn isRemovalOf(query: *const QueryContext, call_node: u32, receiver: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (call_node >= tags.len or !call_resolver.isCallNode(tags[call_node])) return false;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse return false;
    if (call.ast.params.len != 0) return false;
    const popped = removalReceiver(query, @intFromEnum(call.ast.fn_expr)) orelse return false;
    if (!sameStoragePath(query, tree, popped, receiver, tags, datas)) return false;
    return isVerifiedStdArrayListExpression(query, popped);
}

/// The smallest length `<receiver>.items.len` can have while `cond_node`
/// holds. A conjunction proves the stronger of its two bounds and a conjunct
/// that says nothing about the length simply contributes none; a disjunction
/// is not read, because either side may hold on its own.
fn lengthLowerBound(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    cond_node: u32,
    receiver: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    depth: u8,
) ?u32 {
    if (cond_node >= tags.len or depth > 8) return null;
    switch (tags[cond_node]) {
        .bool_and => {
            const pair = datas[cond_node].node_and_node;
            const lhs = lengthLowerBound(query, tree, @intFromEnum(pair[0]), receiver, tags, datas, depth + 1) orelse 0;
            const rhs = lengthLowerBound(query, tree, @intFromEnum(pair[1]), receiver, tags, datas, depth + 1) orelse 0;
            return @max(lhs, rhs);
        },
        .grouped_expression => return lengthLowerBound(query, tree, @intFromEnum(datas[cond_node].node_and_token[0]), receiver, tags, datas, depth + 1),
        .bang_equal, .greater_than, .greater_or_equal => {},
        else => return null,
    }
    const pair = datas[cond_node].node_and_node;
    if (!isContainerItemsLength(query, tree, @intFromEnum(pair[0]), receiver, tags, datas)) return null;
    const bound = @intFromEnum(pair[1]);
    return switch (tags[cond_node]) {
        // `len != 0` can only hold while the list still holds something.
        .bang_equal => blk: {
            const zero = unsignedLiteralValue(tree, bound) orelse break :blk null;
            break :blk if (zero == 0) @as(u32, 1) else null;
        },
        .greater_or_equal => minimumUnsignedValue(query, tree, bound, tags, datas, 0),
        // `len > b` holds with `len` one above the smallest value `b` can take.
        .greater_than => blk: {
            const minimum = minimumUnsignedValue(query, tree, bound, tags, datas, 0) orelse break :blk null;
            const sum = @addWithOverflow(minimum, 1);
            if (sum[1] != 0) break :blk null;
            break :blk sum[0];
        },
        else => null,
    };
}

/// The smallest value an expression can take when it is written as an
/// unsigned integer: a declared `usize` or sized `uN` may be zero, and a
/// literal is its own value. `a + k` keeps the offset `k` whatever `a` holds,
/// because `+` is the checked addition the language defines: an operand pair
/// it cannot represent does not reach the guarded body at all. `+%` wraps
/// silently and `-|` saturates, so neither is read here, and a spelling this
/// file cannot resolve keeps the conservative answer.
fn minimumUnsignedValue(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    depth: u8,
) ?u32 {
    if (node >= tags.len or depth > 4) return null;
    switch (tags[node]) {
        .number_literal => return unsignedLiteralValue(tree, node),
        .identifier => {
            const declared = bindingTypeExprNode(query, node) orelse return null;
            if (!typeNodeIsUnsignedInt(tree, declared)) return null;
            return 0;
        },
        .field_access => {
            const declared = fieldTypeNode(query, node) orelse return null;
            if (!typeNodeIsUnsignedInt(tree, declared)) return null;
            return 0;
        },
        .add => {
            const pair = datas[node].node_and_node;
            if (unsignedLiteralValue(tree, @intFromEnum(pair[1]))) |offset| {
                const base = minimumUnsignedValue(query, tree, @intFromEnum(pair[0]), tags, datas, depth + 1) orelse return null;
                const sum = @addWithOverflow(base, offset);
                return if (sum[1] == 0) sum[0] else null;
            }
            if (unsignedLiteralValue(tree, @intFromEnum(pair[0]))) |offset| {
                const base = minimumUnsignedValue(query, tree, @intFromEnum(pair[1]), tags, datas, depth + 1) orelse return null;
                const sum = @addWithOverflow(base, offset);
                return if (sum[1] == 0) sum[0] else null;
            }
            return null;
        },
        else => return null,
    }
}

/// A written type whose values are unsigned. Primitive type names are
/// identifiers in the tree, so the declaration itself is the reading; a
/// signed integer, an untyped `comptime_int` and any type this file cannot
/// name keep the conservative answer.
fn typeNodeIsUnsignedInt(tree: *const std.zig.Ast, type_node: u32) bool {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (type_node >= tags.len or tags[type_node] != .identifier) return false;
    const token = main_tokens[type_node];
    if (token >= tree.tokens.len) return false;
    const name = tree.tokenSlice(token);
    if (std.mem.eql(u8, name, "usize") or std.mem.eql(u8, name, "c_uint")) return true;
    if (name.len < 2 or name[0] != 'u') return false;
    for (name[1..]) |c| {
        if (!std.ascii.isDigit(c)) return false;
    }
    return true;
}

/// The value of a non-negative integer literal. A float, a digit sequence the
/// parser could not reduce to plain digits, and a literal a unary `-`
/// negates all read as "unknown", because a bound built on a negative value
/// would prove nothing about an unsigned length.
fn unsignedLiteralValue(tree: *const std.zig.Ast, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= tags.len or tags[node] != .number_literal) return null;
    const token = main_tokens[node];
    if (token == 0 or token >= tree.tokens.len) return null;
    if (tree.tokenTag(token - 1) == .minus) return null;

    const text = tree.tokenSlice(token);
    var base: u8 = 10;
    var index: usize = 0;
    if (text.len >= 2 and text[0] == '0') {
        switch (text[1]) {
            'x', 'X' => base = 16,
            'o', 'O' => base = 8,
            'b', 'B' => base = 2,
            else => {},
        }
        if (base != 10) index = 2;
    }
    var digits_buf: [32]u8 = undefined;
    var digits_len: usize = 0;
    while (index < text.len) : (index += 1) {
        const c = text[index];
        if (c == '_') continue;
        if (digits_len >= digits_buf.len) return null;
        digits_buf[digits_len] = c;
        digits_len += 1;
    }
    if (digits_len == 0) return null;
    return std.fmt.parseInt(u32, digits_buf[0..digits_len], base) catch null;
}

fn isContainerItemsLength(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    node: u32,
    receiver: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len or tags[node] != .field_access) return false;
    const access = datas[node].node_and_token;
    if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(access[1])), "len")) return false;
    const items = @intFromEnum(access[0]);
    if (items >= tags.len or tags[items] != .field_access) return false;
    const items_access = datas[items].node_and_token;
    if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(items_access[1])), "items")) return false;
    // The container that owns `.items` must be the popping receiver itself, so
    // a local, a `*list` deref and a `holder.list` field all compare directly.
    return sameStoragePath(query, tree, @intFromEnum(items_access[0]), receiver, tags, datas);
}

/// Same root binding *and* same field chain: `p.waiters` matches `p.waiters`
/// but not `p.other` and not `self.waiters`.
fn sameStoragePath(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    left: u32,
    right: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    var a = left;
    var b = right;
    var depth: u32 = 0;
    while (depth < 16) : (depth += 1) {
        if (a >= tags.len or b >= tags.len) return false;
        if (tags[a] == .grouped_expression) {
            a = @intFromEnum(datas[a].node_and_token[0]);
            continue;
        }
        if (tags[b] == .grouped_expression) {
            b = @intFromEnum(datas[b].node_and_token[0]);
            continue;
        }
        if (tags[a] == .deref) {
            a = @intFromEnum(datas[a].node);
            continue;
        }
        if (tags[b] == .deref) {
            b = @intFromEnum(datas[b].node);
            continue;
        }
        if (tags[a] == .field_access and tags[b] == .field_access) {
            const left_access = datas[a].node_and_token;
            const right_access = datas[b].node_and_token;
            if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(left_access[1])), import_resolver.normalizeIdentifier(tree.tokenSlice(right_access[1])))) return false;
            a = @intFromEnum(left_access[0]);
            b = @intFromEnum(right_access[0]);
            continue;
        }
        if (tags[a] == .identifier and tags[b] == .identifier) {
            return sameIdentifierBinding(query, a, b);
        }
        return false;
    }
    return false;
}

/// The receiver must be a local, a parameter or a field whose *declared* type
/// is the verified `std.ArrayList`/`std.ArrayListUnmanaged` generic, so a
/// project type with its own `pop` never reaches the removal contract.
fn isVerifiedStdArrayListExpression(query: *const QueryContext, expr: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (expr >= tags.len) return false;
    switch (tags[expr]) {
        .grouped_expression => return isVerifiedStdArrayListExpression(
            query,
            @intFromEnum(datas[expr].node_and_token[0]),
        ),
        // `list.pop()`, `list.*.pop()` and a `*std.ArrayList(T)` receiver all
        // reach the same contract; the declared type is read from the binding.
        .identifier, .deref => {
            const base = if (tags[expr] == .deref) @intFromEnum(datas[expr].node) else expr;
            if (tags[base] != .identifier) return false;
            const declared = bindingTypeExprNode(query, base) orelse return false;
            return isVerifiedStdArrayListTypeNode(query, tree, declared, tags, datas);
        },
        .field_access => {
            const declared = fieldTypeNode(query, expr) orelse return false;
            return isVerifiedStdArrayListTypeNode(query, tree, declared, tags, datas);
        },
        else => return false,
    }
}

/// The type expression a `holder.list` access reads. The owner's container
/// comes from the base expression's resolved type; when expression
/// resolution cannot name one, the base binding's own declared type names it
/// instead, so a file-scope `const Holder = struct {...}` reached through
/// `*Holder` still resolves. Either way the member is read from that
/// container's own declaration, never from the name at the use site.
fn fieldTypeNode(query: *const QueryContext, access: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (access >= tags.len or tags[access] != .field_access) return null;
    const pair = datas[access].node_and_token;
    if (pair[1] >= tree.tokens.len) return null;
    const field_name = import_resolver.normalizeIdentifier(tree.tokenSlice(pair[1]));

    // The resolver only ever sees this file, so every container and member it
    // reports is an index into `tree`.
    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    const base = @intFromEnum(pair[0]);
    if (resolver.resolveExprType(base)) |owner| {
        if (owner.container_node != null) {
            if (resolver.resolveFieldTypeNode(owner, field_name)) |field| return field.node_index;
        }
    }
    // A root container type is a declaration, not an expression type, so the
    // base binding's declared type is the only remaining evidence. The
    // resolver already peels pointer, optional and error-union layers.
    const declared = bindingTypeExprNode(query, base) orelse return null;
    if (resolver.resolveTypeNode(declared)) |owner| {
        if (owner.container_node != null) {
            if (resolver.resolveFieldTypeNode(owner, field_name)) |field| return field.node_index;
        }
    }
    const container = containerDeclForTypeName(tree, declared, tags, datas) orelse return null;
    return containerMemberTypeNode(tree, container, field_name, tags);
}

/// The container a declared type names. Pointer, optional and error-union
/// layers reach the carried value, and what is left must be a plain type name
/// whose file-scope declaration spells a struct or a union. Struct *literals*
/// are deliberately not accepted — a root declaration initialised with one
/// holds a value, not a container definition — and every other spelling
/// leaves the container unknown.
fn containerDeclForTypeName(
    tree: *const std.zig.Ast,
    type_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) ?u32 {
    const main_tokens = tree.nodes.items(.main_token);
    var node = type_node;
    for (0..8) |_| {
        if (node >= tags.len) return null;
        switch (tags[node]) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                const pointer = tree.fullPtrType(@enumFromInt(node)) orelse return null;
                node = @intFromEnum(pointer.ast.child_type);
            },
            .optional_type => node = @intFromEnum(datas[node].node),
            .error_union => node = @intFromEnum(datas[node].node_and_node[1]),
            else => break,
        }
    }
    if (node >= tags.len or tags[node] != .identifier or node >= main_tokens.len) return null;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(main_tokens[node]));
    for (tree.rootDecls()) |decl| {
        const decl_node = @intFromEnum(decl);
        if (decl_node >= tags.len or !import_resolver.isVarDeclTag(tags[decl_node])) continue;
        const full = tree.fullVarDecl(@enumFromInt(decl_node)) orelse continue;
        const name_token = full.ast.mut_token + 1;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
        if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), name)) continue;
        const initializer = @intFromEnum(full.ast.init_node.unwrap() orelse continue);
        if (initializer >= tags.len) continue;
        return switch (tags[initializer]) {
            .container_decl,
            .container_decl_trailing,
            .container_decl_two,
            .container_decl_two_trailing,
            .container_decl_arg,
            .container_decl_arg_trailing,
            .tagged_union,
            .tagged_union_trailing,
            .tagged_union_enum_tag,
            .tagged_union_enum_tag_trailing,
            .tagged_union_two,
            .tagged_union_two_trailing,
            => initializer,
            else => null,
        };
    }
    return null;
}

/// The declared type one member of that container carries, whether it is
/// spelled `name: T` or `name: T = default`. A member written as a nested
/// `var`/`const` declaration is read the same way.
fn containerMemberTypeNode(
    tree: *const std.zig.Ast,
    container: u32,
    field_name: []const u8,
    tags: []const std.zig.Ast.Node.Tag,
) ?u32 {
    if (container >= tags.len) return null;
    var buffer: [2]std.zig.Ast.Node.Index = undefined;
    const decl = tree.fullContainerDecl(&buffer, @enumFromInt(container)) orelse return null;
    for (decl.ast.members) |member| {
        const member_node = @intFromEnum(member);
        if (member_node >= tags.len) continue;
        if (!memberIsNamed(tree, member_node, field_name)) continue;
        switch (tags[member_node]) {
            .container_field, .container_field_init, .container_field_align => {
                const field = tree.fullContainerField(@enumFromInt(member_node)) orelse continue;
                if (field.ast.type_expr.unwrap()) |type_node| return @intFromEnum(type_node);
            },
            .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl => {
                const full = tree.fullVarDecl(@enumFromInt(member_node)) orelse continue;
                if (full.ast.type_node.unwrap()) |type_node| return @intFromEnum(type_node);
            },
            else => {},
        }
    }
    return null;
}

/// True when a container member carries the name a field access reads, so
/// `holder.list` picks the `list` member and never a same-spelled one
/// elsewhere in the container.
fn memberIsNamed(tree: *const std.zig.Ast, member: u32, field_name: []const u8) bool {
    if (member >= tree.nodes.len) return false;
    var name_token: u32 = undefined;
    switch (tree.nodeTag(@enumFromInt(member))) {
        .container_field, .container_field_init, .container_field_align => {
            const field = tree.fullContainerField(@enumFromInt(member)) orelse return false;
            if (field.ast.tuple_like) return false;
            name_token = @intCast(field.ast.main_token);
        },
        .global_var_decl, .local_var_decl, .simple_var_decl, .aligned_var_decl => {
            const full = tree.fullVarDecl(@enumFromInt(member)) orelse return false;
            name_token = @intCast(full.ast.mut_token + 1);
        },
        else => return false,
    }
    if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return false;
    return std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), field_name);
}

/// The type expression written for the binding an identifier resolves to: the
/// declared type of a `var`/`const`, or the parameter's own type node.
fn bindingTypeExprNode(query: *const QueryContext, identifier: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (identifier >= tags.len or tags[identifier] != .identifier) return null;
    const binding = query.resolveIdentifierBinding(identifier) orelse return null;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(tree.nodeMainToken(@enumFromInt(identifier))));
    for (query.lexical.namedCandidates(name)) |candidate| {
        if (candidate.name_token != binding) continue;
        switch (candidate.kind) {
            .variable => {
                const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return null;
                return @intFromEnum(full.ast.type_node.unwrap() orelse return null);
            },
            .parameter => {
                if (tree.fullVarDecl(@enumFromInt(candidate.node))) |full|
                    return @intFromEnum(full.ast.type_node.unwrap() orelse return null);
                return candidate.node;
            },
            .function => return null,
        }
    }
    return null;
}

fn isVerifiedStdArrayListTypeNode(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    type_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    // A `*std.ArrayList(T)` declaration reaches the same contract through
    // auto-deref, so the pointer layers do not change the verdict.
    var node = type_node;
    for (0..8) |_| {
        if (node >= tags.len) return false;
        switch (tags[node]) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                const pointer = tree.fullPtrType(@enumFromInt(node)) orelse return false;
                node = @intFromEnum(pointer.ast.child_type);
                continue;
            },
            else => break,
        }
    }
    if (node >= tags.len) return false;
    return isVerifiedStdArrayListValueTypeNode(query, tree, node, tags, datas);
}

/// The type node itself, with every pointer layer already peeled off: a
/// by-value `std.ArrayList(T)`, whose instances own an independent copy of
/// the container header instead of designating the original object.
fn isVerifiedStdArrayListValueTypeNode(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    type_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (type_node >= tree.nodes.len) return false;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, @enumFromInt(type_node)) orelse return false;
    if (call.ast.params.len != 1) return false;
    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return false;
    const access = datas[callee].node_and_token;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
    if (!std.mem.eql(u8, name, "ArrayList") and !std.mem.eql(u8, name, "ArrayListUnmanaged")) return false;

    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    return resolver.isVerifiedImportBinding(@intFromEnum(access[0]), "std");
}

fn findEnclosingIfForUnwrap(
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    parent_map: []const u32,
    tags: []const std.zig.Ast.Node.Tag,
) ?u32 {
    var node = unwrap_node;
    var depth: u32 = 0;

    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;

        if (tags[parent] == .@"if" or tags[parent] == .if_simple) {
            const full_if = tree.fullIf(@enumFromInt(parent)) orelse return null;
            if (isInSubtree(tree, @intFromEnum(full_if.ast.then_expr), unwrap_node)) {
                return parent;
            }
        }

        node = parent;
    }

    return null;
}

fn findContainingBlock(
    tree: *const std.zig.Ast,
    node: u32,
    parent_map: []const u32,
    tags: []const std.zig.Ast.Node.Tag,
) ?u32 {
    _ = tree;
    var current = node;
    var depth: u32 = 0;

    while (current < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) break;

        switch (tags[parent]) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => return parent,
            else => {},
        }

        current = parent;
    }

    return null;
}

fn isGuardFlagAssignment(
    query: *const QueryContext,
    stmt: u32,
    flag_name: []const u8,
    unwrapped_var: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
) bool {
    const tree = query.tree;
    if (stmt >= tags.len) return false;

    switch (tags[stmt]) {
        .simple_var_decl, .local_var_decl, .aligned_var_decl => {
            const full = tree.fullVarDecl(@enumFromInt(stmt)) orelse return false;
            const name_token = full.ast.mut_token + 1;
            const token_tags = tree.tokens.items(.tag);
            if (name_token >= token_tags.len or token_tags[name_token] != .identifier) return false;

            const decl_name = tree.tokenSlice(name_token);
            if (!std.mem.eql(u8, decl_name, flag_name)) return false;

            const init_node = @intFromEnum(full.ast.init_node);
            if (init_node == 0 or init_node >= tags.len) return false;
            return isLabeledBlockGuardExpr(query, init_node, unwrapped_var, tags, datas);
        },
        .assign => {
            const lhs = @intFromEnum(datas[stmt].node_and_node[0]);
            const rhs = @intFromEnum(datas[stmt].node_and_node[1]);
            if (lhs >= tags.len or rhs >= tags.len) return false;
            if (tags[lhs] != .identifier) return false;
            const lhs_name = tree.tokenSlice(main_tokens[lhs]);
            if (!std.mem.eql(u8, lhs_name, flag_name)) return false;
            return isLabeledBlockGuardExpr(query, rhs, unwrapped_var, tags, datas);
        },
        else => return false,
    }
}

fn isLabeledBlockGuardExpr(
    query: *const QueryContext,
    node: u32,
    unwrapped_var: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len) return false;

    return switch (tags[node]) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => subtreeHasNullGuardBreak(query, node, unwrapped_var, tags, datas),
        else => false,
    };
}

fn subtreeHasNullGuardBreak(
    query: *const QueryContext,
    root: u32,
    unwrapped_var: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const tree = query.tree;
    const Visitor = struct {
        query: *const QueryContext,
        stop: bool = false,
        unwrapped_var: u32,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,

        const Self = @This();

        pub fn visit(self: *Self, inner_tree: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
            if (self.stop) return;

            switch (tag) {
                .@"orelse" => {
                    const pair = self.datas[node].node_and_node;
                    const lhs = @intFromEnum(pair[0]);
                    const rhs = @intFromEnum(pair[1]);
                    if (sameVariable(self.query, lhs, self.unwrapped_var) and
                        isBreakWithFalseAndLabel(inner_tree, rhs, self.tags, self.datas))
                    {
                        self.stop = true;
                        return;
                    }
                },
                .@"if", .if_simple => {
                    const full_if = inner_tree.fullIf(@enumFromInt(node)) orelse return;
                    const cond = @intFromEnum(full_if.ast.cond_expr);
                    if (checksNull(self.query, cond, self.unwrapped_var)) {
                        const then_expr = @intFromEnum(full_if.ast.then_expr);
                        if (subtreeHasBreakFalseLabel(inner_tree, then_expr, self.tags, self.datas)) {
                            self.stop = true;
                            return;
                        }
                    }
                },
                else => {},
            }
        }
    };

    var visitor = Visitor{ .query = query, .unwrapped_var = unwrapped_var, .tags = tags, .datas = datas };
    ast_walk.walk(Visitor, tree, root, &visitor) catch return false;
    return visitor.stop;
}

fn subtreeHasBreakFalseLabel(
    tree: *const std.zig.Ast,
    root: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const Visitor = struct {
        stop: bool = false,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,

        const Self = @This();

        pub fn visit(self: *Self, inner_tree: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
            if (self.stop) return;
            if (tag != .@"break") return;

            if (isBreakWithFalseAndLabel(inner_tree, node, self.tags, self.datas)) {
                self.stop = true;
            }
        }
    };

    var visitor = Visitor{ .tags = tags, .datas = datas };
    ast_walk.walk(Visitor, tree, root, &visitor) catch return false;
    return visitor.stop;
}

fn isBreakWithFalseAndLabel(
    tree: *const std.zig.Ast,
    node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len) return false;
    if (tags[node] != .@"break") return false;

    const break_data = datas[node].opt_token_and_opt_node;
    const break_label_token = break_data[0].unwrap() orelse return false;
    if (break_label_token >= tree.tokens.items(.tag).len) return false;

    const value_node = break_data[1].unwrap() orelse return false;
    const value_idx = @intFromEnum(value_node);
    if (value_idx >= tags.len) return false;
    if (tags[value_idx] != .identifier) return false;

    const value_name = tree.tokenSlice(tree.nodes.items(.main_token)[value_idx]);
    return std.mem.eql(u8, value_name, "false");
}

pub fn isGuardedByShortCircuit(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const block = findContainingBlock(tree, unwrap_node, parent_map, tags) orelse 0;
    var node = unwrap_node;
    var blocked_by_mutation = false;
    var depth: u32 = 0;
    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) break;
        const tag = tags[parent];
        if (tag == .bool_and or tag == .bool_or or tag == .@"if" or tag == .if_simple) {
            if (statementMayMutateStorageBefore(query, node, unwrapped_var, tags, datas, block, unwrap_node, type_context))
                blocked_by_mutation = true;
        }
        if (tag == .bool_and or tag == .bool_or) {
            const left = @intFromEnum(datas[parent].node_and_node[0]);
            const right = @intFromEnum(datas[parent].node_and_node[1]);
            if (node == right) {
                if (statementMayMutateStorage(query, left, unwrapped_var, tags, datas, block, type_context))
                    blocked_by_mutation = true;
                if (!blocked_by_mutation) {
                    if (tag == .bool_and and conditionImpliesNotNull(query, left, unwrapped_var)) return true;
                    if (tag == .bool_or and checksNull(query, left, unwrapped_var)) return true;
                }
            }
        }
        if (tag == .@"if" or tag == .if_simple) {
            const full = tree.fullIf(@enumFromInt(parent)) orelse break;
            const cond = @intFromEnum(full.ast.cond_expr);
            const cond_mutates = statementMayMutateStorage(query, cond, unwrapped_var, tags, datas, block, type_context);
            if (!blocked_by_mutation and !cond_mutates) {
                if (node == @intFromEnum(full.ast.then_expr) and conditionImpliesNotNull(query, cond, unwrapped_var)) return true;
                if (full.ast.else_expr.unwrap()) |else_node| {
                    if (node == @intFromEnum(else_node) and conditionImpliesNullnessOnFalse(query, cond, unwrapped_var, false)) return true;
                }
            }
        }
        node = parent;
    }
    return false;
}

fn isInSubtree(tree: *const std.zig.Ast, root_node: u32, target_node: u32) bool {
    if (root_node == target_node) return true;
    const tags = tree.nodes.items(.tag);
    if (root_node >= tags.len) return false;

    const Visitor = struct {
        stop: bool = false,
        target: u32,

        const Self = @This();

        pub fn visit(self: *Self, _: *const std.zig.Ast, node: u32, _: std.zig.Ast.Node.Tag) !void {
            if (self.stop) return;
            if (node == self.target) {
                self.stop = true;
            }
        }
    };

    var visitor = Visitor{ .target = target_node };
    ast_walk.walk(Visitor, tree, root_node, &visitor) catch return false;
    return visitor.stop;
}

fn checksNull(query: *const QueryContext, cond_node: u32, var_node: u32) bool {
    return checkNullComparison(query, cond_node, var_node, true);
}

fn conditionImpliesNotNull(query: *const QueryContext, cond_node: u32, var_node: u32) bool {
    return conditionImpliesNullness(query, cond_node, var_node, false);
}

fn conditionImpliesNullnessOnFalse(
    query: *const QueryContext,
    cond_node: u32,
    var_node: u32,
    want_null: bool,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (cond_node >= tags.len) return false;

    return switch (tags[cond_node]) {
        .bool_and => blk: {
            const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
            const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);
            break :blk conditionImpliesNullnessOnFalse(query, lhs, var_node, want_null) and
                conditionImpliesNullnessOnFalse(query, rhs, var_node, want_null);
        },
        .bool_or => blk: {
            const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
            const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);
            break :blk conditionImpliesNullnessOnFalse(query, lhs, var_node, want_null) or
                conditionImpliesNullnessOnFalse(query, rhs, var_node, want_null);
        },
        .grouped_expression => blk: {
            const inner = @intFromEnum(datas[cond_node].node_and_token[0]);
            break :blk conditionImpliesNullnessOnFalse(query, inner, var_node, want_null);
        },
        .bool_not => {
            const inner = @intFromEnum(datas[cond_node].node);
            return conditionImpliesNullness(query, inner, var_node, want_null);
        },
        .equal_equal, .bang_equal => checkNullComparison(query, cond_node, var_node, !want_null),
        else => false,
    };
}

fn conditionImpliesNullness(query: *const QueryContext, cond_node: u32, var_node: u32, want_null: bool) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (cond_node >= tags.len) return false;

    return switch (tags[cond_node]) {
        .bool_and => blk: {
            const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
            const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);
            break :blk conditionImpliesNullness(query, lhs, var_node, want_null) or
                conditionImpliesNullness(query, rhs, var_node, want_null);
        },
        .bool_or => blk: {
            const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
            const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);
            break :blk conditionImpliesNullness(query, lhs, var_node, want_null) and
                conditionImpliesNullness(query, rhs, var_node, want_null);
        },
        .grouped_expression => blk: {
            const inner = @intFromEnum(datas[cond_node].node_and_token[0]);
            break :blk conditionImpliesNullness(query, inner, var_node, want_null);
        },
        .bool_not => {
            const inner = @intFromEnum(datas[cond_node].node);
            return conditionImpliesNullnessOnFalse(query, inner, var_node, want_null);
        },
        .equal_equal, .bang_equal => checkNullComparison(query, cond_node, var_node, want_null),
        else => false,
    };
}

fn checkNullComparison(query: *const QueryContext, cond_node: u32, var_node: u32, is_null_check: bool) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (cond_node >= tags.len) return false;

    const cond_tag = tags[cond_node];
    if (cond_tag != .equal_equal and cond_tag != .bang_equal) return false;

    const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
    const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);

    // Check if one side is null and the other is our variable
    const lhs_is_null = isNullIdentifier(tree, lhs);
    const rhs_is_null = isNullIdentifier(tree, rhs);

    if (lhs_is_null and sameVariable(query, rhs, var_node)) {
        return is_null_check == (cond_tag == .equal_equal);
    }
    if (rhs_is_null and sameVariable(query, lhs, var_node)) {
        return is_null_check == (cond_tag == .equal_equal);
    }

    return false;
}

fn isNullIdentifier(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);

    if (node >= tags.len) return false;
    if (tags[node] != .identifier) return false;

    const token = main_tokens[node];
    const name = tree.tokenSlice(token);
    return std.mem.eql(u8, name, "null");
}

fn sameVariable(query: *const QueryContext, node1: u32, node2: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);

    if (node1 >= tags.len or node2 >= tags.len) return false;
    return sameVariableRecursive(query, node1, node2, tags, datas, main_tokens, 0);
}

fn sameVariableRecursive(
    query: *const QueryContext,
    node1: u32,
    node2: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    depth: u32,
) bool {
    const tree = query.tree;
    if (node1 >= tags.len or node2 >= tags.len or depth >= 32) return false;

    if (tags[node1] == .grouped_expression) {
        return sameVariableRecursive(
            query,
            @intFromEnum(datas[node1].node_and_token[0]),
            node2,
            tags,
            datas,
            main_tokens,
            depth + 1,
        );
    }
    if (tags[node2] == .grouped_expression) {
        return sameVariableRecursive(
            query,
            node1,
            @intFromEnum(datas[node2].node_and_token[0]),
            tags,
            datas,
            main_tokens,
            depth + 1,
        );
    }
    if (tags[node1] == .unwrap_optional) {
        return sameVariableRecursive(
            query,
            @intFromEnum(datas[node1].node_and_token[0]),
            node2,
            tags,
            datas,
            main_tokens,
            depth + 1,
        );
    }
    if (tags[node2] == .unwrap_optional) {
        return sameVariableRecursive(
            query,
            node1,
            @intFromEnum(datas[node2].node_and_token[0]),
            tags,
            datas,
            main_tokens,
            depth + 1,
        );
    }
    if (tags[node1] == .deref or tags[node1] == .address_of) {
        return sameVariableRecursive(
            query,
            @intFromEnum(datas[node1].node),
            node2,
            tags,
            datas,
            main_tokens,
            depth + 1,
        );
    }
    if (tags[node2] == .deref or tags[node2] == .address_of) {
        return sameVariableRecursive(
            query,
            node1,
            @intFromEnum(datas[node2].node),
            tags,
            datas,
            main_tokens,
            depth + 1,
        );
    }

    if (tags[node1] == .identifier and tags[node2] == .identifier) {
        if (node1 >= main_tokens.len or node2 >= main_tokens.len) return false;
        return sameIdentifierBinding(query, node1, node2);
    }

    if (tags[node1] == .field_access and tags[node2] == .field_access) {
        const field1 = datas[node1].node_and_token[1];
        const field2 = datas[node2].node_and_token[1];
        if (!std.mem.eql(u8, tree.tokenSlice(field1), tree.tokenSlice(field2))) return false;
        const base1 = @intFromEnum(datas[node1].node_and_token[0]);
        const base2 = @intFromEnum(datas[node2].node_and_token[0]);
        return sameVariableRecursive(query, base1, base2, tags, datas, main_tokens, depth + 1);
    }

    return false;
}

/// The first node the source spells with this name, so a test can point at a
/// declaration the same way the checks under test resolve it.
fn nodeNamed(tree: *const std.zig.Ast, name: []const u8, wanted: std.zig.Ast.Node.Tag) ?u32 {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    for (tags, 0..) |tag, index| {
        if (tag != wanted or index >= main_tokens.len) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(main_tokens[index]), name)) continue;
        return @intCast(index);
    }
    return null;
}

/// The `<type>.<method>(...)` call the source spells, read the way the
/// constructor proof reads it.
fn memberCall(tree: *const std.zig.Ast, method: []const u8) ?u32 {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    for (tags, 0..) |tag, index| {
        if (tag != .call_one and tag != .call_one_comma) continue;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(index)) orelse continue;
        const callee = @intFromEnum(call.ast.fn_expr);
        if (callee >= tags.len or tags[callee] != .field_access) continue;
        const access = datas[callee].node_and_token;
        if (!std.mem.eql(u8, tree.tokenSlice(access[1]), method)) continue;
        return @intCast(index);
    }
    return null;
}

test "only plain non-negative integer literals give a length bound" {
    const Case = struct { code: [:0]const u8, value: ?u32 };
    for ([_]Case{
        .{ .code = "const x = 0;", .value = 0 },
        .{ .code = "const x = 10;", .value = 10 },
        .{ .code = "const x = 0xFF;", .value = 255 },
        .{ .code = "const x = 0b101;", .value = 5 },
        .{ .code = "const x = 1_0;", .value = 10 },
        // A float is not an element count.
        .{ .code = "const x = 1.5;", .value = null },
    }) |case| {
        var tree = try std.zig.Ast.parse(std.testing.allocator, case.code, .zig);
        defer tree.deinit(std.testing.allocator);
        try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
        var literals: usize = 0;
        for (tree.nodes.items(.tag), 0..) |tag, index| {
            if (tag != .number_literal) continue;
            try std.testing.expectEqual(case.value, unsignedLiteralValue(&tree, @intCast(index)));
            literals += 1;
        }
        try std.testing.expectEqual(@as(usize, 1), literals);
    }
}

test "a length bound reads unsigned declarations and the offset a checked sum adds" {
    const code: [:0]const u8 =
        \\fn drain(keep: usize, count: u32, wide: i64) void {
        \\    _ = keep;
        \\    _ = count;
        \\    _ = wide;
        \\}
        \\
    ;
    var tree = try std.zig.Ast.parse(std.testing.allocator, code, .zig);
    defer tree.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var lexical = try lexical_index.LexicalIndex.init(std.testing.allocator, &tree);
    defer lexical.deinit(std.testing.allocator);
    const query = QueryContext{ .tree = &tree, .lexical = &lexical };
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    const keep = nodeNamed(&tree, "keep", .identifier) orelse return error.TestUnexpectedResult;
    const count = nodeNamed(&tree, "count", .identifier) orelse return error.TestUnexpectedResult;
    const wide = nodeNamed(&tree, "wide", .identifier) orelse return error.TestUnexpectedResult;

    // A declared `usize` or `uN` may be zero, so `len > keep` still proves one
    // element and `len > keep + 1` proves two.
    try std.testing.expectEqual(@as(?u32, 0), minimumUnsignedValue(&query, &tree, keep, tags, datas, 0));
    try std.testing.expectEqual(@as(?u32, 0), minimumUnsignedValue(&query, &tree, count, tags, datas, 0));
    // A signed declaration may be negative, and then bounds nothing.
    try std.testing.expect(minimumUnsignedValue(&query, &tree, wide, tags, datas, 0) == null);
}

test "a type factory's constructor is read through its declared result" {
    const code: [:0]const u8 =
        \\fn Resource(comptime T: type) type {
        \\    return struct {
        \\        value: T,
        \\        pub fn init(value: T) error{Invalid}!@This() {
        \\            return .{ .value = value };
        \\        }
        \\        pub fn maybeInit(value: T) ?@This() {
        \\            return .{ .value = value };
        \\        }
        \\        pub fn viaParam(value: T) error{Invalid}!T {
        \\            return value;
        \\        }
        \\    };
        \\}
        \\pub fn build(value: u8) void {
        \\    _ = Resource(u8).init(value);
        \\    _ = Resource(u8).maybeInit(value);
        \\    _ = Resource(u8).viaParam(value);
        \\}
        \\
    ;
    var tree = try std.zig.Ast.parse(std.testing.allocator, code, .zig);
    defer tree.deinit(std.testing.allocator);
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    var lexical = try lexical_index.LexicalIndex.init(std.testing.allocator, &tree);
    defer lexical.deinit(std.testing.allocator);
    const query = QueryContext{ .tree = &tree, .lexical = &lexical };

    // `@This()` is the struct the factory returned, so it cannot hold null.
    const init_call = memberCall(&tree, "init") orelse return error.TestUnexpectedResult;
    try std.testing.expect(isFactoryConstructorCall(&query, init_call));
    // An optional result keeps the diagnostic.
    const maybe_call = memberCall(&tree, "maybeInit") orelse return error.TestUnexpectedResult;
    try std.testing.expect(!isFactoryConstructorCall(&query, maybe_call));
    // A result that is a type parameter is only as optional as that parameter.
    const param_call = memberCall(&tree, "viaParam") orelse return error.TestUnexpectedResult;
    try std.testing.expect(!isFactoryConstructorCall(&query, param_call));
}
