const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
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
        const name = assertions.resolveDebugAssertionName(tree, call.ast.fn_expr, scope) orelse
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
        if (isInSubtree(tree, stmt, unwrap_node)) continue;

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
                fact = isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas);
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

fn isDefinitelyNonNullExpression(
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
        else => return typeInfoProvesNonNull(type_context, node),
    }
}

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

fn statementMayMutateStorage(
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
        root_node: u32,
        before_token: ?u32,
        type_context: ?*TypeContext,
        found: bool = false,
        stop: bool = false,

        const Self = @This();

        pub fn visit(self: *Self, _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
            if (self.before_token) |before| {
                if (self.query.firstToken(node) >= before) return;
                if (self.query.lastToken(node) >= before and
                    (node != self.root_node or !isPreTargetContainerTag(tag)))
                    return;
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
        .root_node = statement,
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

fn isPreTargetContainerTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .block,
        .block_semicolon,
        .block_two,
        .block_two_semicolon,
        .@"if",
        .if_simple,
        .@"while",
        .while_simple,
        .while_cont,
        .@"for",
        .for_simple,
        .@"switch",
        .switch_comma,
        .@"orelse",
        .@"catch",
        .bool_and,
        .bool_or,
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
        if (tags[receiver] != .unwrap_optional and storageRootsMayAlias(query, receiver, target, type_context)) {
            return true;
        }
    }

    for (full.ast.params) |param| {
        if (argumentMayMutateStorage(query, @intFromEnum(param), target, tags, datas, type_context)) return true;
    }
    return targetMayBeGlobal(query, target);
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
            if (!expressionNamesBinding(query, value_expr, source)) continue;
            if (!expressionMentionsBinding(query, value_expr, source)) continue;
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
/// `&root` and `root.*` always do, and a declared by-value `std` container
/// copy never does. A `.field_access` initializer is decided by the member's
/// own declared type alone: expression-type resolution cannot tell a
/// pointer-typed field from a value one, and a member whose type cannot be
/// read stays a pointer view. An unresolved (`.unknown`) expression type is
/// no evidence either, so it keeps the conservative reading.
fn initializerCarriesPointer(
    query: *const QueryContext,
    init: u32,
    type_context: ?*TypeContext,
) bool {
    const tags = query.tree.nodes.items(.tag);
    if (init >= tags.len) return true;
    switch (tags[init]) {
        .address_of, .deref => return true,
        .field_access => return !declaredByValueContainer(query, init),
        else => {},
    }
    if (declaredByValueContainer(query, init)) return false;
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

/// True when the initializer's *declared* type is a by-value `std` container,
/// so the new slot owns an independent copy instead of designating the
/// original one. A bare identifier is read through the declared type of the
/// binding it names, a `holder.field` access through the member's own
/// declared type; both are then verified through their `@import`, never by
/// name. A pointer or slice layer, and any type that cannot be read, keep the
/// conservative reading.
fn declaredByValueContainer(query: *const QueryContext, expr: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (expr >= tags.len) return false;
    const declared = switch (tags[expr]) {
        .identifier => bindingTypeExprNode(query, expr) orelse return false,
        .field_access => fieldTypeNode(query, expr) orelse return false,
        else => return false,
    };
    var node = declared;
    for (0..8) |_| {
        if (node >= tags.len) return false;
        switch (tags[node]) {
            // `*T` and `[]T` keep sharing the original storage.
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => return false,
            // `?T` and `E!T` carry the value itself.
            .optional_type => node = @intFromEnum(datas[node].node),
            .error_union => node = @intFromEnum(datas[node].node_and_node[1]),
            else => break,
        }
    }
    return isVerifiedStdArrayListValueTypeNode(query, tree, node, tags, datas);
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

pub fn isGuardedByMethodCallWithCatch(
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

    // Scan for method calls with catch before the unwrap.
    return scanBlockForMethodCallWithCatch(
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

fn scanBlockForMethodCallWithCatch(
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
        if (isInSubtree(tree, stmt, unwrap_node)) continue;

        if (tags[stmt] == .@"catch") {
            const operand = @intFromEnum(datas[stmt].node_and_node[0]);
            const handler = @intFromEnum(datas[stmt].node_and_node[1]);

            if (isEarlyExitExpr(tree, handler, tags, datas) and
                isMethodCallOnSelf(query, operand, tags, datas, ids.astIndex(fn_node)))
            {
                if (methodAssignsToField(query, operand, field_name, fn_node, type_context)) {
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

        if (bodyAssignsToSelfField(query, @intCast(i), field_name, type_context, tags, datas)) {
            return true;
        }
    }

    return false;
}

fn bodyAssignsToSelfField(
    query: *const QueryContext,
    fn_decl: u32,
    field_name: []const u8,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const tree = query.tree;
    // Find the body node
    if (fn_decl >= tags.len) return false;
    const fn_data = datas[fn_decl].node_and_node;
    const body = @intFromEnum(fn_data[1]);
    if (body == 0) return false;

    // Traverse the body looking for assignments to self.field_name
    var stack: [256]u32 = undefined;
    var stack_len: usize = 0;
    stack[stack_len] = body;
    stack_len += 1;

    while (stack_len > 0) {
        stack_len -= 1;
        const node = stack[stack_len];
        if (node >= tags.len) continue;

        if (tags[node] == .assign) {
            const pair = datas[node].node_and_node;
            const lhs = @intFromEnum(pair[0]);
            const rhs = @intFromEnum(pair[1]);
            if (isSelfFieldAccess(query, lhs, field_name, fn_decl, tags, datas) and
                isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas))
            {
                return true;
            }
        }

        // Push children based on node type
        switch (tags[node]) {
            .block, .block_semicolon => {
                const extra = datas[node].extra_range;
                const start: usize = @intFromEnum(extra.start);
                const end: usize = @intFromEnum(extra.end);
                for (start..end) |i| {
                    const child = tree.extra_data[i];
                    if (stack_len < stack.len) {
                        stack[stack_len] = child;
                        stack_len += 1;
                    }
                }
            },
            .block_two, .block_two_semicolon => {
                const opt_nodes = datas[node].opt_node_and_opt_node;
                if (opt_nodes[0].unwrap()) |n| {
                    if (stack_len < stack.len) {
                        stack[stack_len] = @intFromEnum(n);
                        stack_len += 1;
                    }
                }
                if (opt_nodes[1].unwrap()) |n| {
                    if (stack_len < stack.len) {
                        stack[stack_len] = @intFromEnum(n);
                        stack_len += 1;
                    }
                }
            },
            .@"if", .if_simple => {
                const full_if = tree.fullIf(@enumFromInt(node)) orelse continue;
                if (stack_len < stack.len) {
                    stack[stack_len] = @intFromEnum(full_if.ast.then_expr);
                    stack_len += 1;
                }
                if (full_if.ast.else_expr.unwrap()) |else_node| {
                    if (stack_len < stack.len) {
                        stack[stack_len] = @intFromEnum(else_node);
                        stack_len += 1;
                    }
                }
            },
            else => {},
        }
    }

    return false;
}

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
/// when the list is empty, so a loop condition that proves a positive length
/// proves the removal's payload. The contract is bound to the *verified*
/// generic type: a same-spelled `pop` on a project type, or a shadowed `std`,
/// keeps its diagnostic. It also covers a single removal, on the iteration the
/// condition admitted: a nested loop that can reach the unwrap again, or any
/// statement evaluated before it — including one nested in the `if`, `switch`
/// prong or `while (cond) : (payload)` payload that encloses the unwrap — may
/// empty the list first and cancels the proof.
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
    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return false;
    const access = datas[callee].node_and_token;
    if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(access[1])), "pop")) return false;
    const receiver = @intFromEnum(access[0]);

    if (!isVerifiedStdArrayListExpression(query, receiver)) return false;

    const loop_node = findEnclosingWhile(unwrap_node, parent_map, tags) orelse return false;
    const full = tree.fullWhile(@enumFromInt(loop_node)) orelse return false;
    const condition = @intFromEnum(full.ast.cond_expr);
    // The condition decides entry; the unwrap must live in the body or in the
    // `while (cond) : (payload)` continue payload, never in the condition or
    // in the `else` branch.
    if (isInSubtree(tree, condition, unwrap_node)) return false;
    if (full.ast.else_expr.unwrap()) |else_node| {
        if (isInSubtree(tree, @intFromEnum(else_node), unwrap_node)) return false;
    }
    const body = @intFromEnum(full.ast.then_expr);
    if (body >= tags.len) return false;
    const continue_payload: ?u32 = if (full.ast.cont_expr.unwrap()) |cont| @intFromEnum(cont) else null;
    const in_body = isInSubtree(tree, body, unwrap_node);
    const in_continue = if (continue_payload) |cont| isInSubtree(tree, cont, unwrap_node) else false;
    if (!in_body and !in_continue) return false;
    if (!conditionProvesPositiveLength(query, tree, condition, receiver, tags, datas)) return false;

    // A nested loop can reach the unwrap on a later iteration, after an earlier
    // removal consumed the length this iteration's condition proved.
    if (nestedLoopEncloses(unwrap_node, loop_node, parent_map, tags)) return false;

    if (containerBodyMayMutate(query, body, receiver, unwrap_node, type_context)) return false;
    if (continue_payload) |cont| {
        if (in_continue and containerBodyMayMutate(query, cont, receiver, unwrap_node, type_context)) return false;
    }
    return true;
}

fn findEnclosingWhile(
    unwrap_node: u32,
    parent_map: []const u32,
    tags: []const std.zig.Ast.Node.Tag,
) ?u32 {
    var node = unwrap_node;
    var depth: u32 = 0;
    while (node < parent_map.len and depth < 64) : (depth += 1) {
        const parent = parent_map[node];
        if (parent == 0 or parent >= tags.len) return null;
        switch (tags[parent]) {
            .@"while", .while_simple, .while_cont => return parent,
            else => {},
        }
        node = parent;
    }
    return null;
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
        switch (tags[ancestor]) {
            .@"for", .for_simple, .@"while", .while_simple, .while_cont => return true,
            else => {},
        }
        ancestor = parent_map[ancestor];
    }
    return false;
}

/// Everything the loop evaluates before the unwrap must leave the container's
/// length alone. A node that merely *spans* the unwrap — the `if`, `switch`
/// prong or block that encloses it — is descended into so the statements
/// preceding the unwrap inside it are still inspected. The unwrap subtree is
/// pruned before descending: its operand is the very removal the condition
/// proved, not a competing mutation. Everything tokenised after the unwrap is
/// skipped as well.
fn containerBodyMayMutate(
    query: *const QueryContext,
    root: u32,
    target: u32,
    unwrap_node: u32,
    type_context: ?*TypeContext,
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
        type_context: ?*TypeContext,
        found: bool = false,
        stop: bool = false,

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
        fn step(inner_tree: *const std.zig.Ast, node: u32, self: *Self) anyerror!void {
            if (self.stop) return;
            if (self.pruned(node)) return;
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
        .type_context = type_context,
    };
    scan.scan(tree, root) catch unreachable;
    return scan.found;
}

/// `<receiver>.items.len != 0`, `> 0` or `>= 1`.
fn conditionProvesPositiveLength(
    query: *const QueryContext,
    tree: *const std.zig.Ast,
    cond_node: u32,
    receiver: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (cond_node >= tags.len) return false;
    switch (tags[cond_node]) {
        .bang_equal, .greater_than, .greater_or_equal => {},
        else => return false,
    }
    const length = @intFromEnum(datas[cond_node].node_and_node[0]);
    const literal = @intFromEnum(datas[cond_node].node_and_node[1]);
    if (literal >= tree.nodes.len) return false;
    const literal_text = tree.tokenSlice(tree.nodeMainToken(@enumFromInt(literal)));
    return switch (tags[cond_node]) {
        .bang_equal => isContainerItemsLength(query, tree, length, receiver, tags, datas) and
            std.mem.eql(u8, literal_text, "0"),
        .greater_than => isContainerItemsLength(query, tree, length, receiver, tags, datas) and
            std.mem.eql(u8, literal_text, "0"),
        .greater_or_equal => isContainerItemsLength(query, tree, length, receiver, tags, datas) and
            std.mem.eql(u8, literal_text, "1"),
        else => false,
    };
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
