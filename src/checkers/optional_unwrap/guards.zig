const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
const ids = @import("../../ids.zig");
const TypeContext = @import("../../type_context.zig").TypeContext;
const assertions = @import("../../assertions.zig");

pub fn isGuardedByAssertion(
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    target: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
    scope: *const assertions.AssertionScope,
) bool {
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
    var statements: [ast_walk.max_block_statements]u32 = undefined;
    const count = ast_walk.getBlockStatements(tree, block, &statements) orelse return false;
    const before = tree.nodeMainToken(@enumFromInt(unwrap_node));
    var fact = false;
    for (statements[0..count]) |statement| {
        if (tree.firstToken(@enumFromInt(statement)) >= before) break;
        if (statementMayMutateStorageBefore(tree, statement, target, tags, datas, block, unwrap_node, type_context))
            fact = false;
        if (tree.lastToken(@enumFromInt(statement)) >= before) continue;
        const is_try = tags[statement] == .@"try";
        const call_node = if (is_try) @intFromEnum(datas[statement].node) else statement;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse continue;
        if (call.ast.params.len != 1) continue;
        const name = assertions.resolveDebugAssertionName(tree, call.ast.fn_expr, scope) orelse
            if (is_try) assertions.resolveAssertionName(tree, call.ast.fn_expr, scope) orelse continue else continue;
        if (assertions.constraintKindForName(name) != .boolean) continue;
        const condition = @intFromEnum(call.ast.params[0]);
        if (conditionImpliesNotNull(tree, condition, target) and
            !statementMayMutateStorage(tree, condition, target, tags, datas, block, type_context))
            fact = true;
    }
    return fact;
}

pub fn isGuardedByLazyInit(
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
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
        tree,
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
    tree: *const std.zig.Ast,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
) bool {
    if (block >= tags.len) return false;

    // Get position of the unwrap node.
    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    // Get statements from the block.
    var stmts_buf: [ast_walk.max_block_statements]u32 = undefined;
    const stmt_count = ast_walk.getBlockStatements(tree, block, &stmts_buf) orelse return false;
    var fact = false;

    // A lazy initialization proof remains valid only until a later storage write.
    for (stmts_buf[0..stmt_count]) |stmt| {
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
            if (checksNull(tree, cond, unwrapped_var)) {
                const then_expr = @intFromEnum(full.ast.then_expr);
                if (branchProvesNonNull(
                    tree,
                    then_expr,
                    unwrapped_var,
                    type_context,
                    tags,
                    datas,
                    block,
                )) {
                    if (full.ast.else_expr.unwrap()) |else_node| {
                        if (statementMayMutateStorage(
                            tree,
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
        if (statementMayMutateStorage(tree, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
        }
    }

    return fact;
}

fn branchProvesNonNull(
    tree: *const std.zig.Ast,
    node: u32,
    var_node: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
) bool {
    if (node >= tags.len) return false;

    switch (tags[node]) {
        .assign => {
            const pair = datas[node].node_and_node;
            const lhs = @intFromEnum(pair[0]);
            const rhs = @intFromEnum(pair[1]);
            return sameVariable(tree, lhs, var_node) and
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

                if (tags[statement] == .assign) {
                    const pair = datas[statement].node_and_node;
                    const lhs = @intFromEnum(pair[0]);
                    const rhs = @intFromEnum(pair[1]);
                    if (sameVariable(tree, lhs, var_node)) {
                        fact = isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas);
                        continue;
                    }
                }

                if (statementMayMutateStorage(tree, statement, var_node, tags, datas, block, type_context)) {
                    fact = false;
                }
            }

            return fact;
        },
        .block_two, .block_two_semicolon => {
            const opt_nodes = datas[node].opt_node_and_opt_node;
            var fact = false;
            if (opt_nodes[0].unwrap()) |statement| {
                fact = branchProvesNonNull(
                    tree,
                    @intFromEnum(statement),
                    var_node,
                    type_context,
                    tags,
                    datas,
                    block,
                );
            }
            if (opt_nodes[1].unwrap()) |statement| {
                const statement_node = @intFromEnum(statement);
                if (tags[statement_node] == .assign) {
                    const pair = datas[statement_node].node_and_node;
                    const lhs = @intFromEnum(pair[0]);
                    const rhs = @intFromEnum(pair[1]);
                    if (sameVariable(tree, lhs, var_node)) {
                        fact = isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas);
                    } else if (statementMayMutateStorage(tree, statement_node, var_node, tags, datas, block, type_context)) {
                        fact = false;
                    }
                } else if (statementMayMutateStorage(tree, statement_node, var_node, tags, datas, block, type_context)) {
                    fact = false;
                }
            }
            return fact;
        },
        else => return false,
    }
}

pub fn isGuardedByEarlyExit(
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
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
        tree,
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
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
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
        tree,
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
    tree: *const std.zig.Ast,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
) bool {
    if (block >= tags.len) return false;

    // Get the position of the unwrap node.
    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    // Get statements from the block.
    var stmts_buf: [ast_walk.max_block_statements]u32 = undefined;
    const stmt_count = ast_walk.getBlockStatements(tree, block, &stmts_buf) orelse return false;
    var fact = false;

    // A condition whose true branch exits leaves the false-branch facts in
    // force.  Use the full boolean expression, not only a direct comparison:
    // `if (x == null or other_is_invalid) return; x.?` is safe.
    for (stmts_buf[0..stmt_count]) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) continue;
        if (statementMayMutateStorage(tree, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
            continue;
        }

        if (tags[stmt] != .@"if" and tags[stmt] != .if_simple) continue;
        const full = tree.fullIf(@enumFromInt(stmt)) orelse continue;
        const cond = @intFromEnum(full.ast.cond_expr);
        const then_expr = @intFromEnum(full.ast.then_expr);
        if (isEarlyExitExpr(tree, then_expr, tags, datas) and
            conditionImpliesNullnessOnFalse(tree, cond, unwrapped_var, false))
        {
            fact = true;
        }
    }

    return fact;
}

fn scanBlockForSwitchNullCase(
    tree: *const std.zig.Ast,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
) bool {
    if (block >= tags.len) return false;

    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    var stmts_buf: [ast_walk.max_block_statements]u32 = undefined;
    const stmt_count = ast_walk.getBlockStatements(tree, block, &stmts_buf) orelse return false;
    var fact = false;

    for (stmts_buf[0..stmt_count]) |stmt| {
        if (stmt >= tags.len) continue;
        if (stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) continue;
        if (statementMayMutateStorage(tree, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
            continue;
        }

        if (tags[stmt] != .@"switch" and tags[stmt] != .switch_comma) continue;

        const full_switch = tree.switchFull(@enumFromInt(stmt));
        const cond = @intFromEnum(full_switch.ast.condition);
        if (!sameVariable(tree, cond, unwrapped_var)) continue;

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
            var statements: [ast_walk.max_block_statements]u32 = undefined;
            const statement_count = ast_walk.getBlockStatements(tree, node, &statements) orelse return false;
            for (statements[0..statement_count]) |statement| {
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
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
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
            tree,
            boundary,
            unwrapped_var,
            tags,
            datas,
            block,
            unwrap_node,
            type_context,
        )) return false;
        if (scanBlockForPriorAssignment(
            tree,
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
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
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

    var stmts_buf: [ast_walk.max_block_statements]u32 = undefined;
    const stmt_count = ast_walk.getBlockStatements(tree, block, &stmts_buf) orelse return false;
    var fact = false;

    for (stmts_buf[0..stmt_count]) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;
        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) break;

        if (statementMayMutateStorage(tree, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
            continue;
        }
        if (statementHasPriorUnwrap(tree, stmt, unwrap_node, unwrapped_var, unwrap_pos, tags, datas)) {
            fact = true;
        }
    }
    return fact;
}

fn scanBlockForPriorAssignment(
    tree: *const std.zig.Ast,
    block: u32,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    token_starts: []const u32,
) bool {
    if (block >= tags.len or unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    var stmts_buf: [ast_walk.max_block_statements]u32 = undefined;
    const stmt_count = ast_walk.getBlockStatements(tree, block, &stmts_buf) orelse return false;
    var fact = false;

    for (stmts_buf[0..stmt_count]) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;
        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) break;

        if (tags[stmt] == .assign and tree.lastToken(@enumFromInt(stmt)) < main_tokens[unwrap_node]) {
            const pair = datas[stmt].node_and_node;
            const lhs = @intFromEnum(pair[0]);
            const rhs = @intFromEnum(pair[1]);
            if (sameVariable(tree, lhs, unwrapped_var)) {
                fact = isDefinitelyNonNullExpression(tree, rhs, type_context, tags, datas);
                continue;
            }
            if (storageFieldsAreDisjoint(tree, lhs, unwrapped_var, type_context)) {
                if (statementMayMutateStorageBefore(tree, rhs, unwrapped_var, tags, datas, block, unwrap_node, type_context))
                    fact = false;
                continue;
            }
        }

        if (statementMayMutateStorageBefore(tree, stmt, unwrapped_var, tags, datas, block, unwrap_node, type_context)) {
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
    tree: *const std.zig.Ast,
    statement: u32,
    target_unwrap: u32,
    unwrapped_var: u32,
    limit_pos: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);
    return hasUnconditionalPriorUnwrap(
        tree,
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
    tree: *const std.zig.Ast,
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
    if (node == 0 or node == target_unwrap or depth >= 64) return false;
    if (node >= tags.len or node >= main_tokens.len) return false;
    if (main_tokens[node] >= token_starts.len or token_starts[main_tokens[node]] >= limit_pos) return false;

    switch (tags[node]) {
        .unwrap_optional => {
            const operand = @intFromEnum(datas[node].node_and_token[0]);
            if (sameVariable(tree, operand, unwrapped_var)) return true;
            return hasUnconditionalPriorUnwrap(
                tree,
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
                tree,
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
                tree,
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
                tree,
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
                tree,
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
                tree,
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
                    tree,
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
                tree,
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
                tree,
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
                tree,
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
                tree,
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
                tree,
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
                tree,
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
                    tree,
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
                    tree,
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
                    tree,
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
                    tree,
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
                tree,
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
                tree,
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
                    tree,
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
                tree,
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
                tree,
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
                    tree,
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
                    tree,
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
                    tree,
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

fn statementMayMutateStorage(
    tree: *const std.zig.Ast,
    statement: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    type_context: ?*TypeContext,
) bool {
    return statementMayMutateStorageBefore(tree, statement, target, tags, datas, block, null, type_context);
}

fn statementMayMutateStorageBefore(
    tree: *const std.zig.Ast,
    statement: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    block: u32,
    before_node: ?u32,
    type_context: ?*TypeContext,
) bool {
    const Visitor = struct {
        tree: *const std.zig.Ast,
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
                const ast_node: std.zig.Ast.Node.Index = @enumFromInt(node);
                if (self.tree.firstToken(ast_node) >= before) return;
                if (self.tree.lastToken(ast_node) >= before and
                    (node != self.root_node or !isPreTargetContainerTag(tag)))
                    return;
            }
            if (isAssignmentTag(tag)) {
                if (tag == .assign_destructure) {
                    const full = self.tree.assignDestructure(@enumFromInt(node));
                    for (full.ast.variables) |variable| {
                        if (storageWriteMayAffect(
                            self.tree,
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
                    if (storageWriteMayAffect(self.tree, lhs, self.target, self.block, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                        return;
                    }
                }
            }
            switch (tag) {
                .call, .call_comma, .call_one, .call_one_comma => {
                    if (callMayMutateStorage(self.tree, node, self.target, self.tags, self.datas, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                    }
                },
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (builtinCallMayMutateStorage(self.tree, node, self.target, self.tags, self.datas, self.type_context)) {
                        self.found = true;
                        self.stop = true;
                    }
                },
                else => {},
            }
        }
    };

    var visitor = Visitor{
        .tree = tree,
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

fn storageFieldsAreDisjoint(tree: *const std.zig.Ast, lhs: u32, target: u32, type_context: ?*TypeContext) bool {
    const ctx = type_context orelse return false;
    if (tree.nodeTag(@enumFromInt(lhs)) != .field_access or
        tree.nodeTag(@enumFromInt(target)) != .field_access)
        return false;
    const left = tree.nodeData(@enumFromInt(lhs)).node_and_token;
    const right = tree.nodeData(@enumFromInt(target)).node_and_token;
    if (std.mem.eql(u8, tree.tokenSlice(left[1]), tree.tokenSlice(right[1]))) return false;
    return sameVariable(tree, @intFromEnum(left[0]), @intFromEnum(right[0])) and
        ctx.isStructExpression(@intFromEnum(left[0]));
}

fn storageWriteMayAffect(tree: *const std.zig.Ast, lhs: u32, target: u32, block: u32, type_context: ?*TypeContext) bool {
    const tags = tree.nodes.items(.tag);
    if (lhs >= tags.len) return true;
    if (storageFieldsAreDisjoint(tree, lhs, target, type_context)) return false;
    if (storageRootMatches(tree, lhs, target)) return true;
    return switch (tags[lhs]) {
        .deref, .address_of, .field_access, .array_access => !localSlotHasNoAliases(tree, target, block, type_context),
        .identifier => false,
        else => true,
    };
}

fn localSlotHasNoAliases(tree: *const std.zig.Ast, target: u32, block: u32, type_context: ?*TypeContext) bool {
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
    const binding = resolveIdentifierBinding(tree, root) orelse return false;
    if (binding == 0) return false;
    const declaration_tag = tree.tokenTag(binding - 1);
    if (declaration_tag != .keyword_var and declaration_tag != .keyword_const) return false;
    const function = enclosingFunctionForToken(tree, binding) orelse return false;
    const reference = tree.nodeMainToken(@enumFromInt(target));
    if (enclosingFunctionForToken(tree, reference) != function) return false;
    if (enclosingFunctionForToken(tree, tree.firstToken(@enumFromInt(block))) != function) return false;
    const function_start = tree.firstToken(@enumFromInt(function));

    for (tags, 0..) |tag, index| {
        const node: std.zig.Ast.Node.Index = @enumFromInt(index);
        const start = tree.firstToken(node);
        if (start < function_start or start >= reference) continue;
        if (tag == .@"asm" or tag == .asm_simple) return false;
        if (start <= binding) continue;
        if (tag == .address_of and storageRootMatches(tree, @intFromEnum(tree.nodeData(node).node), target)) return false;
        if (call_resolver.isCallNode(tag)) {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, node) orelse return false;
            const callee = call.ast.fn_expr;
            if (tree.nodeTag(callee) == .field_access and
                storageRootMatches(tree, @intFromEnum(tree.nodeData(callee).node_and_token[0]), target))
                return false;
        }
        switch (tag) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&buffer, node) orelse return false;
                for (params) |param| {
                    if (storageRootMatches(tree, @intFromEnum(param), target)) return false;
                }
            },
            else => {},
        }
    }
    return true;
}

fn callMayMutateStorage(
    tree: *const std.zig.Ast,
    call_node: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    type_context: ?*TypeContext,
) bool {
    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
    const full = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return true;
    const callee = @intFromEnum(full.ast.fn_expr);
    if (callee >= tags.len) return true;

    if (tags[callee] == .field_access) {
        const receiver = @intFromEnum(datas[callee].node_and_token[0]);
        if (receiver >= tags.len) return true;
        if (tags[receiver] != .unwrap_optional and storageRootMatches(tree, receiver, target)) {
            return true;
        }
    }

    for (full.ast.params) |param| {
        if (argumentMayMutateStorage(tree, @intFromEnum(param), target, tags, datas, type_context)) return true;
    }
    return targetMayBeGlobal(tree, target);
}

fn builtinCallMayMutateStorage(
    tree: *const std.zig.Ast,
    call_node: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    type_context: ?*TypeContext,
) bool {
    var builtin_buf: [2]std.zig.Ast.Node.Index = undefined;
    const params = tree.builtinCallParams(&builtin_buf, @enumFromInt(call_node)) orelse return true;
    for (params) |param| {
        if (argumentMayMutateStorage(tree, @intFromEnum(param), target, tags, datas, type_context)) return true;
    }
    return targetMayBeGlobal(tree, target);
}

// Unknown calls may mutate globals. This is invalidation only, not a name-based proof.
fn targetMayBeGlobal(tree: *const std.zig.Ast, target: u32) bool {
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
    for (tree.rootDecls()) |decl| {
        const decl_node = @intFromEnum(decl);
        if (decl_node >= tags.len) continue;
        switch (tags[decl_node]) {
            .simple_var_decl, .local_var_decl, .global_var_decl, .aligned_var_decl => {
                const full = tree.fullVarDecl(@enumFromInt(decl_node)) orelse continue;
                const name_token = full.ast.mut_token + 1;
                if (name_token < tree.tokens.items(.tag).len and
                    std.mem.eql(u8, tree.tokenSlice(name_token), root_name))
                {
                    return true;
                }
            },
            else => {},
        }
    }
    return false;
}

fn argumentMayMutateStorage(
    tree: *const std.zig.Ast,
    node: u32,
    target: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    type_context: ?*TypeContext,
) bool {
    if (node >= tags.len) return true;
    var argument = node;
    while (argument < tags.len) {
        switch (tags[argument]) {
            .grouped_expression, .unwrap_optional => {
                argument = @intFromEnum(datas[argument].node_and_token[0]);
            },
            .identifier => {
                if (!storageRootMatches(tree, argument, target)) return false;
                return argumentExpressionMayEscape(type_context, argument);
            },
            .address_of => {
                const pointee = @intFromEnum(datas[argument].node);
                if (storageFieldsAreDisjoint(tree, pointee, target, type_context)) return false;
                return storageRootMatches(tree, argument, target);
            },
            .deref => return storageRootMatches(tree, argument, target),
            .array_access => {
                const base = @intFromEnum(datas[argument].node_and_node[0]);
                if (storageRootMatches(tree, base, target)) return true;
                argument = base;
            },
            .call, .call_comma, .call_one, .call_one_comma => {
                var call_buf: [1]std.zig.Ast.Node.Index = undefined;
                const full = tree.fullCall(&call_buf, @enumFromInt(argument)) orelse return true;
                const callee = @intFromEnum(full.ast.fn_expr);
                if (callee < tags.len and tags[callee] == .field_access) {
                    const receiver = @intFromEnum(datas[callee].node_and_token[0]);
                    if (storageRootMatches(tree, receiver, target)) return true;
                }
                for (full.ast.params) |param| {
                    if (argumentMayMutateStorage(tree, @intFromEnum(param), target, tags, datas, type_context)) return true;
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

fn storageRootMatches(tree: *const std.zig.Ast, node: u32, target: u32) bool {
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
        return sameIdentifierBinding(tree, left, right);
    }
    return false;
}

const BindingScope = struct {
    first_token: u32,
    last_token: u32,

    fn contains(self: BindingScope, token: u32) bool {
        return token >= self.first_token and token <= self.last_token;
    }

    fn span(self: BindingScope) u32 {
        return self.last_token - self.first_token;
    }
};

const BindingCandidate = struct {
    name_token: u32,
    scope: BindingScope,
    function_node: ?u32,
};

fn sameIdentifierBinding(tree: *const std.zig.Ast, left: u32, right: u32) bool {
    const left_binding = resolveIdentifierBinding(tree, left) orelse return false;
    const right_binding = resolveIdentifierBinding(tree, right) orelse return false;
    return left_binding == right_binding;
}

fn resolveIdentifierBinding(tree: *const std.zig.Ast, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= tags.len or tags[node] != .identifier or node >= main_tokens.len) return null;

    const reference_token = main_tokens[node];
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(reference_token));
    const reference_function = enclosingFunctionForToken(tree, reference_token);
    var best: ?BindingCandidate = null;

    for (tags, 0..) |tag, node_index| {
        if (!import_resolver.isVarDeclTag(tag)) continue;
        const full = tree.fullVarDecl(@enumFromInt(node_index)) orelse continue;
        const name_token = full.ast.mut_token + 1;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
        if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), name)) continue;
        const is_root = isRootDeclaration(tree, node_index);
        if (!is_root and name_token > reference_token) continue;

        const function_node = if (is_root) null else enclosingFunctionForToken(tree, name_token);
        if (function_node != null and reference_function != function_node) continue;
        const scope = if (is_root)
            rootBindingScope(tree)
        else
            smallestBindingScope(tree, name_token) orelse continue;
        considerBindingCandidate(
            .{ .name_token = name_token, .scope = scope, .function_node = function_node },
            reference_token,
            reference_function,
            &best,
        );
    }

    considerFunctionParameterBindings(tree, name, reference_token, reference_function, &best);
    considerPayloadBindings(tree, name, reference_token, reference_function, &best);
    return if (best) |candidate| candidate.name_token else null;
}

fn considerBindingCandidate(
    candidate: BindingCandidate,
    reference_token: u32,
    reference_function: ?u32,
    best: *?BindingCandidate,
) void {
    if (!candidate.scope.contains(reference_token)) return;
    if (candidate.function_node != null and candidate.function_node != reference_function) return;
    if (best.*) |previous| {
        if (candidate.scope.span() > previous.scope.span()) return;
        if (candidate.scope.span() == previous.scope.span() and candidate.name_token <= previous.name_token) return;
    }
    best.* = candidate;
}

fn considerFunctionParameterBindings(
    tree: *const std.zig.Ast,
    name: []const u8,
    reference_token: u32,
    reference_function: ?u32,
    best: *?BindingCandidate,
) void {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    var buffer: [1]std.zig.Ast.Node.Index = undefined;

    for (tags, 0..) |tag, node_index| {
        const proto_node = switch (tag) {
            .fn_decl => @intFromEnum(datas[node_index].node_and_node[0]),
            .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi => @as(u32, @intCast(node_index)),
            else => continue,
        };
        if (proto_node >= tags.len) continue;
        const function_node = enclosingFunctionForToken(tree, tree.firstToken(@enumFromInt(proto_node)));
        if (function_node != reference_function) continue;
        const scope = bindingNodeScope(tree, if (function_node) |fn_node| fn_node else proto_node) orelse continue;

        const params: []const std.zig.Ast.Node.Index = switch (tags[proto_node]) {
            .fn_proto => tree.fnProto(@enumFromInt(proto_node)).ast.params,
            .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)).ast.params,
            .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(proto_node)).ast.params,
            .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)).ast.params,
            else => continue,
        };
        for (params) |param| {
            const parameter_node = @intFromEnum(param);
            const name_token = parameterBindingNameToken(tree, parameter_node) orelse continue;
            if (name_token > reference_token) continue;
            if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), name)) continue;
            considerBindingCandidate(
                .{ .name_token = name_token, .scope = scope, .function_node = function_node },
                reference_token,
                reference_function,
                best,
            );
        }
    }
}

const PayloadBindingSearch = struct {
    tree: *const std.zig.Ast,
    name: []const u8,
    reference_token: u32,
    reference_function: ?u32,
    best: *?BindingCandidate,

    fn optional(self: PayloadBindingSearch, payload_token: ?u32, body: u32) void {
        var token = payload_token orelse return;
        const token_tags = self.tree.tokens.items(.tag);
        if (token < token_tags.len and token_tags[token] == .asterisk) token += 1;
        if (token >= token_tags.len or token_tags[token] != .identifier) return;
        if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(self.tree.tokenSlice(token)), self.name)) return;
        const scope = bindingNodeScope(self.tree, body) orelse return;
        const function_node = enclosingFunctionForToken(self.tree, token);
        considerBindingCandidate(
            .{ .name_token = token, .scope = scope, .function_node = function_node },
            self.reference_token,
            self.reference_function,
            self.best,
        );
    }

    fn conditional(self: PayloadBindingSearch, full: anytype) void {
        self.optional(full.payload_token, @intFromEnum(full.ast.then_expr));
        if (full.ast.else_expr.unwrap()) |else_node| {
            self.optional(full.error_token, @intFromEnum(else_node));
        }
    }

    fn forPayloads(self: PayloadBindingSearch, payload_token: u32, body: u32) void {
        const token_tags = self.tree.tokens.items(.tag);
        if (payload_token >= token_tags.len) return;
        var token = payload_token;
        if (token_tags[token] == .pipe) token += 1;
        if (token == 0 or token >= token_tags.len or token_tags[token - 1] != .pipe) return;
        if (token_tags[token] != .identifier and token_tags[token] != .asterisk) return;
        while (token < token_tags.len) : (token += 1) {
            if (token_tags[token] == .pipe) break;
            if (token_tags[token] == .asterisk) {
                token += 1;
                if (token >= token_tags.len) return;
            }
            if (token_tags[token] == .identifier) self.optional(token, body);
        }
    }
};

fn considerPayloadBindings(
    tree: *const std.zig.Ast,
    name: []const u8,
    reference_token: u32,
    reference_function: ?u32,
    best: *?BindingCandidate,
) void {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const search = PayloadBindingSearch{
        .tree = tree,
        .name = name,
        .reference_token = reference_token,
        .reference_function = reference_function,
        .best = best,
    };
    for (tags, 0..) |tag, node_index| {
        const node = @as(u32, @intCast(node_index));
        switch (tag) {
            .@"if", .if_simple => {
                const full = tree.fullIf(@enumFromInt(node)) orelse continue;
                search.conditional(full);
            },
            .@"while", .while_simple, .while_cont => {
                const full = tree.fullWhile(@enumFromInt(node)) orelse continue;
                search.conditional(full);
            },
            .@"for", .for_simple => {
                const full = tree.fullFor(@enumFromInt(node)) orelse continue;
                search.forPayloads(full.payload_token, @intFromEnum(full.ast.then_expr));
            },
            .@"switch", .switch_comma => {
                const full = tree.switchFull(@enumFromInt(node));
                for (full.ast.cases) |case_node| {
                    const full_case = tree.fullSwitchCase(case_node) orelse continue;
                    search.optional(full_case.payload_token, @intFromEnum(full_case.ast.target_expr));
                }
            },
            .@"catch" => {
                const pair = datas[node].node_and_node;
                const catch_token = tree.nodes.items(.main_token)[node];
                const token_tags = tree.tokens.items(.tag);
                if (catch_token + 2 >= token_tags.len or token_tags[catch_token + 1] != .pipe) continue;
                search.optional(catch_token + 2, @intFromEnum(pair[1]));
            },
            .@"errdefer" => {
                const payload_token = datas[node].opt_token_and_node[0].unwrap() orelse continue;
                search.optional(payload_token, @intFromEnum(datas[node].opt_token_and_node[1]));
            },
            else => {},
        }
    }
}

fn parameterBindingNameToken(tree: *const std.zig.Ast, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= tags.len or node >= main_tokens.len) return null;
    if (import_resolver.isVarDeclTag(tags[node])) {
        const full = tree.fullVarDecl(@enumFromInt(node)) orelse return null;
        const name_token = full.ast.mut_token + 1;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
        return name_token;
    }
    return @intCast(import_resolver.paramNameTokenBeforeType(tree, node) orelse return null);
}

fn bindingNodeScope(tree: *const std.zig.Ast, node: u32) ?BindingScope {
    if (node == 0 or node >= tree.nodes.len or tree.tokens.len == 0) return null;
    return .{
        .first_token = @intCast(tree.firstToken(@enumFromInt(node))),
        .last_token = @intCast(tree.lastToken(@enumFromInt(node))),
    };
}

fn rootBindingScope(tree: *const std.zig.Ast) BindingScope {
    return .{
        .first_token = 0,
        .last_token = if (tree.tokens.len == 0) 0 else @intCast(tree.tokens.len - 1),
    };
}

fn smallestBindingScope(tree: *const std.zig.Ast, token: u32) ?BindingScope {
    const tags = tree.nodes.items(.tag);
    var best: ?BindingScope = null;
    for (tags, 0..) |tag, node_index| {
        if (!isBindingScopeTag(tag)) continue;
        const scope = bindingNodeScope(tree, @intCast(node_index)) orelse continue;
        if (!scope.contains(token)) continue;
        if (best == null or scope.span() < best.?.span()) best = scope;
    }
    return best;
}

fn isBindingScopeTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => true,
        else => call_resolver.isContainerTag(tag),
    };
}

fn isRootDeclaration(tree: *const std.zig.Ast, node: usize) bool {
    for (tree.rootDecls()) |decl| {
        if (@intFromEnum(decl) == node) return true;
    }
    return false;
}

fn enclosingFunctionForToken(tree: *const std.zig.Ast, token: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    var best: ?u32 = null;
    var best_span: u32 = std.math.maxInt(u32);
    for (tags, 0..) |tag, node_index| {
        if (tag != .fn_decl) continue;
        const scope = bindingNodeScope(tree, @intCast(node_index)) orelse continue;
        if (!scope.contains(token) or scope.span() >= best_span) continue;
        best = @intCast(node_index);
        best_span = scope.span();
    }
    return best;
}

pub fn isGuardedByMethodCallWithCatch(
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    fn_node: ids.AstNodeId,
    type_context: ?*TypeContext,
) bool {
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
    if (!isSelfReceiver(tree, obj, ids.astIndex(fn_node))) return false;

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
        tree,
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
    tree: *const std.zig.Ast,
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
    if (block >= tags.len) return false;

    // Get position of the unwrap node.
    if (unwrap_node >= main_tokens.len) return false;
    const unwrap_pos = token_starts[main_tokens[unwrap_node]];

    // A successful method guard remains valid only until a later storage write.
    var fact = false;
    var stmts_buf: [ast_walk.max_block_statements]u32 = undefined;
    const stmt_count = ast_walk.getBlockStatements(tree, block, &stmts_buf) orelse return false;

    for (stmts_buf[0..stmt_count]) |stmt| {
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= unwrap_pos) continue;
        if (isInSubtree(tree, stmt, unwrap_node)) continue;

        if (tags[stmt] == .@"catch") {
            const operand = @intFromEnum(datas[stmt].node_and_node[0]);
            const handler = @intFromEnum(datas[stmt].node_and_node[1]);

            if (isEarlyExitExpr(tree, handler, tags, datas) and
                isMethodCallOnSelf(tree, operand, tags, datas, ids.astIndex(fn_node)))
            {
                if (methodAssignsToField(tree, operand, field_name, fn_node, type_context)) {
                    fact = true;
                    continue;
                }
            }
        }

        if (statementMayMutateStorage(tree, stmt, unwrapped_var, tags, datas, block, type_context)) {
            fact = false;
        }
    }

    return fact;
}

fn isMethodCallOnSelf(
    tree: *const std.zig.Ast,
    call_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    fn_node: u32,
) bool {
    if (call_node >= tags.len or !call_utils.isCallNode(tags[call_node])) return false;

    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
    const full_call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return false;
    const callee = @intFromEnum(full_call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return false;

    const receiver = @intFromEnum(datas[callee].node_and_token[0]);
    return isSelfReceiver(tree, receiver, fn_node);
}

fn isSelfReceiver(tree: *const std.zig.Ast, receiver: u32, fn_node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (receiver >= tags.len or tags[receiver] != .identifier) return false;
    const files = [_]import_resolver.File{.{ .path = "", .tree = tree }};
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
    tree: *const std.zig.Ast,
    call_node: u32,
    field_name: []const u8,
    fn_node: ids.AstNodeId,
    type_context: ?*TypeContext,
) bool {
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

    const files = [_]import_resolver.File{.{ .path = "", .tree = tree }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    const receiver_type = resolver.resolveExprType(receiver) orelse return false;

    // Resolve the receiver type before matching a method.  A method name is
    // not a callable identity: same-spelled methods on another type cannot
    // establish this field's invariant.
    for (0..tags.len) |i| {
        if (tags[i] != .fn_decl) continue;
        if (i == ids.astIndex(fn_node)) continue;

        const fn_proto_idx = @intFromEnum(datas[i].node_and_node[0]);
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

        if (bodyAssignsToSelfField(tree, @intCast(i), field_name, type_context, tags, datas)) {
            return true;
        }
    }

    return false;
}

fn bodyAssignsToSelfField(
    tree: *const std.zig.Ast,
    fn_decl: u32,
    field_name: []const u8,
    type_context: ?*TypeContext,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
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
            if (isSelfFieldAccess(tree, lhs, field_name, fn_decl, tags, datas) and
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
    tree: *const std.zig.Ast,
    node: u32,
    field_name: []const u8,
    fn_decl: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len or tags[node] != .field_access) return false;

    const obj = @intFromEnum(datas[node].node_and_token[0]);
    const field_token = datas[node].node_and_token[1];
    if (!isSelfReceiver(tree, obj, fn_decl)) return false;
    return std.mem.eql(u8, tree.tokenSlice(field_token), field_name);
}

pub fn isGuardedByLabeledBlockInvariant(
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
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

    var stmts_buf: [ast_walk.max_block_statements]u32 = undefined;
    const stmt_count = ast_walk.getBlockStatements(tree, block_node, &stmts_buf) orelse return false;

    var fact = false;
    for (0..stmt_count) |idx| {
        const stmt = stmts_buf[idx];
        if (stmt >= tags.len or stmt >= main_tokens.len) continue;

        const stmt_pos = token_starts[main_tokens[stmt]];
        if (stmt_pos >= if_pos) break;

        if (isGuardFlagAssignment(tree, stmt, cond_name, unwrapped_var, tags, datas, main_tokens)) {
            fact = true;
            continue;
        }
        if (statementMayMutateStorage(tree, stmt, unwrapped_var, tags, datas, block_node, type_context)) {
            fact = false;
        }
    }

    if (!fact) return false;
    const then_expr = @intFromEnum(full_if.ast.then_expr);
    return !statementMayMutateStorage(tree, then_expr, unwrapped_var, tags, datas, block_node, type_context);
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
    tree: *const std.zig.Ast,
    stmt: u32,
    flag_name: []const u8,
    unwrapped_var: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
) bool {
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
            return isLabeledBlockGuardExpr(tree, init_node, unwrapped_var, tags, datas);
        },
        .assign => {
            const lhs = @intFromEnum(datas[stmt].node_and_node[0]);
            const rhs = @intFromEnum(datas[stmt].node_and_node[1]);
            if (lhs >= tags.len or rhs >= tags.len) return false;
            if (tags[lhs] != .identifier) return false;
            const lhs_name = tree.tokenSlice(main_tokens[lhs]);
            if (!std.mem.eql(u8, lhs_name, flag_name)) return false;
            return isLabeledBlockGuardExpr(tree, rhs, unwrapped_var, tags, datas);
        },
        else => return false,
    }
}

fn isLabeledBlockGuardExpr(
    tree: *const std.zig.Ast,
    node: u32,
    unwrapped_var: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    if (node >= tags.len) return false;

    return switch (tags[node]) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => subtreeHasNullGuardBreak(tree, node, unwrapped_var, tags, datas),
        else => false,
    };
}

fn subtreeHasNullGuardBreak(
    tree: *const std.zig.Ast,
    root: u32,
    unwrapped_var: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
) bool {
    const Visitor = struct {
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
                    if (sameVariable(inner_tree, lhs, self.unwrapped_var) and
                        isBreakWithFalseAndLabel(inner_tree, rhs, self.tags, self.datas))
                    {
                        self.stop = true;
                        return;
                    }
                },
                .@"if", .if_simple => {
                    const full_if = inner_tree.fullIf(@enumFromInt(node)) orelse return;
                    const cond = @intFromEnum(full_if.ast.cond_expr);
                    if (checksNull(inner_tree, cond, self.unwrapped_var)) {
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

    var visitor = Visitor{ .unwrapped_var = unwrapped_var, .tags = tags, .datas = datas };
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
    tree: *const std.zig.Ast,
    unwrap_node: u32,
    unwrapped_var: u32,
    parent_map: []const u32,
    type_context: ?*TypeContext,
) bool {
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
            if (statementMayMutateStorageBefore(tree, node, unwrapped_var, tags, datas, block, unwrap_node, type_context))
                blocked_by_mutation = true;
        }
        if (tag == .bool_and or tag == .bool_or) {
            const left = @intFromEnum(datas[parent].node_and_node[0]);
            const right = @intFromEnum(datas[parent].node_and_node[1]);
            if (node == right) {
                if (statementMayMutateStorage(tree, left, unwrapped_var, tags, datas, block, type_context))
                    blocked_by_mutation = true;
                if (!blocked_by_mutation) {
                    if (tag == .bool_and and conditionImpliesNotNull(tree, left, unwrapped_var)) return true;
                    if (tag == .bool_or and checksNull(tree, left, unwrapped_var)) return true;
                }
            }
        }
        if (tag == .@"if" or tag == .if_simple) {
            const full = tree.fullIf(@enumFromInt(parent)) orelse break;
            const cond = @intFromEnum(full.ast.cond_expr);
            const cond_mutates = statementMayMutateStorage(tree, cond, unwrapped_var, tags, datas, block, type_context);
            if (!blocked_by_mutation and !cond_mutates) {
                if (node == @intFromEnum(full.ast.then_expr) and conditionImpliesNotNull(tree, cond, unwrapped_var)) return true;
                if (full.ast.else_expr.unwrap()) |else_node| {
                    if (node == @intFromEnum(else_node) and conditionImpliesNullnessOnFalse(tree, cond, unwrapped_var, false)) return true;
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

fn checksNull(tree: *const std.zig.Ast, cond_node: u32, var_node: u32) bool {
    return checkNullComparison(tree, cond_node, var_node, true);
}

fn conditionImpliesNotNull(tree: *const std.zig.Ast, cond_node: u32, var_node: u32) bool {
    return conditionImpliesNullness(tree, cond_node, var_node, false);
}

fn conditionImpliesNullnessOnFalse(
    tree: *const std.zig.Ast,
    cond_node: u32,
    var_node: u32,
    want_null: bool,
) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (cond_node >= tags.len) return false;

    return switch (tags[cond_node]) {
        .bool_and => blk: {
            const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
            const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);
            break :blk conditionImpliesNullnessOnFalse(tree, lhs, var_node, want_null) and
                conditionImpliesNullnessOnFalse(tree, rhs, var_node, want_null);
        },
        .bool_or => blk: {
            const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
            const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);
            break :blk conditionImpliesNullnessOnFalse(tree, lhs, var_node, want_null) or
                conditionImpliesNullnessOnFalse(tree, rhs, var_node, want_null);
        },
        .grouped_expression => blk: {
            const inner = @intFromEnum(datas[cond_node].node_and_token[0]);
            break :blk conditionImpliesNullnessOnFalse(tree, inner, var_node, want_null);
        },
        .bool_not => {
            const inner = @intFromEnum(datas[cond_node].node);
            return conditionImpliesNullness(tree, inner, var_node, want_null);
        },
        .equal_equal, .bang_equal => checkNullComparison(tree, cond_node, var_node, !want_null),
        else => false,
    };
}

fn conditionImpliesNullness(tree: *const std.zig.Ast, cond_node: u32, var_node: u32, want_null: bool) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    if (cond_node >= tags.len) return false;

    return switch (tags[cond_node]) {
        .bool_and => blk: {
            const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
            const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);
            break :blk conditionImpliesNullness(tree, lhs, var_node, want_null) or
                conditionImpliesNullness(tree, rhs, var_node, want_null);
        },
        .bool_or => blk: {
            const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
            const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);
            break :blk conditionImpliesNullness(tree, lhs, var_node, want_null) and
                conditionImpliesNullness(tree, rhs, var_node, want_null);
        },
        .grouped_expression => blk: {
            const inner = @intFromEnum(datas[cond_node].node_and_token[0]);
            break :blk conditionImpliesNullness(tree, inner, var_node, want_null);
        },
        .bool_not => {
            const inner = @intFromEnum(datas[cond_node].node);
            return conditionImpliesNullnessOnFalse(tree, inner, var_node, want_null);
        },
        .equal_equal, .bang_equal => checkNullComparison(tree, cond_node, var_node, want_null),
        else => false,
    };
}

fn checkNullComparison(tree: *const std.zig.Ast, cond_node: u32, var_node: u32, is_null_check: bool) bool {
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

    if (lhs_is_null and sameVariable(tree, rhs, var_node)) {
        return is_null_check == (cond_tag == .equal_equal);
    }
    if (rhs_is_null and sameVariable(tree, lhs, var_node)) {
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

fn sameVariable(tree: *const std.zig.Ast, node1: u32, node2: u32) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);

    if (node1 >= tags.len or node2 >= tags.len) return false;
    return sameVariableRecursive(tree, node1, node2, tags, datas, main_tokens, 0);
}

fn sameVariableRecursive(
    tree: *const std.zig.Ast,
    node1: u32,
    node2: u32,
    tags: []const std.zig.Ast.Node.Tag,
    datas: []const std.zig.Ast.Node.Data,
    main_tokens: []const u32,
    depth: u32,
) bool {
    if (node1 >= tags.len or node2 >= tags.len or depth >= 32) return false;

    if (tags[node1] == .grouped_expression) {
        return sameVariableRecursive(
            tree,
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
            tree,
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
            tree,
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
            tree,
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
            tree,
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
            tree,
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
        return sameIdentifierBinding(tree, node1, node2);
    }

    if (tags[node1] == .field_access and tags[node2] == .field_access) {
        const field1 = datas[node1].node_and_token[1];
        const field2 = datas[node2].node_and_token[1];
        if (!std.mem.eql(u8, tree.tokenSlice(field1), tree.tokenSlice(field2))) return false;
        const base1 = @intFromEnum(datas[node1].node_and_token[0]);
        const base2 = @intFromEnum(datas[node2].node_and_token[0]);
        return sameVariableRecursive(tree, base1, base2, tags, datas, main_tokens, depth + 1);
    }

    return false;
}
