const std = @import("std");
const assertions = @import("../../assertions.zig");
const ast_walk = @import("../../ast_walk.zig");
const checker_mod = @import("../../checker.zig");
const Diagnostic = checker_mod.Diagnostic;
const CheckerError = checker_mod.CheckerError;
const Source = @import("../../source.zig").Source;
const ids = @import("../../ids.zig");
const guards = @import("guards.zig");
const diagnostics = @import("diagnostics.zig");
const engine_mod = @import("../../engine.zig");
const AnalysisEngine = engine_mod.AnalysisEngine;
const cfg_mod = @import("../../cfg.zig");
const Cfg = cfg_mod.Cfg;

const TypeContext = checker_mod.TypeContext;

pub fn scanForUnsafeUnwraps(
    src: *Source,
    allocator: std.mem.Allocator,
    diagnostics_list: *std.ArrayList(Diagnostic),
    tree: *const std.zig.Ast,
    engine: *AnalysisEngine,
    cfg: *const Cfg,
    reported: *std.AutoHashMap(u32, void),
    fn_node: ids.AstNodeId,
    type_context: ?*TypeContext,
) CheckerError!void {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);
    const datas = tree.nodes.items(.data);

    // Scan only the AST nodes that are part of this function's body
    // We do this by walking the function body's AST subtree
    const fn_index = ids.astIndex(fn_node);
    if (fn_index >= tags.len) return;

    const parent_map = try allocator.alloc(u32, tags.len);
    defer allocator.free(parent_map);
    @memset(parent_map, 0);
    ast_walk.fillParentMap(tree, fn_index, parent_map);

    const allow_bare = tags[fn_index] == .test_decl;
    var assertion_scope = try assertions.buildAssertionScope(allocator, tree, fn_index, allow_bare);
    defer assertion_scope.deinit(allocator);

    // Collect all unwrap_optional nodes within this function's body
    var unwraps: std.ArrayList(u32) = .empty;
    defer unwraps.deinit(allocator);

    try collectUnwrapsInSubtree(tree, fn_index, allocator, &unwraps);

    for (unwraps.items) |ast_node| {
        // Skip if already reported
        if (reported.contains(ast_node)) continue;

        // Skip unwraps inside test assertion calls (expectEqual, expectEqualStrings, etc.)
        // These are intentional - the test will panic if the value is null
        if (diagnostics.isInsideTestAssertion(tree, ast_node, parent_map, &assertion_scope)) continue;

        // Skip unwraps inside comptime type expressions (@typeInfo, @TypeOf, etc.)
        // These are evaluated at compile time and will produce a compile error, not a runtime panic
        if (diagnostics.isInsideComptimeTypeExpr(tree, ast_node, parent_map)) continue;

        // Get the variable being unwrapped
        const unwrapped_node = @intFromEnum(datas[ast_node].node_and_token[0]);

        if (guards.isGuardedByAssertion(tree, ast_node, unwrapped_node, parent_map, type_context, &assertion_scope)) continue;

        // Check if the unwrap is guarded by short-circuit evaluation (and/or operators)
        // or by a ternary if expression. These are AST-level guards that the CFG
        // doesn't track because short-circuit evaluation is implicit.
        if (guards.isGuardedByShortCircuit(tree, ast_node, unwrapped_node, parent_map, type_context)) continue;

        // Check if this is a lazy initialization pattern where we initialize
        // the optional before unwrapping it
        if (guards.isGuardedByLazyInit(tree, ast_node, unwrapped_node, parent_map, type_context)) continue;

        // Check if this is an early exit pattern where a null check leads to
        // continue/break/return, making subsequent code only reachable when non-null
        if (guards.isGuardedByEarlyExit(tree, ast_node, unwrapped_node, parent_map, type_context)) continue;

        // Check if this is a switch that exits on null before the unwrap
        if (guards.isGuardedBySwitchNullCase(tree, ast_node, unwrapped_node, parent_map, type_context)) continue;

        // Check if this is an assignment followed by immediate unwrap pattern
        // e.g., `x = foo() orelse return error; x.?`
        if (guards.isGuardedByPriorAssignment(tree, ast_node, unwrapped_node, parent_map, type_context)) continue;

        // A successful earlier unwrap remains a proof only until the storage path
        // is written or passed to a call that may mutate it.
        if (guards.isGuardedByPriorUnwrap(tree, ast_node, unwrapped_node, parent_map, type_context)) continue;

        // Check if this is a method call with catch/early exit that ensures the field
        // e.g., `self.ensureTexture() catch return; ... self.texture.?`
        if (guards.isGuardedByMethodCallWithCatch(tree, ast_node, unwrapped_node, parent_map, fn_node, type_context)) continue;

        // Check if this is a labeled block invariant pattern
        // e.g., `const flag = blk: { x orelse break :blk false; ... }; if (flag) { x.? }`
        if (guards.isGuardedByLabeledBlockInvariant(tree, ast_node, unwrapped_node, parent_map, type_context)) continue;

        // Find the CFG node containing this AST node
        const cfg_node_idx = findCfgNodeForAst(cfg, ast_node, tree);
        const node_idx = cfg_node_idx orelse {
            // AST node not in CFG (possibly unreachable code) - report conservatively
            try diagnostics.reportUnsafeUnwrap(src, allocator, diagnostics_list, main_tokens[ast_node], token_starts);
            try reported.put(ast_node, {});
            continue;
        };

        // Check if the variable is proven non-null at this point
        if (!isProvenNonNull(engine, node_idx, unwrapped_node, cfg, tree)) {
            try diagnostics.reportUnsafeUnwrap(src, allocator, diagnostics_list, main_tokens[ast_node], token_starts);
            try reported.put(ast_node, {});
        }
    }
}

fn collectUnwrapsInSubtree(
    tree: *const std.zig.Ast,
    root: u32,
    allocator: std.mem.Allocator,
    out: *std.ArrayList(u32),
) CheckerError!void {
    var collector = UnwrapCollector{ .allocator = allocator, .out = out };
    try ast_walk.walk(UnwrapCollector, tree, root, &collector);
}

const UnwrapCollector = struct {
    allocator: std.mem.Allocator,
    out: *std.ArrayList(u32),
    stop: bool = false,

    pub fn visit(self: *UnwrapCollector, _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) CheckerError!void {
        if (tag == .unwrap_optional) try self.out.append(self.allocator, node);
    }
};

fn findCfgNodeForAst(cfg: *const Cfg, ast_node: u32, tree: *const std.zig.Ast) ?ids.CfgNodeId {
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    if (ast_node >= main_tokens.len) return null;

    const target_pos = token_starts[main_tokens[ast_node]];

    var best_match: ?ids.CfgNodeId = null;
    var best_start: u32 = 0;

    for (cfg.nodes.items, 0..) |node, idx| {
        if (node.ir_node.ast_node) |node_ast| {
            if (node_ast >= main_tokens.len) continue;
            const cfg_pos = token_starts[main_tokens[node_ast]];

            // Find CFG nodes that start at or before the target position
            // and pick the one that starts closest to the target
            if (cfg_pos <= target_pos and cfg_pos >= best_start) {
                best_start = cfg_pos;
                best_match = ids.cfgId(@intCast(idx));
            }
        }
    }

    return best_match;
}

fn isProvenNonNull(
    engine: *AnalysisEngine,
    cfg_node_idx: ids.CfgNodeId,
    unwrapped_node: u32,
    cfg: *const Cfg,
    tree: *const std.zig.Ast,
) bool {
    var node: std.zig.Ast.Node.Index = @enumFromInt(unwrapped_node);
    while (tree.nodeTag(node) == .grouped_expression) node = tree.nodeData(node).node_and_token[0];
    // Root-variable facts do not prove the nullability of a field or pointee.
    if (tree.nodeTag(node) != .identifier) return false;
    // Get all states reaching this CFG node
    const graph = engine.getGraph();

    // Find the variable ID for the unwrapped expression using the engine's resolver
    const var_id = engine.resolveVarIdFromExpr(@intFromEnum(node), cfg);

    // Track if we found any states at this CFG node
    var found_states = false;
    var all_paths_safe = true;

    // Check all exploded nodes at this CFG location
    for (graph.nodes.items) |exploded_node| {
        if (exploded_node.point.node_index != cfg_node_idx) continue;

        found_states = true;

        // Check if this state proves the variable is non-null
        if (var_id) |vid| {
            const state = &exploded_node.state;

            // Check environment for non-null value
            if (state.getVar(vid)) |val| {
                if (val.isNonNull()) {
                    continue; // This path is safe
                }
                if (!val.isUnknown() and !val.isNull()) {
                    // Concrete values (ints, bools) are non-null
                    continue;
                }
            }

            // Check constraints for null_check with is_null=false
            if (state.hasNonNullConstraint(vid)) {
                continue; // This path is safe
            }

            // This path has an unguarded unwrap
            all_paths_safe = false;
        } else {
            // Couldn't resolve the variable - be conservative
            all_paths_safe = false;
        }
    }

    // If we found no states at this point, be conservative
    if (!found_states) {
        return false;
    }

    return all_paths_safe;
}
