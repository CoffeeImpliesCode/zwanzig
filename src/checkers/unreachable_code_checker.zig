const std = @import("std");
const checker_mod = @import("../checker.zig");
const Checker = checker_mod.Checker;
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const SourceRange = checker_mod.SourceRange;
const Source = @import("../source.zig").Source;
const ast_walk = @import("../ast_walk.zig");
const import_resolver = @import("../analysis/import_resolver.zig");
const LexicalIndex = @import("../analysis/lexical_index.zig").LexicalIndex;
const call_resolver = @import("../analysis/call_resolver.zig");
const value = @import("../engine/value.zig");
const ids = @import("../ids.zig");
const cfg_mod = @import("../cfg.zig");
const engine_mod = @import("../engine.zig");
const AnalysisEngine = engine_mod.AnalysisEngine;
const Constraint = engine_mod.Constraint;
const ConstraintManager = engine_mod.ConstraintManager;
const VarResolver = @import("../engine/var_resolver.zig").VarResolver;

/// Reports constant branches and contradictions under immutable scalar guards.
/// New path-sensitive reports require a complete analysis and an executed condition.
/// Only enclosing guards provide proof premises: arbitrary engine facts may be stale
/// after unsupported effects. The AST rule owns code after terminating statements.
pub const UnreachableCodeChecker = struct {
    pub const checker: Checker = .{
        .name = "unreachable-code-engine",
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
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);

        // Only a comptime scope can hold a compile-time assertion guard, so the
        // parent map that proves one is built when, and only when, the file
        // mentions `comptime` at all. The map is released by the scope that
        // built it, which ends once every check that reads it has run.
        if (hasComptimeKeyword(tree)) {
            const map = try allocator.alloc(u32, tags.len);
            defer if (map.len != 0) allocator.free(map);
            @memset(map, 0);
            for (tags, 0..) |tag, node| {
                switch (tag) {
                    .fn_decl,
                    .test_decl,
                    .simple_var_decl,
                    .local_var_decl,
                    .global_var_decl,
                    .aligned_var_decl,
                    .@"comptime",
                    => ast_walk.fillParentMap(tree, @intCast(node), map),
                    else => {},
                }
            }
            return try checkNodes(src, allocator, diagnostics, context, .{ .parents = map });
        }
        return try checkNodes(src, allocator, diagnostics, context, .{});
    }

    /// Every check the AST rule runs over one file, against what that file
    /// proves about its comptime scopes. A file that never writes `comptime`
    /// carries an empty context, which turns the assertion exemption off.
    fn checkNodes(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        context: checker_mod.CheckerContext,
        ct: ComptimeContext,
    ) CheckerError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);

        for (0..tags.len) |i| {
            const tag = tags[i];
            if (tag == .@"if" or tag == .if_simple) {
                try checkIfStatement(src, allocator, diagnostics, @intCast(i), ct);
            } else if (tag == .while_simple or tag == .while_cont or tag == .@"while") {
                try checkWhileStatement(src, allocator, diagnostics, @intCast(i), ct);
            }
        }

        for (tags, 0..) |tag, i| {
            if (tag == .fn_decl or tag == .test_decl) {
                try checkFunction(src, allocator, diagnostics, context, ids.astId(@intCast(i)));
            }
        }
    }

    const Scalar = enum { integer, boolean };
    const ScalarMap = std.AutoHashMap(ids.VarId, Scalar);
    const Guard = struct {
        point: ids.CfgNodeId,
        constraint: Constraint,
        then_node: u32,
        else_node: ?u32,
    };
    const GuardMap = std.AutoHashMap(u32, Guard);
    const Blocker = struct {
        premise: Constraint,
        blocks_true: bool,
        blocks_false: bool,
    };

    fn checkFunction(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        context: checker_mod.CheckerContext,
        fn_node: ids.AstNodeId,
    ) CheckerError!void {
        var cfg_handle = (context.getOrBuildCfg(allocator, src, fn_node) catch |err| switch (err) {
            error.OutOfMemory => return error.OutOfMemory,
            else => return,
        }) orelse return;
        defer cfg_handle.deinit();
        var condition_count: usize = 0;
        for (cfg_handle.cfg.nodes.items) |node| {
            if (node.ir_node.tag == .branch or node.ir_node.tag == .loop_header) {
                condition_count += 1;
            }
        }
        if (condition_count < 2) return;

        var analysis = try context.getOrAnalyze(allocator, src, &cfg_handle, checker.name, .configured);
        defer analysis.deinit();
        if (!analysis.complete) return;

        const engine = analysis.engine;
        const cfg = cfg_handle.cfg;
        const tree = try src.ast();
        const resolver = (try AnalysisEngine.VarResolution.getOrBuildVarResolver(engine, fn_node)) orelse return;
        var parameters = ScalarMap.init(allocator);
        defer parameters.deinit();
        try collectScalarParameters(tree, fn_node, &parameters);

        var guards = GuardMap.init(allocator);
        defer guards.deinit();
        for (cfg.nodes.items) |*node| {
            if (node.ir_node.tag != .branch and node.ir_node.tag != .loop_header) continue;
            const ast_node = node.ir_node.ast_node orelse continue;
            if (makeGuard(tree, engine, cfg, node, resolver, &parameters)) |guard| {
                try guards.put(ast_node, guard);
            }
        }
        if (guards.count() < 2) return;
        const parents = try engine.getParentMap(tree);
        var blockers: std.ArrayList(Blocker) = .empty;
        defer blockers.deinit(allocator);

        // CFG order visits enclosing branches first. Each condition uses the graph's
        // point index; neither branch bodies nor the whole graph are rescanned.
        for (cfg.nodes.items) |node| {
            const ast_node = node.ir_node.ast_node orelse continue;
            const guard = guards.get(ast_node) orelse continue;
            if (node.index != guard.point) continue;
            blockers.clearRetainingCapacity();
            try collectBlockers(allocator, ast_node, guard.constraint, parents, &guards, &blockers);
            if (blockers.items.len == 0) continue;

            const graph = engine.getGraph();
            const point = engine_mod.ProgramPoint.initPost(guard.point, cfg);
            const at_condition = graph.point_nodes.get(point.hash()) orelse continue;
            var executed = false;
            var impossible_true = true;
            var impossible_false = true;
            for (at_condition.items) |index| {
                const reached = graph.getNode(index) orelse continue;
                if (!reached.point.eql(point) or reached.state.inline_depth != 0) continue;
                if (!reached.state.isSatisfiable()) continue;
                executed = true;
                var blocked_true = false;
                var blocked_false = false;
                for (blockers.items) |blocker| {
                    if (!containsPremise(&reached.state.constraints, blocker.premise)) continue;
                    blocked_true = blocked_true or blocker.blocks_true;
                    blocked_false = blocked_false or blocker.blocks_false;
                }
                impossible_true = impossible_true and blocked_true;
                impossible_false = impossible_false and blocked_false;
            }
            // A missing post-node can mean a pruned predecessor or a noreturn call.
            // It is never evidence that this branch, or every statement in it, is dead.
            if (!executed) continue;
            if (impossible_true) {
                try reportInfeasibleBranch(src, allocator, diagnostics, guard.then_node);
            } else if (impossible_false) {
                if (guard.else_node) |else_node| {
                    try reportInfeasibleBranch(src, allocator, diagnostics, else_node);
                }
            }
        }
    }

    fn makeGuard(
        tree: *const std.zig.Ast,
        engine: *AnalysisEngine,
        cfg: *const cfg_mod.Cfg,
        node: *const cfg_mod.CfgNode,
        resolver: *const VarResolver,
        parameters: *const ScalarMap,
    ) ?Guard {
        const ast_node = node.ir_node.ast_node orelse return null;
        var condition: u32 = undefined;
        var then_node: u32 = undefined;
        var else_node: ?u32 = null;
        if (tree.fullIf(@enumFromInt(ast_node))) |full| {
            if (full.payload_token != null or full.error_token != null) return null;
            condition = @intFromEnum(full.ast.cond_expr);
            then_node = @intFromEnum(full.ast.then_expr);
            if (full.ast.else_expr.unwrap()) |other| else_node = @intFromEnum(other);
        } else if (tree.fullWhile(@enumFromInt(ast_node))) |full| {
            if (full.payload_token != null or full.error_token != null) return null;
            condition = @intFromEnum(full.ast.cond_expr);
            then_node = @intFromEnum(full.ast.then_expr);
        } else return null;
        // Constant diagnostics retain their existing messages and ranges.
        if (evaluateConditionValue(tree, condition) != null) return null;

        var negate = false;
        for (0..32) |_| {
            const data = tree.nodes.items(.data)[condition];
            switch (tree.nodes.items(.tag)[condition]) {
                .grouped_expression => condition = @intFromEnum(data.node_and_token[0]),
                .bool_not => {
                    negate = !negate;
                    condition = @intFromEnum(data.node);
                },
                else => break,
            }
        }
        const tag = tree.nodes.items(.tag)[condition];
        switch (tag) {
            .identifier,
            .equal_equal,
            .bang_equal,
            .less_than,
            .less_or_equal,
            .greater_than,
            .greater_or_equal,
            => {},
            else => return null,
        }
        var canonical_node = node.*;
        canonical_node.ir_node.operand_node = condition;
        var constraint = AnalysisEngine.BranchConstraints.extractBranchConstraint(engine, &canonical_node, cfg) orelse return null;
        const scalar: Scalar = switch (constraint) {
            .int_compare => .integer,
            .bool_check => if (tag == .identifier) .boolean else return null,
            else => return null,
        };
        const var_id = constraintVariable(constraint);
        if (!isImmutableScalar(tree, resolver, parameters, var_id, scalar, 0)) return null;
        if (negate) constraint = constraint.negate();
        return .{
            .point = node.index,
            .constraint = constraint,
            .then_node = then_node,
            .else_node = else_node,
        };
    }

    fn collectScalarParameters(tree: *const std.zig.Ast, fn_node: ids.AstNodeId, result: *ScalarMap) !void {
        const node = ids.astIndex(fn_node);
        if (tree.nodes.items(.tag)[node] != .fn_decl) return;
        const proto_node = tree.nodes.items(.data)[node].node_and_node[0];
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buffer, proto_node) orelse return;
        var parameters = proto.iterate(tree);
        while (parameters.next()) |parameter| {
            const name = parameter.name_token orelse continue;
            const type_node = parameter.type_expr orelse continue;
            const scalar = scalarType(tree, @intFromEnum(type_node)) orelse continue;
            try result.put(ids.varId(name), scalar);
        }
    }

    fn scalarType(tree: *const std.zig.Ast, node: u32) ?Scalar {
        if (tree.nodes.items(.tag)[node] != .identifier) return null;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[node]);
        if (std.mem.eql(u8, name, "bool")) return .boolean;
        if (std.mem.eql(u8, name, "usize") or std.mem.eql(u8, name, "isize") or
            std.mem.eql(u8, name, "comptime_int"))
        {
            return .integer;
        }
        if (name.len < 2 or (name[0] != 'i' and name[0] != 'u')) return null;
        for (name[1..]) |digit| {
            if (!std.ascii.isDigit(digit)) return null;
        }
        return .integer;
    }

    fn isImmutableScalar(
        tree: *const std.zig.Ast,
        resolver: *const VarResolver,
        parameters: *const ScalarMap,
        var_id: ids.VarId,
        scalar: Scalar,
        depth: u8,
    ) bool {
        if (depth == 16) return false;
        if (parameters.get(var_id)) |known| return scalar == known;
        const info = resolver.decl_mappings.get(var_id) orelse return false;
        if (info.is_top_level) return false;
        const full = tree.fullVarDecl(@enumFromInt(info.decl_node)) orelse return false;
        if (tree.tokens.items(.tag)[full.ast.mut_token] != .keyword_const) return false;
        if (full.ast.type_node.unwrap()) |type_node| {
            return scalar == (scalarType(tree, @intFromEnum(type_node)) orelse return false);
        }
        var init = @intFromEnum(full.ast.init_node.unwrap() orelse return false);
        for (0..16) |_| {
            if (tree.nodes.items(.tag)[init] != .grouped_expression) break;
            init = @intFromEnum(tree.nodes.items(.data)[init].node_and_token[0]);
        }
        if (value.evaluateBoolLiteral(tree, init) != null) return scalar == .boolean;
        if (parseIntLiteral(tree, init) != null) return scalar == .integer;
        if (tree.nodes.items(.tag)[init] != .identifier) return false;
        const original = resolver.resolve(init) orelse return false;
        return isImmutableScalar(tree, resolver, parameters, original, scalar, depth + 1);
    }

    fn constraintVariable(constraint: Constraint) ids.VarId {
        return switch (constraint) {
            .int_compare => |comparison| comparison.var_id,
            .bool_check => |check| check.var_id,
            else => unreachable,
        };
    }

    fn collectBlockers(
        allocator: std.mem.Allocator,
        ast_node: u32,
        constraint: Constraint,
        parents: []const u32,
        guards: *const GuardMap,
        result: *std.ArrayList(Blocker),
    ) !void {
        var child = ast_node;
        for (0..256) |_| {
            const parent = parents[child];
            if (parent == 0) return;
            if (guards.get(parent)) |guard| {
                const premise = if (child == guard.then_node)
                    guard.constraint
                else if (guard.else_node != null and child == guard.else_node.?)
                    guard.constraint.negate()
                else {
                    child = parent;
                    continue;
                };
                if (constraintVariable(premise) == constraintVariable(constraint)) {
                    const blocks_true = try contradicts(allocator, premise, constraint);
                    const blocks_false = try contradicts(allocator, premise, constraint.negate());
                    if (blocks_true or blocks_false) {
                        try result.append(allocator, .{
                            .premise = premise,
                            .blocks_true = blocks_true,
                            .blocks_false = blocks_false,
                        });
                    }
                }
            }
            child = parent;
        }
    }

    fn contradicts(allocator: std.mem.Allocator, premise: Constraint, branch: Constraint) !bool {
        var constraints = ConstraintManager.init(allocator);
        defer constraints.deinit();
        try constraints.addConstraint(premise);
        try constraints.addConstraint(branch);
        // Do not consult abstract values: calls and assignments can invalidate them.
        // The canonical constraint index checks these two immutable guard premises.
        return constraints.has_contradiction;
    }

    fn containsPremise(constraints: *const ConstraintManager, premise: Constraint) bool {
        const indexed = constraints.per_var_constraints.get(constraintVariable(premise)) orelse return false;
        const candidates = switch (premise) {
            .int_compare => indexed.int_constraints.items,
            .bool_check => indexed.bool_constraints.items,
            else => unreachable,
        };
        for (candidates) |candidate| {
            if (candidate.eql(premise)) return true;
        }
        return false;
    }

    fn reportInfeasibleBranch(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        body: u32,
    ) !void {
        const range = (try getNodeRange(src, body)) orelse return;
        for (diagnostics.items) |diag| {
            if (!std.mem.eql(u8, diag.rule_id, checker.name) and
                !std.mem.eql(u8, diag.rule_id, "unreachable-code"))
            {
                continue;
            }
            if (!std.mem.eql(u8, diag.file_path, src.getFilePath())) continue;
            if (!locationBefore(range.end, diag.range.start) and
                !locationBefore(diag.range.end, range.start))
            {
                return;
            }
        }
        var diag = try Diagnostic.init(
            allocator,
            src.getFilePath(),
            checker.name,
            .warning,
            "unreachable code: branch contradicts an enclosing condition",
            range,
        );
        errdefer diag.deinit(allocator);
        try diagnostics.append(allocator, diag);
    }

    fn locationBefore(lhs: checker_mod.Location, rhs: checker_mod.Location) bool {
        return lhs.line < rhs.line or (lhs.line == rhs.line and lhs.column < rhs.column);
    }

    fn checkIfStatement(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        if_node: u32,
        ct: ComptimeContext,
    ) CheckerError!void {
        const tree = try src.ast();
        const full_if = tree.fullIf(@enumFromInt(if_node)) orelse return;

        const cond_node: u32 = @intFromEnum(full_if.ast.cond_expr);
        const cond_value = evaluateConditionValue(tree, cond_node);

        if (cond_value) |is_true| {
            if (is_true) {
                if (full_if.ast.else_expr.unwrap()) |else_expr| {
                    const else_node: u32 = @intFromEnum(else_expr);
                    const range = try getNodeRange(src, else_node);
                    if (range) |r| {
                        var diag = try Diagnostic.init(
                            allocator,
                            src.getFilePath(),
                            "unreachable-code-engine",
                            .warning,
                            "unreachable code: else branch is never executed because condition is always true",
                            r,
                        );
                        errdefer diag.deinit(allocator);
                        try diagnostics.append(allocator, diag);
                    }
                }
            } else {
                const then_node: u32 = @intFromEnum(full_if.ast.then_expr);
                if (isComptimeAssertionGuard(
                    src,
                    tree,
                    ct,
                    full_if.ast.else_expr.unwrap() == null,
                    then_node,
                )) return;
                const range = try getNodeRange(src, then_node);
                if (range) |r| {
                    var diag = try Diagnostic.init(
                        allocator,
                        src.getFilePath(),
                        "unreachable-code-engine",
                        .warning,
                        "unreachable code: if body is never executed because condition is always false",
                        r,
                    );
                    errdefer diag.deinit(allocator);
                    try diagnostics.append(allocator, diag);
                }
            }
        }
    }

    fn checkWhileStatement(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        while_node: u32,
        ct: ComptimeContext,
    ) CheckerError!void {
        const tree = try src.ast();
        const full_while = tree.fullWhile(@enumFromInt(while_node)) orelse return;

        const cond_node: u32 = @intFromEnum(full_while.ast.cond_expr);
        const cond_value = evaluateConditionValue(tree, cond_node);

        if (cond_value) |is_true| {
            if (!is_true) {
                const body_node: u32 = @intFromEnum(full_while.ast.then_expr);
                if (isComptimeAssertionGuard(
                    src,
                    tree,
                    ct,
                    full_while.ast.cont_expr.unwrap() == null and
                        full_while.ast.else_expr.unwrap() == null,
                    body_node,
                )) return;
                const range = try getNodeRange(src, body_node);
                if (range) |r| {
                    var diag = try Diagnostic.init(
                        allocator,
                        src.getFilePath(),
                        "unreachable-code-engine",
                        .warning,
                        "unreachable code: while body is never executed because condition is always false",
                        r,
                    );
                    errdefer diag.deinit(allocator);
                    try diagnostics.append(allocator, diag);
                }
            }
        }
    }

    /// What one file can prove about its comptime scopes.
    ///
    /// `parents` is empty when the file never writes `comptime`, which turns
    /// the assertion exemption off for the whole file and costs no allocation.
    const ComptimeContext = struct {
        parents: []const u32 = &.{},
    };

    /// A file that never writes the `comptime` keyword cannot hold a
    /// compile-time assertion, so the parent map that proves one is skipped.
    fn hasComptimeKeyword(tree: *const std.zig.Ast) bool {
        for (tree.tokens.items(.tag)) |tag| {
            if (tag == .keyword_comptime) return true;
        }
        return false;
    }

    /// Lexical index for this tree, borrowed from the source that parsed it.
    fn lexicalIndexFor(src: *Source, tree: *const std.zig.Ast) ?*const LexicalIndex {
        const source_tree = src.ast() catch return null;
        if (tree != source_tree) return null;
        return src.lexicalIndex() catch null;
    }

    /// Proven `@import("std")` binding for an expression, through the project's
    /// own resolver. A user module spelled `std`, a `var` binding, and a local
    /// that shadows the name all fail, because none of them resolves to a
    /// declaration whose initializer is that import. The answer comes from a
    /// single resolution: a malformed file has no lexical index and yields no
    /// binding, so it proves nothing either.
    fn isVerifiedStdImport(src: *Source, tree: *const std.zig.Ast, node: u32) bool {
        if (node >= tree.nodes.items(.tag).len) return false;
        const files = [_]import_resolver.File{.{
            .path = src.getFilePath(),
            .tree = tree,
            .lexical_index = lexicalIndexFor(src, tree),
        }};
        const resolver = call_resolver.ProjectTypeResolver{ .files = &files, .file_index = 0 };
        return resolver.isVerifiedImportBinding(node, "std");
    }

    /// A constant-false branch inside a comptime scope whose body only asserts
    /// is a compile-time invariant guard, not dead application logic: the
    /// branch never runs because the invariant currently holds, and deleting
    /// it would drop the check against a future change that breaks it.
    ///
    /// Both halves are required. The comptime scope keeps an ordinary dead
    /// runtime branch reportable, and the assertion-only body keeps a comptime
    /// branch that runs real logic reportable.
    fn isComptimeAssertionGuard(
        src: *Source,
        tree: *const std.zig.Ast,
        ct: ComptimeContext,
        unconditional_shape: bool,
        body: u32,
    ) bool {
        if (ct.parents.len == 0) return false;
        if (!unconditional_shape) return false;
        if (!isInsideComptimeScope(tree, ct.parents, body)) return false;
        return isAssertionOnlyBody(src, tree, body);
    }

    /// True when the branch is written inside a `comptime` scope. A function
    /// or test body is runtime code even when its own constants are known, so
    /// the walk stops there.
    fn isInsideComptimeScope(
        tree: *const std.zig.Ast,
        comptime_parents: []const u32,
        node: u32,
    ) bool {
        const tags = tree.nodes.items(.tag);
        var current = node;
        var depth: u32 = 0;
        while (depth < 64) : (depth += 1) {
            if (current >= comptime_parents.len) return false;
            const parent = comptime_parents[current];
            if (parent == 0 or parent >= tags.len) return false;
            switch (tags[parent]) {
                .@"comptime" => return true,
                .fn_decl, .test_decl => return false,
                .simple_var_decl,
                .local_var_decl,
                .global_var_decl,
                .aligned_var_decl,
                => {
                    const declaration = tree.fullVarDecl(@enumFromInt(parent)) orelse return false;
                    if (declaration.comptime_token != null) return true;
                },
                else => {},
            }
            current = parent;
        }
        return false;
    }

    /// True when every statement of the branch body is a compile-time
    /// assertion. An empty body asserts nothing.
    fn isAssertionOnlyBody(src: *Source, tree: *const std.zig.Ast, body: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (body >= tags.len) return false;
        switch (tags[body]) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => {
                var buffer: [2]u32 = undefined;
                const statements = ast_walk.getBlockStatements(tree, body, &buffer) orelse return false;
                if (statements.len == 0) return false;
                for (statements) |statement| {
                    if (!isCompileTimeAssertion(src, tree, statement)) return false;
                }
                return true;
            },
            else => return isCompileTimeAssertion(src, tree, body),
        }
    }

    /// `@compileError(...)` stops the build when the branch is taken, and the
    /// real `std.debug.assert(...)` inside a comptime scope stops it for the
    /// same reason. Both assert an invariant rather than run application logic.
    fn isCompileTimeAssertion(src: *Source, tree: *const std.zig.Ast, node: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (node == 0 or node >= tags.len) return false;
        const token_tags = tree.tokens.items(.tag);
        switch (tags[node]) {
            .grouped_expression => return isCompileTimeAssertion(
                src,
                tree,
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
            ),
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                const token = tree.nodes.items(.main_token)[node];
                if (token >= token_tags.len or token_tags[token] != .builtin) return false;
                return std.mem.eql(u8, tree.tokenSlice(token), "@compileError");
            },
            .call, .call_comma, .call_one, .call_one_comma => {
                var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
                const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return false;
                return isDebugAssertCallee(src, tree, @intFromEnum(call.ast.fn_expr));
            },
            else => return false,
        }
    }

    /// True when the callee is `std.debug.assert` reached through a `std` the
    /// file binds to `@import("std")`. The chain is read as
    /// `std` `.` `debug` `.` `assert`, and the base expression must resolve to
    /// that import, so a user module or a shadowing local spelled `std` does
    /// not match. An alias of the assertion is deliberately not accepted: it is
    /// a different spelling that would need its own resolution.
    fn isDebugAssertCallee(src: *Source, tree: *const std.zig.Ast, callee: u32) bool {
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (callee >= tags.len or tags[callee] != .field_access) return false;
        const assert_access = datas[callee].node_and_token;
        if (!segmentMatches(tree, assert_access[1], "assert")) return false;
        const debug_node = @intFromEnum(assert_access[0]);
        if (debug_node >= tags.len or tags[debug_node] != .field_access) return false;
        const debug_access = datas[debug_node].node_and_token;
        if (!segmentMatches(tree, debug_access[1], "debug")) return false;
        return isVerifiedStdImport(src, tree, @intFromEnum(debug_access[0]));
    }

    fn segmentMatches(tree: *const std.zig.Ast, token: u32, name: []const u8) bool {
        const token_tags = tree.tokens.items(.tag);
        if (token >= token_tags.len or token_tags[token] != .identifier) return false;
        return std.mem.eql(u8, tree.tokenSlice(token), name);
    }

    fn evaluateConditionValue(tree: *const std.zig.Ast, cond_node: u32) ?bool {
        return evaluateConstBool(tree, cond_node, 0);
    }

    fn evaluateConstBool(tree: *const std.zig.Ast, node: u32, depth: u8) ?bool {
        if (depth > 8) return null;

        if (value.evaluateBoolLiteral(tree, node)) |literal| {
            return literal;
        }

        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;
        const tag = tags[node];
        const datas = tree.nodes.items(.data);

        return switch (tag) {
            .identifier => blk: {
                const init_node = resolveConstInitNode(tree, node) orelse break :blk null;
                break :blk evaluateConstBool(tree, init_node, depth + 1);
            },
            .grouped_expression => blk: {
                const child = @intFromEnum(datas[node].node_and_token[0]);
                if (child == 0) break :blk null;
                break :blk evaluateConstBool(tree, child, depth + 1);
            },
            .bool_not => blk: {
                const child = @intFromEnum(datas[node].node);
                if (child == 0) break :blk null;
                const child_val = evaluateConstBool(tree, child, depth + 1) orelse break :blk null;
                break :blk !child_val;
            },
            .bool_and, .bool_or => blk: {
                const pair = datas[node].node_and_node;
                const lhs = @intFromEnum(pair[0]);
                const rhs = @intFromEnum(pair[1]);
                const lhs_val = evaluateConstBool(tree, lhs, depth + 1);
                if (lhs_val) |val| {
                    if (tag == .bool_and and !val) break :blk false;
                    if (tag == .bool_or and val) break :blk true;
                }
                const rhs_val = evaluateConstBool(tree, rhs, depth + 1);
                if (rhs_val) |val| {
                    if (tag == .bool_and and !val) break :blk false;
                    if (tag == .bool_or and val) break :blk true;
                }
                if (lhs_val == null or rhs_val == null) break :blk null;
                if (tag == .bool_and) break :blk lhs_val.? and rhs_val.?;
                break :blk lhs_val.? or rhs_val.?;
            },
            .equal_equal, .bang_equal => blk: {
                const pair = datas[node].node_and_node;
                const lhs = @intFromEnum(pair[0]);
                const rhs = @intFromEnum(pair[1]);

                if (evaluateConstInt(tree, lhs, depth + 1)) |lhs_int| {
                    if (evaluateConstInt(tree, rhs, depth + 1)) |rhs_int| {
                        const eq = lhs_int == rhs_int;
                        break :blk if (tag == .equal_equal) eq else !eq;
                    }
                }

                const lhs_bool = evaluateConstBool(tree, lhs, depth + 1) orelse break :blk null;
                const rhs_bool = evaluateConstBool(tree, rhs, depth + 1) orelse break :blk null;
                const eq = lhs_bool == rhs_bool;
                break :blk if (tag == .equal_equal) eq else !eq;
            },
            .less_than, .less_or_equal, .greater_than, .greater_or_equal => blk: {
                const pair = datas[node].node_and_node;
                const lhs = @intFromEnum(pair[0]);
                const rhs = @intFromEnum(pair[1]);
                const lhs_int = evaluateConstInt(tree, lhs, depth + 1) orelse break :blk null;
                const rhs_int = evaluateConstInt(tree, rhs, depth + 1) orelse break :blk null;
                break :blk switch (tag) {
                    .less_than => lhs_int < rhs_int,
                    .less_or_equal => lhs_int <= rhs_int,
                    .greater_than => lhs_int > rhs_int,
                    .greater_or_equal => lhs_int >= rhs_int,
                    else => null,
                };
            },
            else => null,
        };
    }

    fn evaluateConstInt(tree: *const std.zig.Ast, node: u32, depth: u8) ?i64 {
        if (depth > 8) return null;

        if (parseIntLiteral(tree, node)) |literal| {
            return literal;
        }

        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;
        const tag = tags[node];
        const datas = tree.nodes.items(.data);

        return switch (tag) {
            .identifier => blk: {
                const init_node = resolveConstInitNode(tree, node) orelse break :blk null;
                break :blk evaluateConstInt(tree, init_node, depth + 1);
            },
            .grouped_expression => blk: {
                const child = @intFromEnum(datas[node].node_and_token[0]);
                if (child == 0) break :blk null;
                break :blk evaluateConstInt(tree, child, depth + 1);
            },
            .negation => blk: {
                const child = @intFromEnum(datas[node].node);
                if (child == 0) break :blk null;
                const child_val = evaluateConstInt(tree, child, depth + 1) orelse break :blk null;
                if (child_val == std.math.minInt(i64)) break :blk null;
                break :blk -child_val;
            },
            .add, .sub, .mul, .div, .mod => blk: {
                const pair = datas[node].node_and_node;
                const lhs = @intFromEnum(pair[0]);
                const rhs = @intFromEnum(pair[1]);
                const lhs_val = evaluateConstInt(tree, lhs, depth + 1) orelse break :blk null;
                const rhs_val = evaluateConstInt(tree, rhs, depth + 1) orelse break :blk null;

                break :blk switch (tag) {
                    .add => blk_add: {
                        const sum = @addWithOverflow(lhs_val, rhs_val);
                        if (sum[1] != 0) break :blk_add null;
                        break :blk_add sum[0];
                    },
                    .sub => blk_sub: {
                        const diff = @subWithOverflow(lhs_val, rhs_val);
                        if (diff[1] != 0) break :blk_sub null;
                        break :blk_sub diff[0];
                    },
                    .mul => blk_mul: {
                        const prod = @mulWithOverflow(lhs_val, rhs_val);
                        if (prod[1] != 0) break :blk_mul null;
                        break :blk_mul prod[0];
                    },
                    .div => if (rhs_val == 0) null else @divTrunc(lhs_val, rhs_val),
                    .mod => if (rhs_val == 0) null else @mod(lhs_val, rhs_val),
                    else => null,
                };
            },
            else => null,
        };
    }

    fn resolveConstInitNode(tree: *const std.zig.Ast, ident_node: u32) ?u32 {
        const tags = tree.nodes.items(.tag);
        if (ident_node >= tags.len) return null;
        if (tags[ident_node] != .identifier) return null;

        const main_tokens = tree.nodes.items(.main_token);
        const token_tags = tree.tokens.items(.tag);
        const ident_token = main_tokens[ident_node];
        if (ident_token >= token_tags.len) return null;
        if (token_tags[ident_token] != .identifier) return null;
        const ident_name = tree.tokenSlice(ident_token);

        var i: usize = ident_node;
        while (i > 0) {
            i -= 1;
            const node_tag = tags[i];
            if (node_tag == .fn_decl) break;
            if (node_tag != .simple_var_decl and node_tag != .local_var_decl) continue;

            const var_decl = tree.fullVarDecl(@enumFromInt(@as(u32, @intCast(i)))) orelse continue;
            const decl_token = tree.tokens.items(.tag)[var_decl.ast.mut_token];
            if (decl_token != .keyword_const) continue;

            const name_token = var_decl.ast.mut_token + 1;
            if (name_token >= tree.tokens.items(.start).len) continue;
            const decl_name = tree.tokenSlice(name_token);
            if (!std.mem.eql(u8, ident_name, decl_name)) continue;

            const init_node = var_decl.ast.init_node.unwrap() orelse continue;
            return @intFromEnum(init_node);
        }

        return null;
    }

    fn parseIntLiteral(tree: *const std.zig.Ast, node: u32) ?i64 {
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;
        if (tags[node] != .number_literal) return null;

        const main_tokens = tree.nodes.items(.main_token);
        const token = main_tokens[node];
        const token_str = tree.tokenSlice(token);
        if (token_str.len == 0) return null;

        for (token_str) |c| {
            if (c == '.' or c == 'e' or c == 'E' or c == 'p' or c == 'P') return null;
            if (!std.ascii.isDigit(c) and c != '_' and c != 'x' and c != 'X' and
                c != 'b' and c != 'B' and c != 'o' and c != 'O' and
                !(c >= 'a' and c <= 'f') and !(c >= 'A' and c <= 'F'))
            {
                return null;
            }
        }

        var clean_buf: [64]u8 = undefined;
        var clean_len: usize = 0;
        for (token_str) |c| {
            if (c == '_') continue;
            if (clean_len >= clean_buf.len) return null;
            clean_buf[clean_len] = c;
            clean_len += 1;
        }
        if (clean_len == 0) return null;

        const clean_str = clean_buf[0..clean_len];
        var digits = clean_str;
        var base: i64 = 10;
        if (clean_len >= 2 and clean_buf[0] == '0') {
            if (clean_buf[1] == 'x' or clean_buf[1] == 'X') {
                base = 16;
                digits = clean_str[2..];
            } else if (clean_buf[1] == 'b' or clean_buf[1] == 'B') {
                base = 2;
                digits = clean_str[2..];
            } else if (clean_buf[1] == 'o' or clean_buf[1] == 'O') {
                base = 8;
                digits = clean_str[2..];
            }
        }
        if (digits.len == 0) return null;

        var result: i64 = 0;
        for (digits) |c| {
            const digit: i64 = switch (c) {
                '0'...'9' => @intCast(c - '0'),
                'a'...'f' => @intCast(10 + (c - 'a')),
                'A'...'F' => @intCast(10 + (c - 'A')),
                else => return null,
            };
            if (digit >= base) return null;
            const mul = @mulWithOverflow(result, base);
            if (mul[1] != 0) return null;
            const sum = @addWithOverflow(mul[0], digit);
            if (sum[1] != 0) return null;
            result = sum[0];
        }
        return result;
    }

    fn getNodeRange(src: *Source, node: u32) !?SourceRange {
        const tree = try src.ast();
        const main_tokens = tree.nodes.items(.main_token);
        const token_starts = tree.tokens.items(.start);

        if (node >= main_tokens.len) return null;

        const first_token = tree.firstToken(@enumFromInt(node));
        const last_token = tree.lastToken(@enumFromInt(node));

        if (first_token >= token_starts.len or last_token >= token_starts.len) return null;

        const start_byte = token_starts[first_token];
        const end_byte = token_starts[last_token] + tokenLen(tree, last_token);

        return try src.byteRangeToSourceRange(start_byte, end_byte);
    }

    fn tokenLen(tree: *const std.zig.Ast, token: u32) u32 {
        const token_starts = tree.tokens.items(.start);
        const token_tags = tree.tokens.items(.tag);

        if (token + 1 < token_starts.len) {
            return token_starts[token + 1] - token_starts[token];
        }

        const tag = token_tags[token];
        return switch (tag) {
            .identifier => blk: {
                const start = token_starts[token];
                var len: u32 = 0;
                const source = tree.source;
                while (start + len < source.len) {
                    const c = source[start + len];
                    if (!std.ascii.isAlphanumeric(c) and c != '_') break;
                    len += 1;
                }
                break :blk len;
            },
            else => 1,
        };
    }
};

test "unreachable_code_engine - constant emission propagates allocation failures" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "constant-oom.zig",
        \\fn sample() void {
        \\    if (true) {} else { dead(); }
        \\    if (false) { dead(); }
        \\    while (false) { dead(); }
        \\}
    );
    defer source.deinit();
    const tree = try source.ast();
    const Harness = struct {
        fn run(
            memory: std.mem.Allocator,
            ast: *const std.zig.Ast,
            node: u32,
            line: usize,
        ) !void {
            var input = Source.initParsed(memory, "constant-oom.zig", ast);
            defer input.deinit();
            var diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer {
                for (diagnostics.items) |*diagnostic| diagnostic.deinit(memory);
                diagnostics.deinit(memory);
            }
            // The fixture has no `comptime` keyword, so the exemption's context
            // is empty and the constant emission owns every allocation.
            switch (ast.nodes.items(.tag)[node]) {
                .@"if", .if_simple => try UnreachableCodeChecker.checkIfStatement(
                    &input,
                    memory,
                    &diagnostics,
                    node,
                    .{},
                ),
                .@"while", .while_simple, .while_cont => try UnreachableCodeChecker.checkWhileStatement(
                    &input,
                    memory,
                    &diagnostics,
                    node,
                    .{},
                ),
                else => unreachable,
            }
            try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
            try std.testing.expectEqual(line, diagnostics.items[0].range.start.line);
        }
    };
    var line: usize = 2;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        switch (tag) {
            .@"if", .if_simple, .@"while", .while_simple, .while_cont => {
                try std.testing.checkAllAllocationFailures(
                    allocator,
                    Harness.run,
                    .{ tree, @as(u32, @intCast(index)), line },
                );
                line += 1;
            },
            else => {},
        }
    }
}

test "unreachable_code_engine - comptime assertion guards are not dead code" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\comptime {
        \\    const guard_limit: usize = 80;
        \\    const guard_worst_case: usize = 77;
        \\    if (guard_worst_case > guard_limit) {
        \\        @compileError("max_control_bytes must hold the worst-case control sequence");
        \\    }
        \\}
        \\comptime {
        \\    if (77 > 80) {
        \\        std.debug.assert(77 <= 80);
        \\    }
        \\}
        \\comptime {
        \\    while (false) {
        \\        @compileError("the loop must never be entered");
        \\    }
        \\}
        \\comptime {
        \\    const dead_flag: bool = false;
        \\    if (dead_flag) {
        \\        std.debug.print("unreachable feature\n", .{});
        \\    }
        \\}
        \\fn scale(value: u8) u8 {
        \\    const unsupported: bool = false;
        \\    if (unsupported) {
        \\        @compileError("an assertion outside comptime is dead code");
        \\    }
        \\    return value;
        \\}
        \\fn shadowedStd(value: u8) u8 {
        \\    const std = struct {
        \\        pub const debug = struct {
        \\            pub fn assert(ok: bool) void {
        \\                if (!ok) @panic("fake assertion");
        \\            }
        \\        };
        \\    };
        \\    comptime {
        \\        const limit: usize = 80;
        \\        const worst: usize = 77;
        \\        if (worst > limit) {
        \\            std.debug.assert(worst <= limit);
        \\        }
        \\    }
        \\    return value;
        \\}
        \\fn mutableAssertAlias(value: u8) u8 {
        \\    var assert = std.debug.assert;
        \\    defer assert = std.debug.assert;
        \\    comptime {
        \\        const limit: usize = 80;
        \\        const worst: usize = 77;
        \\        if (worst > limit) {
        \\            assert(worst <= limit);
        \\        }
        \\    }
        \\    return value;
        \\}
    ;
    // Only the branches that do not assert a real invariant are reported: the
    // comptime branch that runs real logic, the assertion outside any comptime
    // scope, the call through a `std` the file does not bind, and the call
    // through an alias.
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{ 21, 27, 43, 55 });
}

test "unreachable_code_engine - a user module spelled std names no assertion" {
    const code: [:0]const u8 =
        \\const std = struct {
        \\    pub const debug = struct {
        \\        pub fn assert(ok: bool) void {
        \\            if (!ok) @panic("fake assertion");
        \\        }
        \\    };
        \\};
        \\comptime {
        \\    const limit: usize = 80;
        \\    const worst: usize = 77;
        \\    if (worst > limit) {
        \\        std.debug.assert(worst <= limit);
        \\    }
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{11});
}

test "unreachable_code_engine - comptime parent map propagates allocation failures" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "comptime-oom.zig",
        \\const std = @import("std");
        \\comptime {
        \\    const limit: usize = 80;
        \\    if (77 > limit) {
        \\        @compileError("capacity guard");
        \\    }
        \\}
        \\comptime {
        \\    const dead: bool = false;
        \\    if (dead) {
        \\        std.debug.print("dead\n", .{});
        \\    }
        \\}
    );
    defer source.deinit();
    const tree = try source.ast();
    const Harness = struct {
        fn run(memory: std.mem.Allocator, ast: *const std.zig.Ast) !void {
            var input = Source.initParsed(memory, "comptime-oom.zig", ast);
            defer input.deinit();
            var diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer {
                for (diagnostics.items) |*diagnostic| diagnostic.deinit(memory);
                diagnostics.deinit(memory);
            }
            try UnreachableCodeChecker.checker.checkAst(
                &input,
                memory,
                &diagnostics,
                .{ .build_metadata = null },
            );
            try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
            // The report covers the then-block, whose first token is the `{`
            // that opens it on the `if` line, not the statement inside it.
            try std.testing.expectEqual(@as(usize, 10), diagnostics.items[0].range.start.line);
        }
    };
    try std.testing.checkAllAllocationFailures(allocator, Harness.run, .{tree});
}

fn expectUnreachableLines(
    code: [:0]const u8,
    context: checker_mod.CheckerContext,
    expected_lines: []const usize,
) !void {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |*diag| diag.deinit(allocator);

    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);
    try std.testing.expectEqual(expected_lines.len, diagnostics.items.len);
    for (expected_lines) |line| {
        var matches: usize = 0;
        for (diagnostics.items) |diag| {
            if (diag.range.start.line == line) matches += 1;
        }
        try std.testing.expectEqual(@as(usize, 1), matches);
    }
}

test "unreachable_code_engine - contradictory immutable integer guards" {
    const code: [:0]const u8 =
        \\fn foo(input: i32) i32 {
        \\    const value = input;
        \\    if (0 < value) {
        \\        if (value <= 0) {
        \\            const dead = value + 1;
        \\            return dead;
        \\        }
        \\        while (value < 0) {
        \\            return 2;
        \\        }
        \\    }
        \\    return 0;
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{ 4, 8 });
}

test "unreachable_code_engine - contradictory immutable boolean guards" {
    const code: [:0]const u8 =
        \\fn foo(flag: bool) i32 {
        \\    if (flag) {
        \\        if (!flag) {
        \\            return 1;
        \\        }
        \\        if (flag) {
        \\            return 2;
        \\        } else {
        \\            return 3;
        \\        }
        \\    }
        \\    return 0;
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{ 3, 8 });
}

test "unreachable_code_engine - reachable paths are not dead regions" {
    const code: [:0]const u8 =
        \\fn foo(value: i32, flag: bool) i32 {
        \\    if (value > 0) {
        \\        if (value == 1) return 1;
        \\        if (flag) return 2;
        \\    }
        \\    if (value < 0) return 3;
        \\    return 0;
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{});
}

test "unreachable_code_engine - mutation does not prove a branch impossible" {
    const code: [:0]const u8 =
        \\extern fn mutate(pointer: *i32) void;
        \\fn throughPointer(pointer: *i32) i32 {
        \\    if (pointer.* > 0) {
        \\        mutate(pointer);
        \\        if (pointer.* < 0) return 1;
        \\    }
        \\    return 0;
        \\}
        \\fn throughAlias(input: i32) i32 {
        \\    var value = input;
        \\    if (value > 0) {
        \\        mutate(&value);
        \\        if (value < 0) return 1;
        \\    }
        \\    return 0;
        \\}
        \\fn reassigned(input: i32) i32 {
        \\    var value = input;
        \\    if (value > 0) {
        \\        value = -1;
        \\        if (value < 0) return 1;
        \\    }
        \\    return 0;
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{});
}

test "unreachable_code_engine - unrelated effects preserve immutable guards" {
    const code: [:0]const u8 =
        \\extern fn mutate(pointer: *i32) void;
        \\fn foo(value: i32, pointer: *i32) i32 {
        \\    if (value > 0) {
        \\        mutate(pointer);
        \\        if (value < 0) return 1;
        \\    }
        \\    return 0;
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{5});
}

test "unreachable_code_engine - unsupported floating point guards stay unknown" {
    const code: [:0]const u8 =
        \\fn foo(value: f64) i32 {
        \\    if (value < 0) {
        \\        return 0;
        \\    } else {
        \\        if (value >= 0) return 1;
        \\        return 2;
        \\    }
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{});
}

test "unreachable_code_engine - dead calls and noreturn calls are not evidence" {
    const code: [:0]const u8 =
        \\fn stop() noreturn { unreachable; }
        \\fn reached(flag: bool) void {
        \\    if (flag) { stop(); }
        \\}
        \\fn stopped(value: i32) i32 {
        \\    if (value > 0) {
        \\        stop();
        \\        if (value < 0) return 1;
        \\    }
        \\    return 0;
        \\}
        \\fn returned(value: i32) i32 {
        \\    if (value > 0) {
        \\        return 1;
        \\        if (value < 0) return 2;
        \\    }
        \\    return 0;
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{});
}

test "unreachable_code_engine - incomplete analyses preserve constant-only results" {
    const code: [:0]const u8 =
        \\fn foo(value: i32) i32 {
        \\    if (false) return 1;
        \\    if (value > 0) {
        \\        if (value < 0) return 2;
        \\    }
        \\    return 0;
        \\}
    ;
    try expectUnreachableLines(code, .{
        .build_metadata = null,
        .analysis_limits = .{ .max_worklist_steps = 1 },
    }, &.{2});
    try expectUnreachableLines(code, .{
        .build_metadata = null,
        .analysis_limits = .{ .max_states_per_point = 0 },
    }, &.{2});
}

test "unreachable_code_engine - constant branches do not gain duplicate reports" {
    const code: [:0]const u8 =
        \\fn foo(value: i32) i32 {
        \\    if (false) {
        \\        if (value > 0) {
        \\            if (value < 0) return 1;
        \\        }
        \\    }
        \\    if (value > 0) {
        \\        if (true) {
        \\            return 2;
        \\        } else {
        \\            if (value < 0) return 3;
        \\        }
        \\    }
        \\    return 0;
        \\}
    ;
    try expectUnreachableLines(code, .{ .build_metadata = null }, &.{ 2, 10 });
}

test "unreachable_code_engine - AST terminator reports own overlapping regions" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\fn foo(value: i32) i32 {
        \\    if (value > 0) {
        \\        if (value < 0) {
        \\            return 1;
        \\            consume(value);
        \\        }
        \\    }
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |*diag| diag.deinit(allocator);

    const ast_rule = @import("../rules/unreachable_code.zig").UnreachableCodeRule.rule;
    try ast_rule.check(&source, allocator, &diagnostics);
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, .{ .build_metadata = null });
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("unreachable-code", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 5), diagnostics.items[0].range.start.line);
}

test "unreachable_code_engine - detects if(false) body" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() i32 {
        \\    if (false) {
        \\        return 1;
        \\    }
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("unreachable-code-engine", diagnostics.items[0].rule_id);
}

test "unreachable_code_engine - detects if(true) else branch" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() i32 {
        \\    if (true) {
        \\        return 1;
        \\    } else {
        \\        return 0;
        \\    }
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("unreachable-code-engine", diagnostics.items[0].rule_id);
}

test "unreachable_code_engine - detects while(false) body" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() i32 {
        \\    while (false) {
        \\        return 1;
        \\    }
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("unreachable-code-engine", diagnostics.items[0].rule_id);
}

test "unreachable_code_engine - no diagnostic for runtime condition" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo(x: bool) i32 {
        \\    if (x) {
        \\        return 1;
        \\    }
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "unreachable_code_engine - no diagnostic for empty function" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() void {}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "unreachable_code_engine - no diagnostic for while(true) as it's a legitimate infinite loop" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() noreturn {
        \\    while (true) {}
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "unreachable_code_engine - detects nested if(false)" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo(x: bool) i32 {
        \\    if (x) {
        \\        if (false) {
        \\            return 1;
        \\        }
        \\        return 2;
        \\    }
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
}

test "unreachable_code_engine - no false positive for identifiers starting with true/false" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo(trueValue: bool) i32 {
        \\    if (trueValue) {
        \\        return 1;
        \\    } else {
        \\        return 0;
        \\    }
        \\}
        \\fn bar(falsey: bool) i32 {
        \\    if (falsey) {
        \\        return 1;
        \\    }
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "unreachable_code_engine - detects const flag false" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() i32 {
        \\    const debug = false;
        \\    if (debug) {
        \\        return 1;
        \\    }
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("unreachable-code-engine", diagnostics.items[0].rule_id);
}

test "unreachable_code_engine - detects const flag true else branch" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() i32 {
        \\    const enabled = true;
        \\    if (enabled) {
        \\        return 1;
        \\    } else {
        \\        return 0;
        \\    }
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try testing.expectEqualStrings("unreachable-code-engine", diagnostics.items[0].rule_id);
}

test "unreachable_code_engine - no warning for var flag (may be reassigned)" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo(cond: bool) i32 {
        \\    var flag = true;
        \\    if (cond) flag = false;
        \\    if (flag) return 1;
        \\    return 0;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer diagnostics.deinit(allocator);
    defer for (diagnostics.items) |diag| allocator.free(@constCast(diag.message));

    const context = checker_mod.CheckerContext{ .build_metadata = null };
    try UnreachableCodeChecker.checker.checkAst(&source, allocator, &diagnostics, context);

    try testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}
