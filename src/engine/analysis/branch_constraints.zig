const std = @import("std");
const assertions = @import("../../assertions.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const ids = @import("../../ids.zig");
const Cfg = @import("../../cfg.zig").Cfg;
const CfgNode = @import("../../cfg.zig").CfgNode;
const Constraint = @import("../constraints.zig").Constraint;
const CompareOp = @import("../constraints.zig").CompareOp;
const TypeInfo = @import("../../type_context.zig").TypeInfo;
const ZirBridge = @import("../../zir_bridge.zig").ZirBridge;

pub fn Mixin(comptime _Engine: type) type {
    return struct {
        pub fn getAssertionScope(self: *_Engine, current_cfg: *const Cfg) std.mem.Allocator.Error!?*assertions.AssertionScope {
            const fn_node = current_cfg.fn_ast_node orelse return null;
            if (self.assertion_scopes.getPtr(fn_node)) |scope| return scope;

            const src = self.source orelse return null;
            const tree = try src.ast();

            var scope = try assertions.buildAssertionScope(self.allocator, tree, ids.astIndex(fn_node), false);
            errdefer scope.deinit(self.allocator);
            try self.assertion_scopes.put(fn_node, scope);
            return self.assertion_scopes.getPtr(fn_node);
        }

        /// Extract a constraint from a branch node's condition.
        /// Returns null if no constraint can be extracted.
        pub fn extractBranchConstraint(self: *_Engine, cfg_node: *const CfgNode, current_cfg: *const Cfg) ?Constraint {
            const ir_node = cfg_node.ir_node;
            if (ir_node.operand_node) |cond_node| {
                // First check if the condition is a literal boolean
                if (_Engine.Literals.evaluateLiteral(self, cond_node)) |literal_val| {
                    if (literal_val.toBool()) |bool_val| {
                        // Use literalBool for compile-time known conditions to enable
                        // proper branch pruning (e.g., if (false) should be pruned)
                        return Constraint.literalBool(bool_val);
                    }
                }

                // Check if the condition is a null comparison (x == null or x != null)
                if (extractNullCheckConstraint(self, cond_node, current_cfg)) |null_constraint| {
                    return null_constraint;
                }

                if (self.source) |src| {
                    const tree = src.ast() catch return null;
                    const node = unwrapGroupedExpression(tree, cond_node) orelse return null;
                    if (comparisonOperator(tree.nodes.items(.tag)[node])) |op| {
                        return extractComparisonConstraint(self, tree, node, op, current_cfg);
                    }
                }

                const var_key = if (self.source != null)
                    (_Engine.VarResolution.resolveVarIdFromExpr(self, cond_node, current_cfg) orelse return null)
                else
                    ids.varId(cond_node);
                if (ir_node.ast_node) |ast_node| {
                    if (hasPayloadCapture(self, ast_node)) {
                        return Constraint.nullCheck(var_key, false);
                    }
                }
                // If we only have a variable and no comparison info, check if it's an optional
                // being used as a boolean (if (optional_var) ...)
                if (isOptionalType(self, cond_node, current_cfg)) {
                    // When optional is used as condition: true branch means non-null
                    return Constraint.nullCheck(var_key, false);
                }
                return Constraint.boolCheck(var_key, true);
            }
            return null;
        }

        /// Return the true-edge comparison; the engine negates it on the false edge.
        fn extractComparisonConstraint(
            self: *_Engine,
            tree: *const std.zig.Ast,
            node: u32,
            op: CompareOp,
            current_cfg: *const Cfg,
        ) ?Constraint {
            const operands = tree.nodes.items(.data)[node].node_and_node;
            const lhs = @intFromEnum(operands[0]);
            const rhs = @intFromEnum(operands[1]);
            if (integerLiteral(tree, rhs)) |value| {
                const var_id = resolveComparisonVariable(self, tree, lhs, current_cfg) orelse return null;
                return Constraint.intCompare(var_id, op, value);
            }
            if (integerLiteral(tree, lhs)) |value| {
                const var_id = resolveComparisonVariable(self, tree, rhs, current_cfg) orelse return null;
                return Constraint.intCompare(var_id, reverseComparison(op), value);
            }
            const lhs_id = resolveComparisonVariable(self, tree, lhs, current_cfg) orelse return null;
            const rhs_id = resolveComparisonVariable(self, tree, rhs, current_cfg) orelse return null;
            return Constraint.varCompare(lhs_id, op, rhs_id);
        }

        fn resolveComparisonVariable(
            self: *_Engine,
            tree: *const std.zig.Ast,
            operand: u32,
            current_cfg: *const Cfg,
        ) ?ids.VarId {
            const node = unwrapGroupedExpression(tree, operand) orelse return null;
            // Resolving arbitrary expressions can map an element or dereference to its base.
            if (tree.nodes.items(.tag)[node] != .identifier) return null;
            const fn_node = current_cfg.fn_ast_node orelse return null;
            const resolver = self.var_resolvers.get(fn_node) orelse return null;
            // Do not substitute occurrence tokens for unresolved names.
            const var_id = resolver.resolve(node) orelse return null;
            if (self.type_context) |type_context| {
                if (type_context.getExpressionTypeStrict(node)) |info| {
                    if (info.kind != .unknown) {
                        return if (isComparisonIntegerType(info)) var_id else null;
                    }
                }
            }

            // AST-only callers must not load ZIR. Follow declaration identities, not
            // names or abstract scalar values (which do not carry a numeric type).
            var value_node = node;
            for (0..tree.nodes.len) |_| {
                if (resolver.resolveDeclInfo(value_node)) |info| {
                    const declaration = tree.fullVarDecl(@enumFromInt(info.decl_node)) orelse return null;
                    if (declaration.ast.type_node.unwrap()) |type_node| {
                        const type_info = ZirBridge.extractTypeFromAstNode(tree, @intFromEnum(type_node)) orelse return null;
                        return if (isComparisonIntegerType(type_info)) var_id else null;
                    }
                    const initializer = declaration.ast.init_node.unwrap() orelse return null;
                    const init_node = unwrapGroupedExpression(tree, @intFromEnum(initializer)) orelse return null;
                    if (tree.nodes.items(.tag)[init_node] == .identifier) {
                        value_node = init_node;
                        continue;
                    }
                    // An untyped immutable integer literal is bounded by its value,
                    // unlike a typed float or wide integer initialized from a literal.
                    if (tree.tokenTag(declaration.ast.mut_token) == .keyword_const and
                        integerLiteral(tree, init_node) != null) return var_id;
                    return null;
                }

                const binding = resolver.resolve(value_node) orelse return null;
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const proto = tree.fullFnProto(&buffer, @enumFromInt(ids.astIndex(fn_node))) orelse return null;
                var params = proto.iterate(tree);
                while (params.next()) |param| {
                    const name_token = param.name_token orelse continue;
                    if (ids.varId(name_token) != binding) continue;
                    const type_node = param.type_expr orelse return null;
                    const type_info = ZirBridge.extractTypeFromAstNode(tree, @intFromEnum(type_node)) orelse return null;
                    return if (isComparisonIntegerType(type_info)) var_id else null;
                }
                return null;
            }
            return null;
        }

        /// Extract multiple constraints from a branch condition.
        /// This handles compound null checks like `a == null or b == null`.
        pub fn extractBranchConstraints(
            self: *_Engine,
            cfg_node: *const CfgNode,
            current_cfg: *const Cfg,
            out_constraints: *[4]?Constraint,
        ) usize {
            const ir_node = cfg_node.ir_node;
            if (ir_node.operand_node) |cond_node| {
                // Try compound null constraints first (for bool_or/bool_and patterns)
                const count = extractCompoundNullConstraints(self, cond_node, current_cfg, out_constraints);
                if (count > 0) {
                    return count;
                }

                // Fall back to single constraint
                if (extractBranchConstraint(self, cfg_node, current_cfg)) |c| {
                    out_constraints[0] = c;
                    return 1;
                }
            }
            return 0;
        }

        /// Extract a null check constraint from a comparison expression.
        /// Handles patterns like `x == null` and `x != null`.
        pub fn extractNullCheckConstraint(self: *_Engine, cond_node: u32, current_cfg: *const Cfg) ?Constraint {
            const src = self.source orelse return null;
            const tree = src.ast() catch return null;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (cond_node >= tags.len) return null;

            const tag = tags[cond_node];
            if (tag != .equal_equal and tag != .bang_equal) return null;

            // Get both operands of the comparison
            const lhs = datas[cond_node].node_and_node[0];
            const rhs = datas[cond_node].node_and_node[1];

            // Check if either operand is `null`
            const lhs_is_null = _Engine.Literals.isNullLiteral(self, @intFromEnum(lhs));
            const rhs_is_null = _Engine.Literals.isNullLiteral(self, @intFromEnum(rhs));

            if (!lhs_is_null and !rhs_is_null) return null;

            // The other operand is the variable being compared
            const var_node = if (lhs_is_null) @intFromEnum(rhs) else @intFromEnum(lhs);
            const var_key = _Engine.VarResolution.resolveVarIdFromExpr(self, var_node, current_cfg) orelse ids.varId(var_node);

            // For == null: is_null=true (true branch means var is null)
            // For != null: is_null=false (true branch means var is non-null)
            const is_null = (tag == .equal_equal);
            return Constraint.nullCheck(var_key, is_null);
        }

        /// Extract multiple null check constraints from compound expressions.
        /// Handles patterns like:
        /// - `a == null or b == null` -> on false branch, both a and b are non-null
        /// - `a != null and b != null` -> on true branch, both a and b are non-null
        /// Returns constraints for the TRUE branch; caller should negate for false branch.
        pub fn extractCompoundNullConstraints(
            self: *_Engine,
            cond_node: u32,
            current_cfg: *const Cfg,
            out_constraints: *[4]?Constraint,
        ) usize {
            const src = self.source orelse return 0;
            const tree = src.ast() catch return 0;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (cond_node >= tags.len) return 0;

            const tag = tags[cond_node];

            // Handle bool_or: (a == null or b == null)
            // On TRUE branch: at least one is null (can't use easily)
            // On FALSE branch: both are non-null (useful!)
            // We return the TRUE branch constraint, so for bool_or we return is_null=true for both
            if (tag == .bool_or) {
                const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
                const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);

                var count: usize = 0;
                if (extractNullCheckConstraint(self, lhs, current_cfg)) |c| {
                    out_constraints[count] = c;
                    count += 1;
                }
                if (extractNullCheckConstraint(self, rhs, current_cfg)) |c| {
                    out_constraints[count] = c;
                    count += 1;
                }
                return count;
            }

            // Handle bool_and: (a != null and b != null)
            // On TRUE branch: both are non-null (useful!)
            // On FALSE branch: at least one is null (can't use easily)
            if (tag == .bool_and) {
                const lhs = @intFromEnum(datas[cond_node].node_and_node[0]);
                const rhs = @intFromEnum(datas[cond_node].node_and_node[1]);

                var count: usize = 0;
                if (extractNullCheckConstraint(self, lhs, current_cfg)) |c| {
                    out_constraints[count] = c;
                    count += 1;
                }
                if (extractNullCheckConstraint(self, rhs, current_cfg)) |c| {
                    out_constraints[count] = c;
                    count += 1;
                }
                return count;
            }

            // Fall back to single constraint
            if (extractNullCheckConstraint(self, cond_node, current_cfg)) |c| {
                out_constraints[0] = c;
                return 1;
            }

            return 0;
        }

        /// Extract a nullability constraint from an assertion call.
        /// Handles patterns like:
        /// - testing.expect(x != null)
        /// - std.testing.expect(x != null)
        /// - std.testing.expectEqual(x, null)
        /// After such a call, we assume the asserted relationship holds.
        pub fn extractAssertionConstraint(self: *_Engine, call_node: u32, current_cfg: *const Cfg) std.mem.Allocator.Error!?Constraint {
            const src = self.source orelse return null;
            const tree = try src.ast();
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (call_node >= tags.len) return null;

            // Get the full call information
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const full_call = switch (tags[call_node]) {
                .call, .call_comma, .call_one, .call_one_comma => tree.fullCall(&call_buf, @enumFromInt(call_node)),
                else => null,
            } orelse return null;

            const scope = (try getAssertionScope(self, current_cfg)) orelse return null;
            const lexical = src.lexicalIndex() catch return null;
            var assertion_name = assertions.resolveAssertionName(tree, full_call.ast.fn_expr, scope);
            if (assertion_name == null) {
                assertion_name = assertions.resolveDebugAssertionName(tree, full_call.ast.fn_expr, scope, lexical);
            }
            const resolved_name = assertion_name orelse return null;
            const assertion_kind = assertions.constraintKindForName(resolved_name) orelse return null;

            // Get the first argument (the condition being asserted)
            const args = full_call.ast.params;
            if (args.len == 0) return null;

            switch (assertion_kind) {
                .boolean => {
                    const cond_node = @intFromEnum(args[0]);

                    // Check if the condition is a null check (x != null)
                    if (cond_node >= tags.len) return null;
                    const cond_tag = tags[cond_node];

                    if (cond_tag == .bang_equal) {
                        // x != null pattern - after expect(x != null), x is non-null
                        const lhs = datas[cond_node].node_and_node[0];
                        const rhs = datas[cond_node].node_and_node[1];

                        const lhs_is_null = _Engine.Literals.isNullLiteral(self, @intFromEnum(lhs));
                        const rhs_is_null = _Engine.Literals.isNullLiteral(self, @intFromEnum(rhs));

                        if (lhs_is_null or rhs_is_null) {
                            const var_node = if (lhs_is_null) @intFromEnum(rhs) else @intFromEnum(lhs);
                            const var_key = _Engine.VarResolution.resolveVarIdFromExpr(self, var_node, current_cfg) orelse return null;
                            // After expect(x != null), x is proven non-null (is_null=false)
                            return Constraint.nullCheck(var_key, false);
                        }
                    } else if (cond_tag == .equal_equal) {
                        // x == null pattern - after expect(x == null), x is proven null
                        // This is less common but we handle it for completeness
                        const lhs = datas[cond_node].node_and_node[0];
                        const rhs = datas[cond_node].node_and_node[1];

                        const lhs_is_null = _Engine.Literals.isNullLiteral(self, @intFromEnum(lhs));
                        const rhs_is_null = _Engine.Literals.isNullLiteral(self, @intFromEnum(rhs));

                        if (lhs_is_null or rhs_is_null) {
                            const var_node = if (lhs_is_null) @intFromEnum(rhs) else @intFromEnum(lhs);
                            const var_key = _Engine.VarResolution.resolveVarIdFromExpr(self, var_node, current_cfg) orelse return null;
                            // After expect(x == null), x is proven null (is_null=true)
                            return Constraint.nullCheck(var_key, true);
                        }
                    }

                    return null;
                },
                .equality => {
                    if (args.len < 2) return null;
                    const lhs_node = @intFromEnum(args[0]);
                    const rhs_node = @intFromEnum(args[1]);

                    const lhs_is_null = _Engine.Literals.isNullLiteral(self, lhs_node);
                    const rhs_is_null = _Engine.Literals.isNullLiteral(self, rhs_node);

                    if (lhs_is_null or rhs_is_null) {
                        const var_node = if (lhs_is_null) rhs_node else lhs_node;
                        const var_key = _Engine.VarResolution.resolveVarIdFromExpr(self, var_node, current_cfg) orelse return null;
                        return Constraint.nullCheck(var_key, true);
                    }

                    const lhs_is_non_null = _Engine.Literals.isNonNullLiteral(self, lhs_node);
                    const rhs_is_non_null = _Engine.Literals.isNonNullLiteral(self, rhs_node);

                    if (lhs_is_non_null or rhs_is_non_null) {
                        const var_node = if (lhs_is_non_null) rhs_node else lhs_node;
                        const var_key = _Engine.VarResolution.resolveVarIdFromExpr(self, var_node, current_cfg) orelse return null;
                        return Constraint.nullCheck(var_key, false);
                    }

                    return null;
                },
            }
        }

        /// Extract a non-null constraint from a try expression wrapping an assertion call.
        /// Handles patterns like: try testing.expect(x != null)
        pub fn extractTryAssertionConstraint(self: *_Engine, try_ast_node: u32, current_cfg: *const Cfg) std.mem.Allocator.Error!?Constraint {
            const src = self.source orelse return null;
            const tree = try src.ast();
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (try_ast_node >= tags.len) return null;

            // Check if the AST node is a try expression
            if (tags[try_ast_node] != .@"try") return null;

            // Get the operand of the try expression
            const try_operand = @intFromEnum(datas[try_ast_node].node);
            if (try_operand >= tags.len) return null;

            // Check if the operand is a call expression
            const operand_tag = tags[try_operand];
            if (!call_utils.isCallNode(operand_tag)) {
                return null;
            }

            // Delegate to the regular assertion constraint extraction
            return extractAssertionConstraint(self, try_operand, current_cfg);
        }

        /// Check if a condition expression is an optional type.
        pub fn isOptionalType(self: *_Engine, cond_node: u32, current_cfg: *const Cfg) bool {
            _ = current_cfg;
            const src = self.source orelse return false;
            const tree = src.ast() catch return false;
            const tags = tree.nodes.items(.tag);

            if (cond_node >= tags.len) return false;

            // If it's an identifier, check if the type context knows it's optional
            if (tags[cond_node] == .identifier) {
                if (self.type_context) |type_ctx| {
                    const main_tokens = tree.nodes.items(.main_token);
                    const token = main_tokens[cond_node];
                    const name = tree.tokenSlice(token);
                    if (type_ctx.getDeclType(name)) |type_info| {
                        return type_info.kind == .optional;
                    }
                }
            }

            return false;
        }

        pub fn hasPayloadCapture(self: *_Engine, ast_node: u32) bool {
            const src = self.source orelse return false;
            const tree = src.ast() catch return false;
            const tags = tree.nodes.items(.tag);

            if (ast_node >= tags.len) return false;
            if (tags[ast_node] != .@"if" and tags[ast_node] != .if_simple) return false;
            const full_if = tree.fullIf(@enumFromInt(ast_node)) orelse return false;
            return full_if.payload_token != null;
        }
    };
}

fn isComparisonIntegerType(info: TypeInfo) bool {
    // Constraint ranges and strict +/-1 bounds are defined over signed i64 only.
    if (info.size_bits == 0) return false;
    return switch (info.kind) {
        .int => info.size_bits <= 64,
        .uint => info.size_bits <= 63,
        else => false,
    };
}

fn unwrapGroupedExpression(tree: *const std.zig.Ast, expression: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    var node = expression;
    var remaining = tags.len;
    while (remaining > 0 and node != 0 and node < tags.len) : (remaining -= 1) {
        if (tags[node] != .grouped_expression) return node;
        node = @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]);
    }
    return null;
}

fn comparisonOperator(tag: std.zig.Ast.Node.Tag) ?CompareOp {
    return switch (tag) {
        .equal_equal => .eq,
        .bang_equal => .ne,
        .less_than => .lt,
        .less_or_equal => .le,
        .greater_than => .gt,
        .greater_or_equal => .ge,
        else => null,
    };
}

fn reverseComparison(op: CompareOp) CompareOp {
    return switch (op) {
        .eq, .ne => op,
        .lt => .gt,
        .le => .ge,
        .gt => .lt,
        .ge => .le,
    };
}

fn integerLiteral(tree: *const std.zig.Ast, expression: u32) ?i64 {
    var node = unwrapGroupedExpression(tree, expression) orelse return null;
    const tags = tree.nodes.items(.tag);
    const negative = tags[node] == .negation;
    if (negative) {
        const child = @intFromEnum(tree.nodes.items(.data)[node].node);
        node = unwrapGroupedExpression(tree, child) orelse return null;
    }
    if (tags[node] != .number_literal) return null;

    // Parse the whole token: floats, overflow, and invalid digits must stay unknown.
    const token = tree.nodes.items(.main_token)[node];
    const magnitude = std.fmt.parseInt(u64, tree.tokenSlice(token), 0) catch return null;
    if (!negative) return std.math.cast(i64, magnitude);

    // The magnitude of minInt(i64) is not representable as a positive i64.
    const min_magnitude = @as(u64, std.math.maxInt(i64)) + 1;
    if (magnitude > min_magnitude) return null;
    if (magnitude == min_magnitude) return std.math.minInt(i64);
    return -@as(i64, @intCast(magnitude));
}

const TestEngine = @import("engine.zig").AnalysisEngine;
const TestSource = @import("../../source.zig").Source;
const TestCfgBuilder = @import("../../cfg.zig").CfgBuilder;
const TestState = @import("../state.zig").ProgramState;
const TestValue = @import("../value.zig").AbstractValue;

fn extractTestConstraint(condition: []const u8, value_type: []const u8, with_types: bool) !struct {
    constraint: ?Constraint,
    var_id: ids.VarId,
} {
    const allocator = std.testing.allocator;
    var buffer: [512]u8 = undefined;
    const code = try std.fmt.bufPrint(
        &buffer,
        "fn compare(value: {s}, other: {s}) void {{ if ({s}) {{}} }}\x00",
        .{ value_type, value_type, condition },
    );
    var source = TestSource.init(allocator, "comparison.zig", code[0 .. code.len - 1 :0]);
    defer source.deinit();
    var type_context = @import("../../type_context.zig").TypeContext.init(allocator, &source);
    defer type_context.deinit();
    const tree = try source.ast();
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    const fn_node = tree.rootDecls()[0];
    const proto_node = tree.nodes.items(.data)[@intFromEnum(fn_node)].node_and_node[0];
    var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&proto_buffer, proto_node) orelse return error.TestUnexpectedResult;
    var params = proto.iterate(tree);
    const param = params.next() orelse return error.TestUnexpectedResult;
    const name_token = param.name_token orelse return error.TestUnexpectedResult;
    const var_id = ids.varId(name_token);

    var builder = TestCfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, ids.astId(@intFromEnum(fn_node)))) orelse
        return error.TestUnexpectedResult;
    defer cfg.deinit();
    var engine = TestEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    if (with_types) engine.setTypeContext(&type_context);
    try TestEngine.VarResolution.prepare(&engine, &cfg);
    for (cfg.nodes.items) |*node| {
        if (node.ir_node.tag != .branch) continue;
        return .{
            .constraint = TestEngine.BranchConstraints.extractBranchConstraint(&engine, node, &cfg),
            .var_id = var_id,
        };
    }
    return error.TestUnexpectedResult;
}

test "assertion scope allocation failures propagate through direct and try calls" {
    // Include every alias list so failures also exercise partial scope cleanup.
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const lib = @import("std");
        \\const debug = lib.debug;
        \\fn check(value: ?u8) !void {
        \\    const testing = lib.testing;
        \\    try testing.expect(value != null);
        \\    debug.assert(value != null);
        \\}
    ;
    var source = TestSource.init(allocator, "assertion-oom.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = tree.rootDecls()[2];
    const try_node = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag == .@"try") break @as(u32, @intCast(index));
    } else return error.TestUnexpectedResult;
    const call_node = @intFromEnum(tree.nodes.items(.data)[try_node].node);
    const proto_node = tree.nodes.items(.data)[@intFromEnum(fn_node)].node_and_node[0];
    var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&proto_buffer, proto_node) orelse return error.TestUnexpectedResult;
    var params = proto.iterate(tree);
    const param = params.next() orelse return error.TestUnexpectedResult;
    const name_token = param.name_token orelse return error.TestUnexpectedResult;
    const var_id = ids.varId(name_token);

    var builder = TestCfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, ids.astId(@intFromEnum(fn_node)))) orelse
        return error.TestUnexpectedResult;
    defer cfg.deinit();
    try std.testing.checkAllAllocationFailures(allocator, testAssertionScopeAllocationFailure, .{
        &cfg, code, call_node,
    });

    for ([_]bool{ false, true }) |wrapped_in_try| {
        var failing = std.testing.FailingAllocator.init(allocator, .{});
        var engine = TestEngine.initWithSource(failing.allocator(), &cfg, &source);
        defer engine.deinit();
        try TestEngine.VarResolution.prepare(&engine, &cfg);
        failing.fail_index = failing.alloc_index;
        failing.resize_fail_index = failing.resize_index;
        const failed = if (wrapped_in_try)
            TestEngine.BranchConstraints.extractTryAssertionConstraint(&engine, try_node, &cfg)
        else
            TestEngine.BranchConstraints.extractAssertionConstraint(&engine, call_node, &cfg);
        try std.testing.expectError(error.OutOfMemory, failed);

        failing.fail_index = std.math.maxInt(usize);
        failing.resize_fail_index = std.math.maxInt(usize);
        const constraint = (try if (wrapped_in_try)
            TestEngine.BranchConstraints.extractTryAssertionConstraint(&engine, try_node, &cfg)
        else
            TestEngine.BranchConstraints.extractAssertionConstraint(&engine, call_node, &cfg)) orelse
            return error.TestUnexpectedResult;
        try std.testing.expect(constraint.eql(Constraint.nullCheck(var_id, false)));
    }
}

fn testAssertionScopeAllocationFailure(
    allocator: std.mem.Allocator,
    cfg: *const Cfg,
    code: [:0]const u8,
    call_node: u32,
) !void {
    // Keep this source cold to cover parsing as well as scope and cache allocation.
    var source = TestSource.init(allocator, "assertion-oom.zig", code);
    defer source.deinit();
    var engine = TestEngine.initWithSource(allocator, cfg, &source);
    defer engine.deinit();
    const scope = (try TestEngine.BranchConstraints.getAssertionScope(&engine, cfg)) orelse
        return error.TestUnexpectedResult;
    const tree = try source.ast();
    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(call_node)) orelse
        return error.TestUnexpectedResult;
    const name = assertions.resolveAssertionName(tree, call.ast.fn_expr, scope) orelse
        return error.TestUnexpectedResult;
    try std.testing.expectEqualStrings("expect", name);
}

test "branch comparisons preserve operand order and both edge meanings" {
    // Check strict and inclusive boundaries against the actual parameter binding.
    const cases = [_]struct { operator: []const u8, matches: [3]bool }{
        .{ .operator = "==", .matches = .{ false, true, false } },
        .{ .operator = "!=", .matches = .{ true, false, true } },
        .{ .operator = "<", .matches = .{ true, false, false } },
        .{ .operator = "<=", .matches = .{ true, true, false } },
        .{ .operator = ">", .matches = .{ false, false, true } },
        .{ .operator = ">=", .matches = .{ false, true, true } },
    };
    for (cases) |case| {
        for ([_]bool{ false, true }) |reversed| {
            var buffer: [64]u8 = undefined;
            const expression = try std.fmt.bufPrint(&buffer, "{s} {s} {s}", .{
                if (reversed) "-3" else "value",
                case.operator,
                if (reversed) "value" else "-3",
            });
            const extracted = try extractTestConstraint(expression, "i64", false);
            const constraint = extracted.constraint orelse return error.TestUnexpectedResult;
            for ([_]i64{ -4, -3, -2 }, 0..) |value, index| {
                const matches = case.matches[if (reversed) 2 - index else index];
                for ([_]bool{ false, true }) |true_edge| {
                    var state = TestState.init(std.testing.allocator);
                    defer state.deinit();
                    try state.setVar(extracted.var_id, .{ .concrete_int = value });
                    try state.addConstraint(if (true_edge) constraint else constraint.negate());
                    try std.testing.expectEqual(matches == true_edge, state.isSatisfiable());
                }
            }
        }
    }
}

test "branch comparisons refine signed literal bounds without overflow" {
    const min = std.math.minInt(i64);
    const max = std.math.maxInt(i64);
    const cases = [_]struct { expression: []const u8, expected: TestValue }{
        .{ .expression = "value == -9223372036854775808", .expected = .{ .concrete_int = min } },
        .{ .expression = "9223372036854775807 == value", .expected = .{ .concrete_int = max } },
        .{ .expression = "(-0x2 < (value))", .expected = .{ .int_range = .{ .min = -1, .max = max } } },
        .{ .expression = "(value) <= -(0b10)", .expected = .{ .int_range = .{ .min = min, .max = -2 } } },
        .{ .expression = "-0o2 <= value", .expected = .{ .int_range = .{ .min = -2, .max = max } } },
        .{ .expression = "value == -1_024", .expected = .{ .concrete_int = -1024 } },
    };
    for (cases) |case| {
        const extracted = try extractTestConstraint(case.expression, "i64", false);
        const constraint = extracted.constraint orelse return error.TestUnexpectedResult;
        var state = TestState.init(std.testing.allocator);
        defer state.deinit();
        try state.setVar(extracted.var_id, .unknown);
        try state.addConstraint(constraint);
        try std.testing.expect(state.isSatisfiable());
        const value = state.getVar(extracted.var_id) orelse return error.TestUnexpectedResult;
        try std.testing.expect(case.expected.eql(value));
    }
}

test "branch comparisons keep shadowed and relational bindings distinct" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\fn compare(value: i64, other: i64) void {
        \\    {
        \\        const value: i64 = -3;
        \\        if (value < other) {}
        \\        if (value == -3) {}
        \\    }
        \\    if (value == 0) {}
        \\}
    ;
    var source = TestSource.init(allocator, "shadowed-comparison.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = tree.rootDecls()[0];
    const proto_node = tree.nodes.items(.data)[@intFromEnum(fn_node)].node_and_node[0];
    var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&proto_buffer, proto_node) orelse return error.TestUnexpectedResult;
    var params = proto.iterate(tree);
    const outer_param = params.next() orelse return error.TestUnexpectedResult;
    const outer_id = ids.varId(outer_param.name_token orelse return error.TestUnexpectedResult);
    const other_param = params.next() orelse return error.TestUnexpectedResult;
    const other_id = ids.varId(other_param.name_token orelse return error.TestUnexpectedResult);
    const inner_id = for (tree.nodes.items(.tag), 0..) |_, index| {
        const decl = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
        break ids.varId(decl.ast.mut_token + 1);
    } else return error.TestUnexpectedResult;

    var builder = TestCfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, ids.astId(@intFromEnum(fn_node)))) orelse
        return error.TestUnexpectedResult;
    defer cfg.deinit();
    var engine = TestEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    try TestEngine.VarResolution.prepare(&engine, &cfg);
    var constraints: [3]Constraint = undefined;
    var count: usize = 0;
    for (cfg.nodes.items) |*node| {
        if (node.ir_node.tag != .branch) continue;
        try std.testing.expect(count < constraints.len);
        constraints[count] = TestEngine.BranchConstraints.extractBranchConstraint(
            &engine,
            node,
            &cfg,
        ) orelse return error.TestUnexpectedResult;
        count += 1;
    }
    try std.testing.expectEqual(constraints.len, count);
    try std.testing.expect(constraints[0].eql(Constraint.varCompare(inner_id, .lt, other_id)));
    try std.testing.expect(constraints[0].negate().eql(Constraint.varCompare(inner_id, .ge, other_id)));

    var state = TestState.init(allocator);
    defer state.deinit();
    try state.setVar(outer_id, .{ .concrete_int = 0 });
    try state.setVar(inner_id, .unknown);
    try state.addConstraint(constraints[1]);
    try state.addConstraint(constraints[2]);
    try std.testing.expect(state.isSatisfiable());
    const outer_value = state.getVar(outer_id) orelse return error.TestUnexpectedResult;
    const inner_value = state.getVar(inner_id) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(i64, 0), outer_value.concrete_int);
    try std.testing.expectEqual(@as(i64, -3), inner_value.concrete_int);
}

test "branch comparisons require representable integer operand types" {
    const cases = [_]struct { value_type: []const u8, representable: bool }{
        .{ .value_type = "i64", .representable = true },
        .{ .value_type = "u63", .representable = true },
        .{ .value_type = "i65", .representable = false },
        .{ .value_type = "u64", .representable = false },
        .{ .value_type = "i128", .representable = false },
        .{ .value_type = "f64", .representable = false },
        .{ .value_type = "usize", .representable = false },
        .{ .value_type = "anytype", .representable = false },
    };
    for (cases) |case| {
        for ([_]bool{ false, true }) |with_types| {
            for ([_][]const u8{ "value > 0", "0 < value", "value < other" }) |expression| {
                const extracted = try extractTestConstraint(expression, case.value_type, with_types);
                try std.testing.expectEqual(case.representable, extracted.constraint != null);
            }
        }
    }
}

test "unsupported branch comparisons leave both paths feasible" {
    const expressions = [_][]const u8{
        "value + 1 == 0",
        "0 < value * 2",
        "-value == 0",
        "value == 9223372036854775808",
        "value < -9223372036854775809",
        "value == 0.5",
        "value == 1e3",
        "value == @as(f64, 0.5)",
        "missing == 0",
        "value == missing",
        "value[0] == 0",
        "value.* != 0",
        "value == -%1",
    };
    for (expressions) |expression| {
        const extracted = try extractTestConstraint(expression, "i64", false);
        try std.testing.expect(extracted.constraint == null);
    }

    // Exercise CFG propagation as well as extraction: unsupported arithmetic must not prune.
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\fn compare() i32 {
        \\    const value: i32 = 0;
        \\    if (value + 1 == 1) return 1;
        \\    return 2;
        \\}
    ;
    var source = TestSource.init(allocator, "unsupported-comparison.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    var builder = TestCfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, ids.astId(@intFromEnum(tree.rootDecls()[0])))) orelse
        return error.TestUnexpectedResult;
    defer cfg.deinit();
    var engine = TestEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    try engine.run();
    var reached_returns: usize = 0;
    for (cfg.nodes.items) |node| {
        if (node.ir_node.tag != .ret) continue;
        const reached = for (engine.getGraph().nodes.items) |executed| {
            if (executed.point.cfg == &cfg and executed.point.node_index == node.index and
                executed.point.kind == .pre) break true;
        } else false;
        try std.testing.expect(reached);
        reached_returns += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), reached_returns);
}
