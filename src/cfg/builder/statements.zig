const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");

const source_range = @import("source_range.zig");
const graph = @import("../graph.zig");
const ids = @import("../../ids.zig");
const Source = @import("../../source.zig").Source;

const Cfg = graph.Cfg;
const EdgeKind = graph.EdgeKind;
const IrNode = graph.IrNode;
const CfgNodeId = ids.CfgNodeId;
const IrTag = graph.IrTag;

pub fn Mixin(comptime _Builder: type) type {
    return struct {
        pub fn processBlock(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const tags = tree.nodes.items(.tag);
            const data = tree.nodes.items(.data);

            const tag = tags[ast_node];

            var stmts: []const u32 = &[_]u32{};
            var inline_stmts: [2]u32 = undefined;

            switch (tag) {
                .block, .block_semicolon => {
                    const extra = data[ast_node].extra_range;
                    const start: usize = @intFromEnum(extra.start);
                    const end: usize = @intFromEnum(extra.end);
                    if (end > start) {
                        stmts = tree.extra_data[start..end];
                    }
                },
                .block_two, .block_two_semicolon => {
                    var count: usize = 0;
                    const opt_nodes = data[ast_node].opt_node_and_opt_node;
                    if (opt_nodes[0].unwrap()) |node| {
                        inline_stmts[count] = @intFromEnum(node);
                        count += 1;
                    }
                    if (opt_nodes[1].unwrap()) |node| {
                        inline_stmts[count] = @intFromEnum(node);
                        count += 1;
                    }
                    stmts = inline_stmts[0..count];
                },
                else => return .{ .last = null, .terminates = false },
            }

            // A labeled block is what `break :label` targets, so its exit node
            // is created before the body is walked: a break inside the body
            // then knows where to land. Unlabeled blocks keep the shape they
            // had before - no extra node, no allocation.
            const label_token = blockLabelToken(tree, ast_node);
            const merge_node: ?CfgNodeId = if (label_token == 0) null else try cfg.addNode(IrNode.init(.nop));

            // The chain borrows this frame: nested walks read it through
            // `current_scope`, and the parent link puts it back afterwards.
            // Nothing is allocated and no nesting depth is outgrown.
            const scope: _Builder.Scope = .{
                .parent = self.current_scope,
                .ast_node = ast_node,
                .label_token = label_token,
                .merge_node = merge_node,
            };
            self.current_scope = &scope;
            defer self.current_scope = scope.parent;

            if (stmts.len == 0) {
                // An empty labeled block still hands control on. Without this
                // edge its exit node is an orphan and every statement after it
                // loses the path that reaches it.
                if (merge_node) |exit| try cfg.addEdge(prev_node, exit);
                return .{ .last = merge_node, .terminates = false };
            }

            var current_prev = prev_node;
            var last_processed: ?CfgNodeId = null;
            var terminates = false;
            var pending_edge_kind: ?EdgeKind = null;
            var last_stmt_edge_start: usize = 0;

            for (stmts) |stmt| {
                const edge_count_before = cfg.edges.items.len;
                const result = try self.processNode(cfg, source, stmt, current_prev);

                // If the previous statement requested a specific edge kind for the
                // connection to the next statement, apply it now
                if (pending_edge_kind) |kind| {
                    self.markEdgeFromNode(cfg, edge_count_before, current_prev, kind);
                    pending_edge_kind = null;
                }

                if (result.last) |node_idx| {
                    last_processed = node_idx;
                    current_prev = node_idx;
                }

                last_stmt_edge_start = edge_count_before;

                // Save the edge kind for the next iteration (e.g., try_success after try)
                pending_edge_kind = result.next_edge_kind;

                if (result.terminates) {
                    terminates = true;
                    break;
                }
            }

            const exit_node = merge_node orelse return .{ .last = last_processed, .terminates = terminates };

            if (!terminates) {
                // A trailing `try` asked for a `try_success` edge onto whatever
                // follows it; inside a labeled block that is the merge node.
                if (pending_edge_kind) |kind| {
                    if (last_processed) |last_node| {
                        self.markEdgeFromNode(cfg, last_stmt_edge_start, last_node, kind);
                    }
                }
                try cfg.addEdge(last_processed orelse prev_node, exit_node);
            }

            return .{ .last = exit_node, .terminates = false };
        }

        /// `break :label [operand]`.
        ///
        /// The labeled block's exit node exists before its body is walked, so a
        /// resolved break evaluates its operand, runs the `defer` bodies of the
        /// scopes it leaves, and lands after the target block. It does not fall
        /// through into the statement a guard was protecting.
        ///
        /// A transfer that leaves the deferred body being inlined is refused as
        /// a malformed AST (see `breaksOutOfDeferBody`) rather than modeled.
        ///
        /// An unlabeled `break`, or one naming a label this builder does not
        /// model (a loop label, or none at all), keeps the generic expression
        /// treatment: this analysis does not model loop exits, and treating an
        /// unresolved transfer as a jump would drop a path and call code safe
        /// that nothing ever analyzed.
        pub fn processBreak(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const break_data = tree.nodes.items(.data)[ast_node].opt_token_and_opt_node;

            const label_token = break_data[0].unwrap() orelse
                return try processGenericExpr(self, cfg, source, ast_node, prev_node);

            const target = findLabeledBlock(self, tree, label_token) orelse
                return try processGenericExpr(self, cfg, source, ast_node, prev_node);
            const target_merge = target.merge_node orelse return error.InvalidAst;

            // A transfer that leaves the deferred body currently being inlined
            // is a compile error, not a jump. Refuse the function rather than
            // resolving it and dropping the path behind it.
            if (breaksOutOfDeferBody(self, target)) return error.InvalidAst;

            var tail = prev_node;

            // The operand is evaluated before control leaves the block, so a
            // `break :blk 1 / x` is still analyzed. It goes through the normal
            // expression dispatch instead of a bare node: a `try` operand keeps
            // its error edge to the function exit, a `catch` operand keeps its
            // handler, and only a plain expression collapses to one node.
            if (break_data[1].unwrap()) |operand| {
                const edge_count_before = cfg.edges.items.len;
                const result = try self.processNode(cfg, source, @intFromEnum(operand), tail);
                if (result.last) |operand_end| {
                    if (result.next_edge_kind) |kind| {
                        self.markEdgeFromNode(cfg, edge_count_before, tail, kind);
                    }
                    tail = operand_end;
                }
            }

            const break_range = try source_range.getSourceRange(source, ast_node);
            const break_node = try cfg.addNode(IrNode.initFull(.break_stmt, ast_node, break_range));
            try cfg.addEdge(tail, break_node);

            tail = (try emitExitedScopeDefers(self, cfg, source, ast_node, target, break_node)) orelse
                return .{ .last = break_node, .terminates = true };

            try cfg.addEdgeWithKind(tail, target_merge, .jump);

            return .{ .last = break_node, .terminates = true };
        }

        /// Innermost open scope whose label names `label_token`, or null when no
        /// enclosing labeled block matches. Nearest wins, so an inner
        /// `blk: { break :blk; }` never resolves to an outer `blk`, and the
        /// chain reaches any nesting depth the source actually has.
        fn findLabeledBlock(self: *_Builder, tree: *const std.zig.Ast, label_token: u32) ?*const _Builder.Scope {
            var scope = self.current_scope;
            while (scope) |entry| {
                if (entry.merge_node != null and labelsMatch(tree, entry.label_token, label_token)) return entry;
                scope = entry.parent;
            }
            return null;
        }

        /// Chain the `defer` bodies that fire while control leaves the scopes a
        /// labeled break jumps out of: innermost scope first, and within a scope
        /// in reverse declaration order. Only defers the break had already
        /// reached count - one declared after it never runs on this path - and
        /// `errdefer` bodies stay out, because a plain break is not an error
        /// path.
        ///
        /// Returns the last node built, or null when the path genuinely stops:
        /// a deferred body that does not fall through.
        fn emitExitedScopeDefers(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            break_ast_node: u32,
            target: *const _Builder.Scope,
            from: CfgNodeId,
        ) !?CfgNodeId {
            const tree = try source.ast();
            const break_start = nodeStartOffset(tree, break_ast_node);

            var tail = from;
            var scope = self.current_scope;
            while (scope) |entry| {
                tail = (try emitScopeDefers(self, cfg, source, entry, break_start, tail)) orelse
                    return null;
                if (entry == target) break;
                scope = entry.parent;
            }
            return @as(?CfgNodeId, tail);
        }

        fn emitScopeDefers(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            declaring: *const _Builder.Scope,
            break_start: u32,
            from: CfgNodeId,
        ) !?CfgNodeId {
            const tree = try source.ast();
            const tags = tree.nodes.items(.tag);
            const data = tree.nodes.items(.data);
            if (declaring.ast_node >= tags.len) return @as(?CfgNodeId, from);

            // A deferred body sees the scope that declared it and everything
            // above it, and nothing else. The scopes this unwind already left,
            // and the blocks a previously inlined body pushed, stay invisible so
            // a label inside one of them cannot be resolved from here.
            const outer_scope = self.current_scope;
            self.current_scope = declaring;
            defer self.current_scope = outer_scope;
            const outer_boundary = self.defer_boundary;
            self.defer_boundary = declaring;
            defer self.defer_boundary = outer_boundary;

            var inline_stmts: [2]u32 = undefined;
            const stmts = ast_walk.getBlockStatements(tree, declaring.ast_node, &inline_stmts) orelse
                return @as(?CfgNodeId, from);

            var tail = from;
            var i = stmts.len;
            while (i > 0) {
                i -= 1;
                const stmt = stmts[i];
                if (stmt >= tags.len) continue;
                if (tags[stmt] != .@"defer") continue;
                if (nodeStartOffset(tree, stmt) >= break_start) continue;

                const body = @intFromEnum(data[stmt].node);
                if (body == 0 or body >= tags.len) continue;

                const edge_count_before = cfg.edges.items.len;
                const nodes_before = cfg.nodes.items.len;
                const result = try self.processNode(cfg, source, body, tail);
                self.markEdgeFromNode(cfg, edge_count_before, tail, .defer_edge);

                if (result.terminates) {
                    // Inside a deferred body, only a `break` to one of the body's
                    // own labels can end its statement list, and that means the
                    // body completed: control reaches the body's exit node, which
                    // is where the unwind carries on. `unreachable` really is a
                    // dead end, and `return` is a compile error in a defer body.
                    const last_tag: IrTag = if (result.last) |last|
                        if (cfg.getNode(last)) |node| node.ir_node.tag else .nop
                    else
                        .nop;
                    if (last_tag == .unreachable_stmt) return null;
                    if (last_tag != .break_stmt) return error.InvalidAst;
                    tail = deferBodyExit(cfg, nodes_before) orelse return null;
                } else if (result.last) |last| {
                    tail = last;
                }
            }
            return @as(?CfgNodeId, tail);
        }

        /// Exit node of a labeled block: the merge it creates before walking its
        /// body, which is the first merge that walk added.
        fn deferBodyExit(cfg: *const Cfg, first_new_node: usize) ?CfgNodeId {
            var i = first_new_node;
            while (i < cfg.nodes.items.len) : (i += 1) {
                if (cfg.nodes.items[i].ir_node.tag == .nop) return cfg.nodes.items[i].index;
            }
            return null;
        }

        /// True when `target` names the scope that owns the deferred body being
        /// inlined, or anything above it. Zig rejects a transfer that leaves a
        /// defer body, so the function is refused rather than turned into a jump
        /// that drops a path and calls what follows proven safe. Labels the body
        /// declares itself sit below the boundary and resolve normally.
        fn breaksOutOfDeferBody(self: *_Builder, target: *const _Builder.Scope) bool {
            var scope = self.defer_boundary;
            while (scope) |entry| {
                if (entry == target) return true;
                scope = entry.parent;
            }
            return false;
        }

        /// Token index of a block's label identifier, or 0 when it has none.
        /// A block's main token is its `{`; `blk: {` puts the label two tokens
        /// earlier.
        fn blockLabelToken(tree: *const std.zig.Ast, ast_node: u32) u32 {
            const main_tokens = tree.nodes.items(.main_token);
            const token_tags = tree.tokens.items(.tag);
            if (ast_node >= main_tokens.len) return 0;

            const main_token = main_tokens[ast_node];
            if (main_token < 2 or main_token >= token_tags.len) return 0;
            if (token_tags[main_token - 1] != .colon) return 0;
            if (token_tags[main_token - 2] != .identifier) return 0;
            return main_token - 2;
        }

        /// Labels name identifiers, and `@"name"` is the same identifier as
        /// `name`, so both spellings normalize before they compare. A label
        /// whose text still carries an escape is left as written: the spellings
        /// then simply do not compare equal, and an unresolved label keeps its
        /// fallthrough treatment instead of resolving to the wrong target.
        fn labelsMatch(tree: *const std.zig.Ast, scope_label: u32, break_label: u32) bool {
            return std.mem.eql(u8, labelText(tree, scope_label), labelText(tree, break_label));
        }

        fn labelText(tree: *const std.zig.Ast, token: u32) []const u8 {
            if (token >= tree.tokens.items(.tag).len) return "";
            return import_resolver.normalizeIdentifier(tree.tokenSlice(token));
        }

        /// Byte offset where an AST node starts, or maxInt when it has no usable
        /// token. Comparing offsets decides whether a statement came before the
        /// break that unwinds its scope.
        fn nodeStartOffset(tree: *const std.zig.Ast, ast_node: u32) u32 {
            const main_tokens = tree.nodes.items(.main_token);
            const token_starts = tree.tokens.items(.start);
            if (ast_node >= main_tokens.len) return std.math.maxInt(u32);

            const main_token = main_tokens[ast_node];
            if (main_token >= token_starts.len) return std.math.maxInt(u32);
            return token_starts[main_token];
        }

        pub fn processReturn(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const range = try source_range.getSourceRange(source, ast_node);

            // Check if the return expression contains a try or catch expression
            // Return node data: opt_node format - a single optional return expression
            const data = tree.nodes.items(.data);
            const ret_expr_opt = data[ast_node].opt_node;
            if (ret_expr_opt.unwrap()) |ret_expr_node| {
                const ret_expr_idx = @intFromEnum(ret_expr_node);
                const tags = tree.nodes.items(.tag);
                if (ret_expr_idx < tags.len) {
                    const ret_expr_tag = tags[ret_expr_idx];
                    if (ret_expr_tag == .@"try") {
                        return try _Builder.ErrorFlow.processReturnWithTry(self, cfg, source, ast_node, ret_expr_idx, prev_node, range);
                    } else if (ret_expr_tag == .@"catch") {
                        return try _Builder.ErrorFlow.processReturnWithCatch(self, cfg, source, ast_node, ret_expr_idx, prev_node, range);
                    } else if (ret_expr_tag == .@"switch" or ret_expr_tag == .switch_comma) {
                        return try _Builder.SwitchFlow.processReturnWithSwitch(self, cfg, source, ast_node, ret_expr_idx, prev_node, range);
                    }
                }
            }

            const ret_node = try cfg.addNode(IrNode.initFull(.ret, ast_node, range));
            try cfg.addEdge(prev_node, ret_node);
            try cfg.addEdgeWithKind(ret_node, cfg.exit, .jump);
            return .{ .last = ret_node, .terminates = true };
        }

        pub fn processVarDecl(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const range = try source_range.getSourceRange(source, ast_node);

            // Check if the initializer contains a try or catch expression
            const full_var = tree.fullVarDecl(@enumFromInt(ast_node));
            if (full_var) |vd| {
                if (vd.ast.init_node.unwrap()) |init_node| {
                    const init_idx = @intFromEnum(init_node);
                    const tags = tree.nodes.items(.tag);
                    if (init_idx < tags.len) {
                        const init_tag = tags[init_idx];
                        if (init_tag == .@"try") {
                            return try _Builder.ErrorFlow.processVarDeclWithTry(self, cfg, source, ast_node, init_idx, prev_node, range);
                        } else if (init_tag == .@"catch") {
                            return try _Builder.ErrorFlow.processVarDeclWithCatch(self, cfg, source, ast_node, init_idx, prev_node, range);
                        } else if (init_tag == .@"switch" or init_tag == .switch_comma) {
                            return try _Builder.SwitchFlow.processVarDeclWithSwitch(self, cfg, source, ast_node, init_idx, prev_node, range);
                        }
                    }
                }
            }

            // Simple var decl without try/catch in initializer
            // Annotate with type information if available
            var ir_node = IrNode.initFull(.var_decl, ast_node, range);
            ir_node = _Builder.TypeAnnotation.annotateWithType(self, ir_node, source, ast_node);

            const decl_node = try cfg.addNode(ir_node);
            try cfg.addEdge(prev_node, decl_node);
            return .{ .last = decl_node, .terminates = false };
        }

        pub fn processAssign(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const range = try source_range.getSourceRange(source, ast_node);

            // Check if the RHS contains a try or catch expression
            // Assign node data: lhs and rhs
            const data = tree.nodes.items(.data);
            const assign_data = data[ast_node].node_and_node;
            const lhs_idx = @intFromEnum(assign_data[0]);
            const rhs_idx = @intFromEnum(assign_data[1]);
            const tags = tree.nodes.items(.tag);
            if (rhs_idx < tags.len) {
                const rhs_tag = tags[rhs_idx];
                if (rhs_tag == .@"try") {
                    return try _Builder.ErrorFlow.processAssignWithTry(self, cfg, source, ast_node, lhs_idx, rhs_idx, prev_node, range);
                } else if (rhs_tag == .@"catch") {
                    return try _Builder.ErrorFlow.processAssignWithCatch(self, cfg, source, ast_node, lhs_idx, rhs_idx, prev_node, range);
                } else if (rhs_tag == .@"switch" or rhs_tag == .switch_comma) {
                    return try _Builder.SwitchFlow.processAssignWithSwitch(self, cfg, source, ast_node, lhs_idx, rhs_idx, prev_node, range);
                }
            }

            const assign_node = try cfg.addNode(IrNode.initAssign(ast_node, lhs_idx, rhs_idx, range));
            try cfg.addEdge(prev_node, assign_node);
            return .{ .last = assign_node, .terminates = false };
        }

        pub fn processCall(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            _ = self;
            const range = try source_range.getSourceRange(source, ast_node);
            const call_node = try cfg.addNode(IrNode.initFull(.call, ast_node, range));
            try cfg.addEdge(prev_node, call_node);
            return .{ .last = call_node, .terminates = false };
        }

        pub fn processGenericExpr(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            _ = self;
            const range = try source_range.getSourceRange(source, ast_node);
            const expr_node = try cfg.addNode(IrNode.initFull(.expr, ast_node, range));
            try cfg.addEdge(prev_node, expr_node);
            return .{ .last = expr_node, .terminates = false };
        }

        /// `unreachable` is a statically dead point: any path that reaches it
        /// does not continue. Create an IR node so analyses can see the
        /// statement, attach an incoming edge, and return `terminates = true`
        /// so the surrounding block stops feeding successors. No outgoing
        /// edges are added; the engine treats a node with no successors as a
        /// dead end and stops propagating state.
        pub fn processUnreachable(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            _ = self;
            const range = try source_range.getSourceRange(source, ast_node);
            const u_node = try cfg.addNode(IrNode.initFull(.unreachable_stmt, ast_node, range));
            try cfg.addEdge(prev_node, u_node);
            return .{ .last = u_node, .terminates = true };
        }
    };
}
