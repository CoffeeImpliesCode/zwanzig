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

/// Which side of a transfer's boundary scope the `defer` unwind stops on.
const Winding = enum {
    /// The boundary scope ends too, so its defers run as well.
    through_boundary,
    /// The boundary scope keeps running, so the walk stops below it.
    up_to_boundary,
};

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
            const label_token = labelTokenBefore(tree, ast_node);
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

        /// `break [:label] [operand]`.
        ///
        /// A break ends the innermost thing the source names and lands after
        /// it: the labeled block `:label` picks, or, with no label at all or a
        /// label no block carries, the innermost open loop. The target's exit
        /// node exists before its body is walked - a loop builds its exit
        /// while it is still at the header - so a resolved break evaluates its
        /// operand, runs the `defer` bodies of the scopes it leaves, and
        /// jumps there. It does not fall through into the statement a guard
        /// was protecting, and it does not loop back either: control leaves
        /// the body, so no path out of here starts another pass over it.
        ///
        /// `:label` picks its target the way the source does, nearest first.
        /// The block chain is asked before the loop chain because a label
        /// names one of the two or the other and never both, so a block
        /// carrying it is the target and the loop chain is only left for a
        /// label that names no block - a loop's own.
        ///
        /// A transfer that leaves the deferred body being inlined is a
        /// compile error rather than a jump, and so is one whose loop frame is
        /// not on the scope chain this walk opened (see
        /// `transferLeavesDeferBody` and `scopeChainHas`). Both refuse the
        /// function rather than resolve the transfer and drop the path behind
        /// it.
        ///
        /// A break no open loop carries - one in a switch prong outside every
        /// loop - keeps the generic expression treatment: inventing a loop to
        /// jump to would drop a path and call code safe that nothing ever
        /// analyzed.
        pub fn processBreak(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const break_data = tree.nodes.items(.data)[ast_node].opt_token_and_opt_node;

            const label_token = break_data[0].unwrap() orelse 0;
            const operand: ?u32 = if (break_data[1].unwrap()) |node| @intFromEnum(node) else null;

            if (label_token != 0) {
                if (findLabeledBlock(self, tree, label_token)) |target| {
                    const target_merge = target.merge_node orelse return error.InvalidAst;
                    if (breaksOutOfDeferBody(self, target)) return error.InvalidAst;
                    return transferTo(self, cfg, source, ast_node, operand, prev_node, target, .through_boundary, target_merge);
                }
            }

            const frame = findTargetLoop(self, tree, label_token) orelse
                return try processGenericExpr(self, cfg, source, ast_node, prev_node);

            // The loop's own scope frame sits on the chain this walk opened, so
            // the unwind below stops below it and never leaves a scope the
            // break does not: the loop's body ends here, but the scope holding
            // the loop statement keeps running, which is what
            // `up_to_boundary` says. A frame off that chain would send the
            // walk past the loop itself, so refuse the function rather than
            // guess where its defers end.
            const boundary = frame.enclosing_scope;
            if (!scopeChainHas(self.current_scope, boundary)) return error.InvalidAst;
            if (transferLeavesDeferBody(self, boundary)) return error.InvalidAst;

            return transferTo(self, cfg, source, ast_node, operand, prev_node, boundary, .up_to_boundary, frame.break_target);
        }

        /// The transfer itself: the operand, the `break` node, the `defer`
        /// bodies that fire on the way out, and the jump onto `landing`.
        ///
        /// The operand is evaluated before control leaves the target, so a
        /// `break :blk 1 / x` is still analyzed. It goes through the normal
        /// expression dispatch instead of a bare node: a `try` operand keeps
        /// its error edge to the function exit, a `catch` operand keeps its
        /// handler, and only a plain expression collapses to one node.
        ///
        /// Returns the `break` node. The path after it ends on `landing`, or
        /// nowhere at all when a deferred body does not fall through, so the
        /// transfer terminates either way.
        fn transferTo(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            operand: ?u32,
            prev_node: CfgNodeId,
            boundary: ?*const _Builder.Scope,
            winding: Winding,
            landing: CfgNodeId,
        ) !_Builder.ProcessResult {
            var tail = prev_node;

            if (operand) |operand_node| {
                const edge_count_before = cfg.edges.items.len;
                const result = try self.processNode(cfg, source, operand_node, tail);
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

            const unwound = try unwindDefers(self, cfg, source, ast_node, boundary, winding, break_node) orelse
                return .{ .last = break_node, .terminates = true };

            try cfg.addEdgeWithKind(unwound, landing, .jump);

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

        /// `continue [:label]`.
        ///
        /// A continue moves control to the iteration step of the loop that
        /// encloses it: the continuation expression of a `while (c) : (step)`,
        /// or the loop header when the loop has none, and always the header of
        /// a `for`, whose header is where its next item comes from. Jumping to
        /// the header of a `while` that has a continuation would repeat the
        /// body the continue just left, and landing past the continuation
        /// would repeat the iteration without running its step, so the
        /// continuation node is built before the body is walked and the
        /// continue links to it directly.
        ///
        /// `:label` picks the loop carrying that label rather than the nearest
        /// one, so a continue inside a nested loop can leave both and land on
        /// the outer loop's step.
        ///
        /// The scopes the transfer leaves run their `defer` bodies first, and
        /// `terminates = true` stops the enclosing block from falling through
        /// into the statements behind the continue.
        ///
        /// A continue naming a label no open loop carries keeps the generic
        /// expression treatment: resolving it against some other loop would
        /// drop a path and call code safe that nothing ever analyzed.
        pub fn processContinue(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const label_token = tree.nodes.items(.data)[ast_node].opt_token_and_opt_node[0].unwrap() orelse 0;

            const frame = findTargetLoop(self, tree, label_token) orelse
                return try processGenericExpr(self, cfg, source, ast_node, prev_node);

            // The loop's own scope frame sits on the chain this walk opened, so
            // the unwind below stops below it and never leaves a scope the
            // continue does not. A frame off that chain would send the walk
            // past the loop itself, so refuse the function rather than guess
            // where its defers end.
            const boundary = frame.enclosing_scope;
            if (!scopeChainHas(self.current_scope, boundary)) return error.InvalidAst;

            // A transfer that leaves the deferred body being inlined is a
            // compile error, not a jump.
            if (transferLeavesDeferBody(self, boundary)) return error.InvalidAst;

            // The transfer is carried by the loop back edge below and by
            // `terminates`, so the node keeps the plain expression tag the
            // statement already carried: an analysis that reads an expression
            // node as doing no computation keeps that reading of it.
            const continue_range = try source_range.getSourceRange(source, ast_node);
            const continue_node = try cfg.addNode(IrNode.initFull(.expr, ast_node, continue_range));
            try cfg.addEdge(prev_node, continue_node);

            const unwound = try unwindDefers(self, cfg, source, ast_node, boundary, .up_to_boundary, continue_node);
            const tail = unwound orelse return .{ .last = continue_node, .terminates = true };

            try cfg.addEdgeWithKind(tail, frame.continue_target, .loop_back);

            return .{ .last = continue_node, .terminates = true };
        }

        /// The loop a continue transfers to: the innermost open loop, or, when
        /// a label is named, the innermost open loop carrying that label. The
        /// label wins over proximity, so `outer: while (...) { while (...) {
        /// continue :outer; } }` leaves the inner loop, and a label no open
        /// loop carries has no target at all.
        fn findTargetLoop(self: *_Builder, tree: *const std.zig.Ast, label_token: u32) ?*const _Builder.LoopFrame {
            if (label_token == 0) return self.current_loop;
            var frame = self.current_loop;
            while (frame) |entry| {
                if (entry.label_token != 0 and labelsMatch(tree, entry.label_token, label_token)) return entry;
                frame = entry.parent;
            }
            return null;
        }

        /// True when a transfer out of the loop holding `boundary` leaves the
        /// deferred body currently being inlined. Zig rejects such a transfer,
        /// so the function is refused rather than turned into a jump that drops
        /// a path and calls what follows proven safe. The body is left exactly
        /// when the scope holding the loop is not at or below the scope owning
        /// the body: a loop the body is written inside can be left, a loop
        /// written around it cannot.
        fn transferLeavesDeferBody(self: *_Builder, boundary: ?*const _Builder.Scope) bool {
            const defer_scope = self.defer_boundary orelse return false;
            var scope = boundary;
            while (scope) |entry| {
                if (entry == defer_scope) return false;
                scope = entry.parent;
            }
            return true;
        }

        /// True when `needle` is one of the scopes currently open. A transfer
        /// relies on this to know its unwind ends where the source says it
        /// does, so a scope it cannot account for means the frame and the
        /// scope chain disagree and nothing safe can be built.
        fn scopeChainHas(chain: ?*const _Builder.Scope, needle: ?*const _Builder.Scope) bool {
            if (needle == null) return false;
            var scope = chain;
            while (scope) |entry| {
                if (entry == needle) return true;
                scope = entry.parent;
            }
            return false;
        }

        /// Chain the `defer` bodies that fire while a transfer leaves the
        /// scopes it passes: innermost scope first, and within a scope in
        /// reverse declaration order. Only defers the transfer had already
        /// reached count - one declared after it never runs on this path -
        /// and `errdefer` bodies stay out, because neither a `break` nor a
        /// `continue` is an error path.
        ///
        /// `winding` decides what happens to the boundary scope itself. A
        /// labeled break ends the block it targets, so that block's defers
        /// run too; a `continue` leaves the scope that holds its loop running,
        /// so the walk stops below that scope.
        ///
        /// Returns the last node built, or null when the path genuinely stops:
        /// a deferred body that does not fall through.
        fn unwindDefers(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            transfer_ast_node: u32,
            boundary: ?*const _Builder.Scope,
            winding: Winding,
            from: CfgNodeId,
        ) !?CfgNodeId {
            const tree = try source.ast();
            const transfer_start = nodeStartOffset(tree, transfer_ast_node);

            var tail = from;
            var scope = self.current_scope;
            while (scope) |entry| {
                if (winding == .up_to_boundary and entry == boundary) break;
                tail = (try emitScopeDefers(self, cfg, source, entry, transfer_start, tail)) orelse
                    return null;
                if (winding == .through_boundary and entry == boundary) break;
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

        /// Token index of the label identifier written in front of a node's
        /// own keyword - a block's `{` or a loop's keyword - or 0 when it
        /// carries no label. The label sits two tokens earlier, behind the
        /// colon that separates it from what it names.
        pub fn labelTokenBefore(tree: *const std.zig.Ast, ast_node: u32) u32 {
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

        /// The expression a statement hands to the control flow, looking
        /// through the parentheses it may be written in.
        ///
        /// Parentheses are not a separate expression: `x = (a() catch b());`
        /// has to split that `catch`'s arms exactly as `x = a() catch b();`
        /// does, because which arm ran is what decides what the path still
        /// owns. A `return`, a declaration's initializer and an assignment's
        /// right-hand side all dispatch on this, so all three look through the
        /// same group rather than each deciding on its own whether a
        /// parenthesis is an expression of its own.
        ///
        /// Only the operand the dispatch reads changes here. The statement's
        /// own AST node and the range every diagnostic carries stay the ones
        /// the statement was written with, and the node the fallthrough below
        /// builds is assembled from exactly those, as it was before.
        ///
        /// Every step is a parenthesis handing over the one expression it
        /// holds, so the walk only ever moves further into the tree and ends.
        fn transparentOperand(tree: *const std.zig.Ast, operand_node: u32) u32 {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            var current = operand_node;
            while (current < tags.len and tags[current] == .grouped_expression) {
                current = @intFromEnum(datas[current].node_and_token[0]);
            }
            return current;
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
                const ret_expr_idx = transparentOperand(tree, @intFromEnum(ret_expr_node));
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
                    const init_idx = transparentOperand(tree, @intFromEnum(init_node));
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
            const rhs_idx = transparentOperand(tree, @intFromEnum(assign_data[1]));
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

// Colocated CFG tests.
//
// A continue shows up only in the graph it builds, so these drive the builder
// over real source and read the transitions it produced back out of the CFG.

const CfgBuilder = @import("../builder.zig").CfgBuilder;

/// CFG of the first function declared in `source`.
fn cfgOf(allocator: std.mem.Allocator, source: *Source) !?Cfg {
    var builder = CfgBuilder.init(allocator);
    const tree = try source.ast();
    const root_decls = tree.rootDecls();
    if (root_decls.len == 0) return null;
    return builder.buildFromFn(source, ids.astId(@intFromEnum(root_decls[0])));
}

/// Body block of the first function declared in `tree`.
fn firstFnBody(tree: *const std.zig.Ast) ?u32 {
    const root_decls = tree.rootDecls();
    if (root_decls.len == 0) return null;
    const fn_node: u32 = @intFromEnum(root_decls[0]);
    return @intFromEnum(tree.nodes.items(.data)[fn_node].node_and_node[1]);
}

/// The `index`-th statement in the requested AST family directly inside `block`.
fn nthStatement(tree: *const std.zig.Ast, block: u32, tag: std.zig.Ast.Node.Tag, index: usize) ?u32 {
    var block_buffer: [2]u32 = undefined;
    var seen: usize = 0;
    for (ast_walk.getBlockStatements(tree, block, &block_buffer) orelse return null) |stmt| {
        const matches = switch (tag) {
            .@"while" => tree.fullWhile(@enumFromInt(stmt)) != null,
            .@"for" => tree.fullFor(@enumFromInt(stmt)) != null,
            .@"if" => tree.fullIf(@enumFromInt(stmt)) != null,
            .local_var_decl => tree.fullVarDecl(@enumFromInt(stmt)) != null,
            else => tree.nodes.items(.tag)[stmt] == tag,
        };
        if (!matches) continue;
        if (seen == index) return stmt;
        seen += 1;
    }
    return null;
}

/// The `index`-th `continue` statement in the file.
fn nthContinue(tree: *const std.zig.Ast, index: usize) ?u32 {
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, node| {
        if (tag != .@"continue") continue;
        if (seen == index) return @intCast(node);
        seen += 1;
    }
    return null;
}

/// The `index`-th `break` statement in the file.
fn nthBreak(tree: *const std.zig.Ast, index: usize) ?u32 {
    var seen: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, node| {
        if (tag != .@"break") continue;
        if (seen == index) return @intCast(node);
        seen += 1;
    }
    return null;
}

/// The `index`-th call in `block`, whatever arity spelling it was written in.
fn nthCall(tree: *const std.zig.Ast, block: u32, index: usize) ?u32 {
    var block_buffer: [2]u32 = undefined;
    var seen: usize = 0;
    for (ast_walk.getBlockStatements(tree, block, &block_buffer) orelse return null) |stmt| {
        switch (tree.nodes.items(.tag)[stmt]) {
            .call, .call_comma, .call_one, .call_one_comma, .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => continue,
        }
        if (seen == index) return stmt;
        seen += 1;
    }
    return null;
}

/// The body block of the `while` at `ast_node`.
fn whileBody(tree: *const std.zig.Ast, ast_node: u32) ?u32 {
    const full = tree.fullWhile(@enumFromInt(ast_node)) orelse return null;
    return @intFromEnum(full.ast.then_expr);
}

/// The continuation expression of the `while` at `ast_node`.
fn whileContExpr(tree: *const std.zig.Ast, ast_node: u32) ?u32 {
    const full = tree.fullWhile(@enumFromInt(ast_node)) orelse return null;
    const cont = full.ast.cont_expr.unwrap() orelse return null;
    return @intFromEnum(cont);
}

/// The single CFG node built for `ast_node` carrying `tag`.
fn nodeFor(cfg: *const Cfg, ast_node: u32, tag: IrTag) ?CfgNodeId {
    for (cfg.nodes.items) |node| {
        if (node.ir_node.tag != tag) continue;
        const built = node.ir_node.ast_node orelse continue;
        if (built == ast_node) return node.index;
    }
    return null;
}

/// The one CFG node carrying `tag`, or null when the graph holds more or
/// fewer of them.
fn onlyNodeWith(cfg: *const Cfg, tag: IrTag) ?CfgNodeId {
    var found: ?CfgNodeId = null;
    for (cfg.nodes.items) |node| {
        if (node.ir_node.tag != tag) continue;
        if (found != null) return null;
        found = node.index;
    }
    return found;
}

/// The one edge leaving `from`, or null when it leaves more than one or none.
fn onlyEdge(cfg: *const Cfg, from: CfgNodeId) ?graph.CfgEdge {
    var found: ?graph.CfgEdge = null;
    for (cfg.edges.items) |edge| {
        if (edge.from != from) continue;
        if (found != null) return null;
        found = edge;
    }
    return found;
}

/// The single edge of `kind` leaving `from`, or null when it leaves more than
/// one of that kind or none.
fn onlyEdgeOfKind(cfg: *const Cfg, from: CfgNodeId, kind: EdgeKind) ?graph.CfgEdge {
    var found: ?graph.CfgEdge = null;
    for (cfg.edges.items) |edge| {
        if (edge.from != from or edge.kind != kind) continue;
        if (found != null) return null;
        found = edge;
    }
    return found;
}

/// The single edge of `kind` running into `to`, or null when more than one of
/// that kind arrives or none does.
fn onlyEdgeIntoOfKind(cfg: *const Cfg, to: CfgNodeId, kind: EdgeKind) ?graph.CfgEdge {
    var found: ?graph.CfgEdge = null;
    for (cfg.edges.items) |edge| {
        if (edge.to != to or edge.kind != kind) continue;
        if (found != null) return null;
        found = edge;
    }
    return found;
}

/// How many edges leave `from`.
fn outgoingEdges(cfg: *const Cfg, from: CfgNodeId) usize {
    var count: usize = 0;
    for (cfg.edges.items) |edge| {
        if (edge.from == from) count += 1;
    }
    return count;
}

/// Kind of the edge from `from` into `to`, or null when there is none.
fn edgeKind(cfg: *const Cfg, from: CfgNodeId, to: CfgNodeId) ?EdgeKind {
    for (cfg.edges.items) |edge| {
        if (edge.from == from and edge.to == to) return edge.kind;
    }
    return null;
}

fn incomingEdges(cfg: *const Cfg, to: CfgNodeId) usize {
    var count: usize = 0;
    for (cfg.edges.items) |edge| {
        if (edge.to == to) count += 1;
    }
    return count;
}

/// Walk the single-successor path out of `from`, stopping when it forks or
/// dead-ends, or once `limit` nodes have been collected. `from` comes first.
fn solePath(allocator: std.mem.Allocator, cfg: *const Cfg, from: CfgNodeId, limit: usize) ![]CfgNodeId {
    var path: std.ArrayList(CfgNodeId) = .empty;
    errdefer path.deinit(allocator);
    try path.append(allocator, from);
    while (path.items.len < limit) {
        const edge = onlyEdge(cfg, path.items[path.items.len - 1]) orelse break;
        try path.append(allocator, edge.to);
    }
    return path.toOwnedSlice(allocator);
}

fn indexOfPath(path: []const CfgNodeId, node: CfgNodeId) ?usize {
    for (path, 0..) |entry, index| {
        if (entry == node) return index;
    }
    return null;
}

test "a continue in a while body links to the continuation expression" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var x: i32 = 0;
        \\    while (x < 10) : (x += 1) {
        \\        if (x == 3) continue;
        \\        x += 2;
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const while_node = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const header = nodeFor(&cfg, while_node, .loop_header) orelse return error.TestUnexpectedResult;
    const cont_ast = whileContExpr(tree, while_node) orelse return error.TestUnexpectedResult;
    const increment = nodeFor(&cfg, cont_ast, .expr) orelse return error.TestUnexpectedResult;
    const continue_ast = nthContinue(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, continue_ast, .expr) orelse return error.TestUnexpectedResult;

    // The back edge lands on `x += 1` rather than on the header: running the
    // continuation is what makes the next pass a new iteration.
    const step = onlyEdge(&cfg, transfer) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.loop_back, step.kind);
    try testing.expectEqual(increment, step.to);
    try testing.expect(increment != header);

    // The continuation then loops back to the header, so the condition is
    // tested again only once the increment has run.
    const back = onlyEdge(&cfg, increment) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.loop_back, back.kind);
    try testing.expectEqual(header, back.to);
}

test "an unconditional continue still starts the next iteration" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Both arms fall through to the same `continue`, so no path out of the
    // body does: the step is reached only through the transfer, and it is
    // left only by running it.
    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var x: i32 = 0;
        \\    while (x < 10) : (x += 1) {
        \\        if (x == 3) {
        \\            record(x);
        \\        } else {
        \\            skip(x);
        \\        }
        \\        continue;
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const while_node = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const header = nodeFor(&cfg, while_node, .loop_header) orelse return error.TestUnexpectedResult;
    const body_ast = whileBody(tree, while_node) orelse return error.TestUnexpectedResult;
    const body = nodeFor(&cfg, body_ast, .loop_body) orelse return error.TestUnexpectedResult;
    const cont_ast = whileContExpr(tree, while_node) orelse return error.TestUnexpectedResult;
    const increment = nodeFor(&cfg, cont_ast, .expr) orelse return error.TestUnexpectedResult;
    const continue_ast = nthContinue(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, continue_ast, .expr) orelse return error.TestUnexpectedResult;

    // The transfer runs the step and the step loops back, so the next pass
    // starts instead of the transfer dead-ending on the continuation.
    try testing.expectEqual(increment, onlyEdge(&cfg, transfer).?.to);
    const back = onlyEdgeOfKind(&cfg, increment, .loop_back) orelse
        return error.TestUnexpectedResult;
    try testing.expectEqual(header, back.to);

    // Only the explicit continue reaches the step; the terminating body
    // cannot bypass its statements through a fallthrough edge.
    try testing.expectEqual(increment, onlyEdgeIntoOfKind(&cfg, header, .loop_back).?.from);
    try testing.expect(edgeKind(&cfg, body, header) == null);
    try testing.expectEqual(@as(usize, 1), incomingEdges(&cfg, increment));
    try testing.expect(edgeKind(&cfg, body, increment) == null);

    // The header still forks the pass in two: the condition sends it into the
    // body, and the other way out is the exit.
    try testing.expectEqual(@as(usize, 2), outgoingEdges(&cfg, header));
    try testing.expectEqual(EdgeKind.branch_true, edgeKind(&cfg, header, body).?);
    try testing.expect(onlyEdgeOfKind(&cfg, header, .loop_exit).?.to != increment);
}

test "a continue does not fall through into the statements behind it" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo(items: []const i32) void {
        \\    for (items) |item| {
        \\        if (item == 0) continue;
        \\        consume(item);
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const for_node = nthStatement(tree, fn_body, .@"for", 0) orelse
        return error.TestUnexpectedResult;
    const header = nodeFor(&cfg, for_node, .loop_header) orelse return error.TestUnexpectedResult;
    const continue_ast = nthContinue(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, continue_ast, .expr) orelse return error.TestUnexpectedResult;
    const consume_call = onlyNodeWith(&cfg, .call) orelse return error.TestUnexpectedResult;

    // A for loop takes its next item at the header, so that is where the
    // continue goes, and it goes there alone.
    const step = onlyEdge(&cfg, transfer) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.loop_back, step.kind);
    try testing.expectEqual(header, step.to);

    // The statement behind the continue is reachable only from the arm that
    // did not continue.
    try testing.expect(edgeKind(&cfg, transfer, consume_call) == null);
    try testing.expectEqual(@as(usize, 1), incomingEdges(&cfg, consume_call));
}

test "a continue releases the defers of the scopes it leaves" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo(x: i32) void {
        \\    while (x > 0) : (x -= 1) {
        \\        defer {
        \\            const outer = 1;
        \\            _ = outer;
        \\        }
        \\        if (x == 2) {
        \\            defer {
        \\                const inner = 2;
        \\                _ = inner;
        \\            }
        \\            continue;
        \\        }
        \\        consume(x);
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const while_node = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const cont_ast = whileContExpr(tree, while_node) orelse return error.TestUnexpectedResult;
    const increment = nodeFor(&cfg, cont_ast, .expr) orelse return error.TestUnexpectedResult;
    const continue_ast = nthContinue(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, continue_ast, .expr) orelse return error.TestUnexpectedResult;

    const body = whileBody(tree, while_node) orelse return error.TestUnexpectedResult;
    const if_node = nthStatement(tree, body, .@"if", 0) orelse return error.TestUnexpectedResult;
    const then_full = tree.fullIf(@enumFromInt(if_node)) orelse return error.TestUnexpectedResult;
    const then_body = @intFromEnum(then_full.ast.then_expr);
    const inner_defer = nthStatement(tree, then_body, .@"defer", 0) orelse
        return error.TestUnexpectedResult;
    const inner_decl_ast = deferBodyDecl(tree, inner_defer) orelse
        return error.TestUnexpectedResult;
    const inner_decl = nodeFor(&cfg, inner_decl_ast, .var_decl) orelse
        return error.TestUnexpectedResult;
    const outer_defer = nthStatement(tree, body, .@"defer", 0) orelse
        return error.TestUnexpectedResult;
    const outer_decl_ast = deferBodyDecl(tree, outer_defer) orelse
        return error.TestUnexpectedResult;
    const outer_decl = nodeFor(&cfg, outer_decl_ast, .var_decl) orelse
        return error.TestUnexpectedResult;

    // Every hop out of the continue runs one of those bodies and none of them
    // offers a way out, so the path runs inner then outer and reaches the loop
    // continuation through a loop back edge.
    const path = try solePath(allocator, &cfg, transfer, 32);
    defer allocator.free(path);
    const step = indexOfPath(path, increment) orelse return error.TestUnexpectedResult;
    try testing.expect(step > 0);
    try testing.expect(indexOfPath(path, inner_decl) != null);
    try testing.expect(indexOfPath(path, outer_decl) != null);
    try testing.expect(indexOfPath(path, inner_decl).? < indexOfPath(path, outer_decl).?);
    try testing.expectEqual(EdgeKind.loop_back, edgeKind(&cfg, path[step - 1], increment).?);
}

/// The declaration a `defer` at `ast_node` guards.
fn deferBodyDecl(tree: *const std.zig.Ast, ast_node: u32) ?u32 {
    const body = @intFromEnum(tree.nodes.items(.data)[ast_node].node);
    return nthStatement(tree, body, .local_var_decl, 0);
}

test "a labeled continue leaves the inner loop" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var x: i32 = 0;
        \\    outer: while (x < 10) : (x += 1) {
        \\        inner: while (x < 5) : (x += 2) {
        \\            if (x == 2) continue :outer;
        \\        }
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const outer = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const outer_body = whileBody(tree, outer) orelse return error.TestUnexpectedResult;
    const inner = nthStatement(tree, outer_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const outer_cont = whileContExpr(tree, outer) orelse return error.TestUnexpectedResult;
    const outer_step = nodeFor(&cfg, outer_cont, .expr) orelse
        return error.TestUnexpectedResult;
    const inner_cont = whileContExpr(tree, inner) orelse return error.TestUnexpectedResult;
    const inner_step = nodeFor(&cfg, inner_cont, .expr) orelse
        return error.TestUnexpectedResult;
    const continue_ast = nthContinue(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, continue_ast, .expr) orelse return error.TestUnexpectedResult;

    // The label names the outer loop, so the transfer leaves both loops and
    // lands on the outer one's step instead of the inner one's.
    const step = onlyEdge(&cfg, transfer) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.loop_back, step.kind);
    try testing.expectEqual(outer_step, step.to);
    try testing.expect(step.to != inner_step);
    try testing.expect(step.to != nodeFor(&cfg, inner, .loop_header).?);
}

test "a loop's else branch continues the loop around it" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Zig refuses a continue in a loop's else branch; this pins how the
    // builder reads one. The loop's own context covers its body, so a
    // continue in the else branch belongs to the enclosing loop.
    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var x: i32 = 0;
        \\    while (x < 10) : (x += 1) {
        \\        while (x < 5) : (x += 2) {
        \\            x += 1;
        \\        } else {
        \\            continue;
        \\        }
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const outer = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const outer_body = whileBody(tree, outer) orelse return error.TestUnexpectedResult;
    const inner = nthStatement(tree, outer_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const outer_cont = whileContExpr(tree, outer) orelse return error.TestUnexpectedResult;
    const outer_step = nodeFor(&cfg, outer_cont, .expr) orelse
        return error.TestUnexpectedResult;
    const inner_cont = whileContExpr(tree, inner) orelse return error.TestUnexpectedResult;
    const inner_step = nodeFor(&cfg, inner_cont, .expr) orelse
        return error.TestUnexpectedResult;
    const continue_ast = nthContinue(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, continue_ast, .expr) orelse return error.TestUnexpectedResult;

    try testing.expectEqual(outer_step, onlyEdge(&cfg, transfer).?.to);
    try testing.expect(outer_step != inner_step);
}

test "a continue whose label no open loop carries keeps falling through" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var x: i32 = 0;
        \\    while (x < 10) : (x += 1) {
        \\        continue :missing;
        \\        consume(x);
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const while_node = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const header = nodeFor(&cfg, while_node, .loop_header) orelse return error.TestUnexpectedResult;
    const cont_ast = whileContExpr(tree, while_node) orelse return error.TestUnexpectedResult;
    const increment = nodeFor(&cfg, cont_ast, .expr) orelse return error.TestUnexpectedResult;
    const continue_ast = nthContinue(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, continue_ast, .expr) orelse return error.TestUnexpectedResult;
    const consumer = onlyNodeWith(&cfg, .call) orelse return error.TestUnexpectedResult;

    // Nothing binds `:missing`, so the builder keeps the expression it always
    // was rather than invent a loop to jump to: the consumer behind it is
    // still reached, and the loop still runs its continuation from the tail.
    try testing.expectEqual(EdgeKind.normal, onlyEdge(&cfg, transfer).?.kind);
    try testing.expectEqual(consumer, onlyEdge(&cfg, transfer).?.to);
    try testing.expect(edgeKind(&cfg, transfer, header) == null);
    try testing.expectEqual(EdgeKind.normal, edgeKind(&cfg, consumer, increment).?);
}

test "each loop's continue targets that loop after an earlier loop closed" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var x: i32 = 0;
        \\    while (x < 10) : (x += 1) {
        \\        if (x == 3) continue;
        \\        x += 2;
        \\    }
        \\    var y: i32 = 0;
        \\    while (y < 10) : (y += 1) {
        \\        if (y == 3) continue;
        \\        y += 2;
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const first_loop = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const first_cont = whileContExpr(tree, first_loop) orelse return error.TestUnexpectedResult;
    const first_step = nodeFor(&cfg, first_cont, .expr) orelse return error.TestUnexpectedResult;
    const second_loop = nthStatement(tree, fn_body, .@"while", 1) orelse
        return error.TestUnexpectedResult;
    const second_cont = whileContExpr(tree, second_loop) orelse
        return error.TestUnexpectedResult;
    const second_step = nodeFor(&cfg, second_cont, .expr) orelse
        return error.TestUnexpectedResult;

    // The first loop's context is put back when it closes, so the second
    // loop's continue reaches the second loop and not the first.
    const early_ast = nthContinue(tree, 0) orelse return error.TestUnexpectedResult;
    const early = nodeFor(&cfg, early_ast, .expr) orelse return error.TestUnexpectedResult;
    const late_ast = nthContinue(tree, 1) orelse return error.TestUnexpectedResult;
    const late = nodeFor(&cfg, late_ast, .expr) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(first_step, onlyEdge(&cfg, early).?.to);
    try testing.expectEqual(second_step, onlyEdge(&cfg, late).?.to);
}

test "an unlabeled break leaves the loop instead of running the body again" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var i: i32 = 0;
        \\    while (i < 10) : (i += 1) {
        \\        record(i);
        \\        break;
        \\        consume(i);
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const while_node = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const body = whileBody(tree, while_node) orelse return error.TestUnexpectedResult;
    const header = nodeFor(&cfg, while_node, .loop_header) orelse return error.TestUnexpectedResult;
    const cont_ast = whileContExpr(tree, while_node) orelse return error.TestUnexpectedResult;
    const increment = nodeFor(&cfg, cont_ast, .expr) orelse return error.TestUnexpectedResult;
    const break_ast = nthBreak(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, break_ast, .break_stmt) orelse return error.TestUnexpectedResult;

    // The one way out of the break is the loop's own exit - the node the header
    // takes when the condition runs out - and not a step back into the body it
    // just left.
    const exit = onlyEdge(&cfg, transfer) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.jump, exit.kind);
    try testing.expectEqual(onlyEdgeOfKind(&cfg, header, .loop_exit).?.to, exit.to);
    try testing.expect(edgeKind(&cfg, transfer, header) == null);

    // The body ends at the break, so nothing falls through into the step and
    // the loop cannot run a second pass over what it already did.
    try testing.expectEqual(@as(usize, 0), incomingEdges(&cfg, increment));

    // What the break left behind is never built, so no path through the loop
    // reaches it, while the call in front of it is.
    try testing.expect(nodeFor(&cfg, nthCall(tree, body, 0).?, .call) != null);
    try testing.expect(nodeFor(&cfg, nthCall(tree, body, 1).?, .call) == null);
}

test "a break leaves the innermost loop and the flow carries on after it" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var x: i32 = 0;
        \\    outer: while (x < 10) : (x += 1) {
        \\        inner: while (x < 5) : (x += 2) {
        \\            if (x == 2) break;
        \\            consume(x);
        \\        }
        \\        after_inner(x);
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const outer = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const outer_body = whileBody(tree, outer) orelse return error.TestUnexpectedResult;
    const inner = nthStatement(tree, outer_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const inner_header = nodeFor(&cfg, inner, .loop_header) orelse
        return error.TestUnexpectedResult;
    const inner_cont = whileContExpr(tree, inner) orelse return error.TestUnexpectedResult;
    const inner_step = nodeFor(&cfg, inner_cont, .expr) orelse return error.TestUnexpectedResult;
    const break_ast = nthBreak(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, break_ast, .break_stmt) orelse return error.TestUnexpectedResult;

    // Proximity picks the loop: the break ends the inner one, so it lands on
    // that loop's exit and not on the exit of the one written around it.
    const exit = onlyEdge(&cfg, transfer) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.jump, exit.kind);
    const inner_exit_edge = onlyEdgeOfKind(&cfg, inner_header, .loop_exit) orelse
        return error.TestUnexpectedResult;
    const inner_exit = inner_exit_edge.to;
    try testing.expectEqual(inner_exit, exit.to);
    try testing.expect(exit.to != onlyEdgeOfKind(&cfg, nodeFor(&cfg, outer, .loop_header).?, .loop_exit).?.to);

    // The arm that did not break still runs the next pass, so the transfer
    // ends one path out of the loop rather than the loop itself.
    const back = onlyEdgeIntoOfKind(&cfg, inner_header, .loop_back) orelse
        return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.loop_back, back.kind);
    try testing.expectEqual(inner_step, back.from);

    // Leaving the inner loop is not leaving the outer one: the statement
    // behind the inner loop is reached from the node the break landed on, and
    // from nowhere else.
    const after_call_ast = nthCall(tree, outer_body, 0) orelse return error.TestUnexpectedResult;
    const after_inner = nodeFor(&cfg, after_call_ast, .call) orelse
        return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.normal, edgeKind(&cfg, inner_exit, after_inner).?);
    try testing.expectEqual(@as(usize, 1), incomingEdges(&cfg, after_inner));
}

test "a break leaves the loop its own label names" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo() void {
        \\    var x: i32 = 0;
        \\    outer: while (x < 10) : (x += 1) {
        \\        while (x < 5) : (x += 2) {
        \\            if (x == 2) break :outer;
        \\        }
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const outer = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const outer_body = whileBody(tree, outer) orelse return error.TestUnexpectedResult;
    const inner = nthStatement(tree, outer_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const break_ast = nthBreak(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, break_ast, .break_stmt) orelse return error.TestUnexpectedResult;

    // The label names the outer loop, so the break leaves both of them and
    // lands on the outer one's exit instead of the inner one's.
    const exit = onlyEdge(&cfg, transfer) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(EdgeKind.jump, exit.kind);
    try testing.expectEqual(onlyEdgeOfKind(&cfg, nodeFor(&cfg, outer, .loop_header).?, .loop_exit).?.to, exit.to);
    try testing.expect(exit.to != onlyEdgeOfKind(&cfg, nodeFor(&cfg, inner, .loop_header).?, .loop_exit).?.to);
}

test "a break runs the defers of the scopes it leaves and lands after the loop" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const code: [:0]const u8 =
        \\fn foo(x: i32) void {
        \\    while (x > 0) : (x -= 1) {
        \\        defer {
        \\            const outer = 1;
        \\            _ = outer;
        \\        }
        \\        if (x == 2) {
        \\            defer {
        \\                const inner = 2;
        \\                _ = inner;
        \\            }
        \\            break;
        \\        }
        \\        consume(x);
        \\    }
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const while_node = nthStatement(tree, fn_body, .@"while", 0) orelse
        return error.TestUnexpectedResult;
    const header = nodeFor(&cfg, while_node, .loop_header) orelse return error.TestUnexpectedResult;
    const break_ast = nthBreak(tree, 0) orelse return error.TestUnexpectedResult;
    const transfer = nodeFor(&cfg, break_ast, .break_stmt) orelse return error.TestUnexpectedResult;

    const body = whileBody(tree, while_node) orelse return error.TestUnexpectedResult;
    const if_node = nthStatement(tree, body, .@"if", 0) orelse return error.TestUnexpectedResult;
    const then_full = tree.fullIf(@enumFromInt(if_node)) orelse return error.TestUnexpectedResult;
    const then_body = @intFromEnum(then_full.ast.then_expr);
    const inner_defer = nthStatement(tree, then_body, .@"defer", 0) orelse
        return error.TestUnexpectedResult;
    const inner_decl_ast = deferBodyDecl(tree, inner_defer) orelse
        return error.TestUnexpectedResult;
    const inner_decl = nodeFor(&cfg, inner_decl_ast, .var_decl) orelse
        return error.TestUnexpectedResult;
    const outer_defer = nthStatement(tree, body, .@"defer", 0) orelse
        return error.TestUnexpectedResult;
    const outer_decl_ast = deferBodyDecl(tree, outer_defer) orelse
        return error.TestUnexpectedResult;
    const outer_decl = nodeFor(&cfg, outer_decl_ast, .var_decl) orelse
        return error.TestUnexpectedResult;

    // The path out of the break runs the body scopes' defers innermost first
    // and ends on the loop's exit. The scope holding the loop keeps running,
    // so a break stops there and not one scope further out.
    const path = try solePath(allocator, &cfg, transfer, 32);
    defer allocator.free(path);
    const exit_edge = onlyEdgeOfKind(&cfg, header, .loop_exit) orelse
        return error.TestUnexpectedResult;
    const exit = indexOfPath(path, exit_edge.to) orelse return error.TestUnexpectedResult;
    try testing.expect(exit > 0);
    try testing.expect(indexOfPath(path, inner_decl) != null);
    try testing.expect(indexOfPath(path, outer_decl) != null);
    try testing.expect(indexOfPath(path, inner_decl).? < indexOfPath(path, outer_decl).?);
    try testing.expect(indexOfPath(path, outer_decl).? < exit);
    try testing.expectEqual(EdgeKind.jump, edgeKind(&cfg, path[exit - 1], path[exit]).?);
}

test "a break no open loop carries keeps falling through" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // The prong of a switch outside every loop: nothing here can be resolved
    // to a loop, so the builder keeps the expression the statement always was
    // rather than invent a loop to jump to.
    const code: [:0]const u8 =
        \\fn foo(x: i32) void {
        \\    switch (x) {
        \\        0 => {
        \\            record(x);
        \\            break;
        \\        },
        \\        else => {}
        \\    }
        \\    consume(x);
        \\}
    ;

    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
    defer cfg.deinit();

    const tree = try source.ast();
    const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
    const switch_node = nthStatement(tree, fn_body, .@"switch", 0) orelse
        return error.TestUnexpectedResult;
    const prong = tree.switchFull(@enumFromInt(switch_node)).ast.cases[0];
    const prong_full = tree.fullSwitchCase(prong) orelse return error.TestUnexpectedResult;
    const target = @intFromEnum(prong_full.ast.target_expr);
    const break_node = nthBreak(tree, 0) orelse return error.TestUnexpectedResult;

    // Nothing binds the transfer, so it is not the terminator a resolved path
    // is built from: it stays an expression the statements behind it are
    // reached through, while the call in front of it keeps its own node.
    try testing.expect(nodeFor(&cfg, break_node, .break_stmt) == null);
    try testing.expect(nodeFor(&cfg, nthCall(tree, target, 0).?, .call) != null);

    const transfer = nodeFor(&cfg, break_node, .expr) orelse return error.TestUnexpectedResult;
    const call_ast = nthCall(tree, fn_body, 0) orelse return error.TestUnexpectedResult;
    const consume = nodeFor(&cfg, call_ast, .call) orelse return error.TestUnexpectedResult;
    // The arm ends at the switch merge, and the merge is what reaches the
    // post-switch call: the break falls through its own arm, not past the
    // whole statement.
    const merge_edge = onlyEdge(&cfg, transfer) orelse return error.TestUnexpectedResult;
    const merge = merge_edge.to;
    try testing.expectEqual(EdgeKind.normal, onlyEdge(&cfg, transfer).?.kind);
    try testing.expectEqual(consume, onlyEdge(&cfg, merge).?.to);
}

test "loop breaks reach postloop calls but terminating else branches do not" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const cases = [_]struct {
        code: [:0]const u8,
        loop_tag: std.zig.Ast.Node.Tag,
    }{
        .{
            .code =
            \\fn foo(condition: bool) void {
            \\    while (condition) { break; } else { return; }
            \\    observe();
            \\}
            ,
            .loop_tag = .@"while",
        },
        .{
            .code =
            \\fn foo(items: []const u8) void {
            \\    for (items) |_| { break; } else { return; }
            \\    observe();
            \\}
            ,
            .loop_tag = .@"for",
        },
    };
    for (cases) |case| {
        var source = Source.init(allocator, "test.zig", case.code);
        defer source.deinit();
        var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
        defer cfg.deinit();
        const tree = try source.ast();
        const body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
        const loop_ast = nthStatement(tree, body, case.loop_tag, 0) orelse
            return error.TestUnexpectedResult;
        const header = nodeFor(&cfg, loop_ast, .loop_header) orelse
            return error.TestUnexpectedResult;
        const call_ast = nthCall(tree, body, 0) orelse return error.TestUnexpectedResult;
        const call = nodeFor(&cfg, call_ast, .call) orelse return error.TestUnexpectedResult;
        const break_ast = nthBreak(tree, 0) orelse return error.TestUnexpectedResult;
        const transfer = nodeFor(&cfg, break_ast, .break_stmt) orelse
            return error.TestUnexpectedResult;
        const transfer_edge = onlyEdge(&cfg, transfer) orelse return error.TestUnexpectedResult;
        const exit = transfer_edge.to;
        try testing.expectEqual(EdgeKind.jump, onlyEdge(&cfg, transfer).?.kind);
        try testing.expectEqual(call, onlyEdge(&cfg, exit).?.to);
        try testing.expectEqual(@as(usize, 1), incomingEdges(&cfg, exit));

        const exit_edge = onlyEdgeOfKind(&cfg, header, .loop_exit) orelse
            return error.TestUnexpectedResult;
        const else_entry = exit_edge.to;
        const path = try solePath(allocator, &cfg, else_entry, cfg.nodes.items.len + 1);
        defer allocator.free(path);
        try testing.expect(indexOfPath(path, exit) == null);
        try testing.expect(indexOfPath(path, call) == null);
        var saw_return = false;
        for (path) |node| {
            const path_node = cfg.getNode(node) orelse return error.TestUnexpectedResult;
            if (path_node.ir_node.tag == .ret) saw_return = true;
        }
        try testing.expect(saw_return);
    }
}

test "loops with terminal else and no break stop postloop construction" {
    const testing = std.testing;
    const allocator = testing.allocator;
    const cases = [_][:0]const u8{
        \\fn foo(condition: bool) void {
        \\    while (condition) { work(); } else { return; }
        \\    observe();
        \\}
        ,
        \\fn foo(items: []const u8) void {
        \\    for (items) |_| { work(); } else { return; }
        \\    observe();
        \\}
        ,
    };
    for (cases) |code| {
        var source = Source.init(allocator, "test.zig", code);
        defer source.deinit();
        var cfg = (try cfgOf(allocator, &source)) orelse return error.TestUnexpectedResult;
        defer cfg.deinit();
        const tree = try source.ast();
        const fn_body = firstFnBody(tree) orelse return error.TestUnexpectedResult;
        const call_ast = nthCall(tree, fn_body, 0) orelse return error.TestUnexpectedResult;
        try testing.expect(nodeFor(&cfg, call_ast, .call) == null);
        for (cfg.nodes.items) |node| {
            if (node.ir_node.tag != .ret) continue;
            try testing.expectEqual(@as(usize, 1), outgoingEdges(&cfg, node.index));
            try testing.expectEqual(cfg.exit, onlyEdge(&cfg, node.index).?.to);
        }
    }
}
