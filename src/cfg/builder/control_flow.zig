const source_range = @import("source_range.zig");
const graph = @import("../graph.zig");
const ids = @import("../../ids.zig");
const Source = @import("../../source.zig").Source;

const Cfg = graph.Cfg;
const IrNode = graph.IrNode;
const CfgNodeId = ids.CfgNodeId;

pub fn Mixin(comptime _Builder: type) type {
    return struct {
        pub fn processIf(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();

            const range = try source_range.getSourceRange(source, ast_node);

            const full_if = tree.fullIf(@enumFromInt(ast_node)) orelse return .{ .last = null, .terminates = false };

            var branch_ir_node = IrNode.initFull(.branch, ast_node, range);
            branch_ir_node.operand_node = @intFromEnum(full_if.ast.cond_expr);
            const branch_node = try cfg.addNode(branch_ir_node);
            try cfg.addEdge(prev_node, branch_node);

            const then_body: u32 = @intFromEnum(full_if.ast.then_expr);
            const else_body: ?u32 = if (full_if.ast.else_expr.unwrap()) |e| @intFromEnum(e) else null;

            const merge_node = try cfg.addNode(IrNode.init(.nop));

            var then_terminates = false;
            if (then_body != 0) {
                const edge_count_before = cfg.edges.items.len;
                const then_result = try self.processNode(cfg, source, then_body, branch_node);
                markEdgeFromBranchTrue(self, cfg, edge_count_before, branch_node);

                if (then_result.last) |then_end| {
                    if (then_result.terminates) {
                        then_terminates = true;
                    } else {
                        try cfg.addEdge(then_end, merge_node);
                    }
                } else {
                    try cfg.addEdgeWithKind(branch_node, merge_node, .branch_true);
                }
            } else {
                try cfg.addEdgeWithKind(branch_node, merge_node, .branch_true);
            }

            var else_terminates = false;
            if (else_body) |else_node| {
                if (else_node != 0) {
                    const edge_count_before = cfg.edges.items.len;
                    const else_result = try self.processNode(cfg, source, else_node, branch_node);
                    markEdgeFromBranchFalse(self, cfg, edge_count_before, branch_node);

                    if (else_result.last) |else_end| {
                        if (else_result.terminates) {
                            else_terminates = true;
                        } else {
                            try cfg.addEdge(else_end, merge_node);
                        }
                    } else {
                        try cfg.addEdgeWithKind(branch_node, merge_node, .branch_false);
                    }
                } else {
                    try cfg.addEdgeWithKind(branch_node, merge_node, .branch_false);
                }
            } else {
                try cfg.addEdgeWithKind(branch_node, merge_node, .branch_false);
            }

            if (then_terminates and else_terminates) {
                return .{ .last = branch_node, .terminates = true };
            }

            return .{ .last = merge_node, .terminates = false };
        }

        fn markEdgeFromBranchTrue(self: *_Builder, cfg: *Cfg, edge_start_idx: usize, branch_node: CfgNodeId) void {
            _ = self;
            for (cfg.edges.items[edge_start_idx..]) |*edge| {
                if (edge.from == branch_node and edge.kind == .normal) {
                    edge.kind = .branch_true;
                    break;
                }
            }
        }

        fn markEdgeFromBranchFalse(self: *_Builder, cfg: *Cfg, edge_start_idx: usize, branch_node: CfgNodeId) void {
            _ = self;
            for (cfg.edges.items[edge_start_idx..]) |*edge| {
                if (edge.from == branch_node and edge.kind == .normal) {
                    edge.kind = .branch_false;
                    break;
                }
            }
        }

        pub fn processWhile(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const range = try source_range.getSourceRange(source, ast_node);

            const header_node = try cfg.addNode(IrNode.initFull(.loop_header, ast_node, range));
            try cfg.addEdge(prev_node, header_node);

            const full_while = tree.fullWhile(@enumFromInt(ast_node)) orelse return .{ .last = null, .terminates = false };

            // Handle else expression if present - this executes when loop condition is false
            const else_ast = if (full_while.ast.else_expr.unwrap()) |e| @intFromEnum(e) else 0;

            var exit_node: CfgNodeId = undefined;
            if (else_ast != 0) {
                // Process else body - loop_exit goes to else body, then else body goes to merge
                const else_range = try source_range.getSourceRange(source, else_ast);
                const else_entry_node = try cfg.addNode(IrNode.initFull(.block, else_ast, else_range));
                try cfg.addEdgeWithKind(header_node, else_entry_node, .loop_exit);

                const else_result = try self.processNode(cfg, source, else_ast, else_entry_node);

                // `exit_node` is where control goes once the loop is over, so
                // it is also where a `break` from the body lands: the else
                // branch belongs to running the condition out, and a break
                // skips it. The else body's entry is therefore never the exit
                // itself - not even here, where the else body ends every path
                // it has - because that would send a break through the branch
                // it just skipped.
                exit_node = try cfg.addNode(IrNode.init(.nop));
                if (!else_result.terminates) {
                    try cfg.addEdge(else_result.last orelse else_entry_node, exit_node);
                }
            } else {
                exit_node = try cfg.addNode(IrNode.init(.nop));
                try cfg.addEdgeWithKind(header_node, exit_node, .loop_exit);
            }

            // The continuation expression runs after the body and before the
            // loop back, and a `continue` has to run it too: a continue that
            // jumped straight to the header would repeat the body it just
            // left. Its node therefore exists before the body is walked, so a
            // continue inside that body can link to it directly, and the back
            // edge to the header leaves it (see below) rather than the body.
            const cont_ast = if (full_while.ast.cont_expr.unwrap()) |c| @intFromEnum(c) else 0;
            var cont_node: ?CfgNodeId = null;
            if (cont_ast != 0) {
                const cont_range = try source_range.getSourceRange(source, cont_ast);
                cont_node = try cfg.addNode(IrNode.initFull(.expr, cont_ast, cont_range));
            }

            const body_ast = @intFromEnum(full_while.ast.then_expr);
            if (body_ast != 0) {
                const body_range = try source_range.getSourceRange(source, body_ast);
                const body_node = try cfg.addNode(IrNode.initFull(.loop_body, body_ast, body_range));
                try cfg.addEdgeWithKind(header_node, body_node, .branch_true);

                // The loop's own context covers the body walk only. Its else
                // branch is walked above, outside the frame, so a continue
                // there resolves against an enclosing loop like any code that
                // sits after this one.
                const frame: _Builder.LoopFrame = .{
                    .parent = self.current_loop,
                    .ast_node = ast_node,
                    .label_token = _Builder.Statements.labelTokenBefore(tree, ast_node),
                    .enclosing_scope = self.current_scope,
                    .continue_target = cont_node orelse header_node,
                    .break_target = exit_node,
                };
                self.current_loop = &frame;
                defer self.current_loop = frame.parent;

                const body_result = try self.processNode(cfg, source, body_ast, body_node);

                var loop_back_from: CfgNodeId = body_node;
                if (body_result.last) |body_end| {
                    if (!body_result.terminates) {
                        loop_back_from = body_end;
                    }
                }

                // `continue` terminates the body but still runs the continuation.
                // Its back edge must not depend on body fallthrough.
                if (cont_node) |cont| {
                    if (!body_result.terminates) {
                        try cfg.addEdge(loop_back_from, cont);
                    }
                    try cfg.addEdgeWithKind(cont, header_node, .loop_back);
                } else if (!body_result.terminates) {
                    try cfg.addEdgeWithKind(loop_back_from, header_node, .loop_back);
                }
            } else {
                try cfg.addEdgeWithKind(header_node, header_node, .loop_back);
            }

            for (cfg.edges.items) |edge| {
                if (edge.to == exit_node) return .{ .last = exit_node, .terminates = false };
            }
            return .{ .last = exit_node, .terminates = true };
        }

        pub fn processFor(
            self: *_Builder,
            cfg: *Cfg,
            source: *Source,
            ast_node: u32,
            prev_node: CfgNodeId,
        ) !_Builder.ProcessResult {
            const tree = try source.ast();
            const range = try source_range.getSourceRange(source, ast_node);

            const header_node = try cfg.addNode(IrNode.initFull(.loop_header, ast_node, range));
            try cfg.addEdge(prev_node, header_node);

            const full_for = tree.fullFor(@enumFromInt(ast_node)) orelse return .{ .last = null, .terminates = false };

            // Handle else expression if present - this executes when loop completes normally (not via break)
            const else_ast = if (full_for.ast.else_expr.unwrap()) |e| @intFromEnum(e) else 0;

            var exit_node: CfgNodeId = undefined;
            if (else_ast != 0) {
                // Process else body - loop_exit goes to else body, then else body goes to merge
                const else_range = try source_range.getSourceRange(source, else_ast);
                const else_entry_node = try cfg.addNode(IrNode.initFull(.block, else_ast, else_range));
                try cfg.addEdgeWithKind(header_node, else_entry_node, .loop_exit);

                const else_result = try self.processNode(cfg, source, else_ast, else_entry_node);

                // `exit_node` is where control goes once the loop is over, so
                // it is also where a `break` from the body lands: the else
                // branch belongs to running the loop out, and a break skips
                // it. The else body's entry is therefore never the exit
                // itself - not even here, where the else body ends every path
                // it has - because that would send a break through the branch
                // it just skipped.
                exit_node = try cfg.addNode(IrNode.init(.nop));
                if (!else_result.terminates) {
                    try cfg.addEdge(else_result.last orelse else_entry_node, exit_node);
                }
            } else {
                exit_node = try cfg.addNode(IrNode.init(.nop));
                try cfg.addEdgeWithKind(header_node, exit_node, .loop_exit);
            }

            const body_ast = @intFromEnum(full_for.ast.then_expr);
            if (body_ast != 0) {
                const body_range = try source_range.getSourceRange(source, body_ast);
                const body_node = try cfg.addNode(IrNode.initFull(.loop_body, body_ast, body_range));
                try cfg.addEdgeWithKind(header_node, body_node, .branch_true);

                // A for loop has no continuation expression: its header steps
                // to the next item, so that is where a continue lands. The
                // frame covers the body walk only, so a continue in the else
                // branch walked above resolves against an enclosing loop.
                const frame: _Builder.LoopFrame = .{
                    .parent = self.current_loop,
                    .ast_node = ast_node,
                    .label_token = _Builder.Statements.labelTokenBefore(tree, ast_node),
                    .enclosing_scope = self.current_scope,
                    .continue_target = header_node,
                    .break_target = exit_node,
                };
                self.current_loop = &frame;
                defer self.current_loop = frame.parent;

                const body_result = try self.processNode(cfg, source, body_ast, body_node);

                if (body_result.last) |body_end| {
                    if (!body_result.terminates) {
                        try cfg.addEdgeWithKind(body_end, header_node, .loop_back);
                    }
                } else {
                    try cfg.addEdgeWithKind(body_node, header_node, .loop_back);
                }
            } else {
                try cfg.addEdgeWithKind(header_node, header_node, .loop_back);
            }

            for (cfg.edges.items) |edge| {
                if (edge.to == exit_node) return .{ .last = exit_node, .terminates = false };
            }
            return .{ .last = exit_node, .terminates = true };
        }
    };
}
