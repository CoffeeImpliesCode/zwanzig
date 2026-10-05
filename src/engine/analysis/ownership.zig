const std = @import("std");
const ids = @import("../../ids.zig");
const ast_walk = @import("../../ast_walk.zig");
const allocator_utils = @import("../../analysis/allocator_utils.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
const LexicalIndex = @import("../../analysis/lexical_index.zig").LexicalIndex;
const Source = @import("../../source.zig").Source;
const Cfg = @import("../../cfg.zig").Cfg;
const ProgramState = @import("../state.zig").ProgramState;
const EngineError = @import("../base.zig").EngineError;

pub fn Mixin(comptime _Engine: type) type {
    return struct {
        pub fn resolveCallToken(self: *_Engine, call_node: u32) ?u32 {
            const src = self.source orelse return null;
            const tree = src.ast() catch return null;
            const main_tokens = tree.nodes.items(.main_token);
            if (call_node >= main_tokens.len) return null;
            return main_tokens[call_node];
        }

        pub fn checkUseAfterFreeInCall(self: *_Engine, state: *ProgramState, call_node: u32, current_cfg: *const Cfg) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);

            if (call_node >= tags.len) return;

            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const full_call = switch (tags[call_node]) {
                .call, .call_comma, .call_one, .call_one_comma => tree.fullCall(&call_buf, @enumFromInt(call_node)),
                else => null,
            } orelse return;

            try checkUseAfterFreeInExpr(self, state, @intFromEnum(full_call.ast.fn_expr), current_cfg);

            for (full_call.ast.params) |param| {
                try checkUseAfterFreeInExpr(self, state, @intFromEnum(param), current_cfg);
            }
        }

        pub fn checkUseAfterFreeInExpr(self: *_Engine, state: *ProgramState, expr_node: u32, current_cfg: *const Cfg) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const main_tokens = tree.nodes.items(.main_token);

            if (expr_node >= tags.len) return;

            switch (tags[expr_node]) {
                .identifier => {
                    if (_Engine.VarResolution.resolveVarIdFromIdentifier(self, expr_node, current_cfg)) |var_id| {
                        const token = main_tokens[expr_node];
                        try state.trackUse(var_id, token);
                    }
                },
                .grouped_expression, .unwrap_optional => {
                    const data = datas[expr_node].node_and_token;
                    try checkUseAfterFreeInExpr(self, state, @intFromEnum(data[0]), current_cfg);
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr_node)) orelse return;
                    try checkUseAfterFreeInExpr(self, state, @intFromEnum(slice.ast.sliced), current_cfg);
                },
                .array_access => {
                    const pair = datas[expr_node].node_and_node;
                    try checkUseAfterFreeInExpr(self, state, @intFromEnum(pair[0]), current_cfg);
                },
                .field_access => {
                    const data = datas[expr_node].node_and_token;
                    try checkUseAfterFreeInExpr(self, state, @intFromEnum(data[0]), current_cfg);
                },
                .address_of, .deref, .@"try" => {
                    const child = datas[expr_node].node;
                    try checkUseAfterFreeInExpr(self, state, @intFromEnum(child), current_cfg);
                },
                .@"catch" => {
                    const pair = datas[expr_node].node_and_node;
                    try checkUseAfterFreeInExpr(self, state, @intFromEnum(pair[0]), current_cfg);
                    try checkUseAfterFreeInExpr(self, state, @intFromEnum(pair[1]), current_cfg);
                },
                .call, .call_comma, .call_one, .call_one_comma => {
                    try checkUseAfterFreeInCall(self, state, expr_node, current_cfg);
                },
                .container_field, .container_field_init, .container_field_align => {
                    const full_field = tree.fullContainerField(@enumFromInt(expr_node)) orelse return;
                    if (full_field.ast.value_expr.unwrap()) |value_expr| {
                        try checkUseAfterFreeInExpr(self, state, @intFromEnum(value_expr), current_cfg);
                    }
                },
                .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const struct_init = tree.fullStructInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (struct_init.ast.fields) |field| {
                        try checkUseAfterFreeInExpr(self, state, @intFromEnum(field), current_cfg);
                    }
                },
                else => {},
            }
            // A store reads both of the operands its node names: the
            // destination it writes into, and the value it writes. The node
            // itself is neither, so a walk that stopped here would read
            // neither - and the store the builder lowered as a plain
            // expression, a `while` step written anywhere at all, arrives at
            // this walk as nothing but the store it is.
            if (call_resolver.isAssignTag(tags[expr_node])) {
                const operands = datas[expr_node].node_and_node;
                try checkUseAfterFreeInExpr(self, state, @intFromEnum(operands[0]), current_cfg);
                try checkUseAfterFreeInExpr(self, state, @intFromEnum(operands[1]), current_cfg);
            }
            if (pointerCastOperand(tree, expr_node)) |value| {
                try checkUseAfterFreeInExpr(self, state, value, current_cfg);
            }
        }

        /// Follow the ownership of an expression out of the function.
        ///
        /// A pointer-preserving cast hands back the very allocation its
        /// argument names, so `@ptrCast(bytes.ptr)` returns `bytes` to the
        /// caller exactly as returning `bytes` would. A cast that changes
        /// representation, such as `@intFromPtr`, names no owner and is left
        /// alone.
        pub fn markEscapedInExpr(self: *_Engine, state: *ProgramState, expr_node: u32, current_cfg: *const Cfg) EngineError!void {
            return markEscapedInExprWith(self, state, expr_node, current_cfg, .discard, 0);
        }

        /// What an escape leaves behind of a release the block already has.
        const ReleaseHistory = enum {
            /// The escape drops the record, as every escape has.
            discard,
            /// The escape drops the record too, except for a block that is
            /// already released: that stays released, so handing it to the
            /// caller does not silence the read or the second release that
            /// follows.
            keep,
        };

        /// True when `region` is already released, so escaping it must not
        /// erase that release.
        fn regionAlreadyReleased(state: *const ProgramState, region: ids.VarId) bool {
            const region_state = state.getRegionState(region) orelse return false;
            return region_state == .freed;
        }

        /// How far the escape walk follows an expression before it stops. Every
        /// step is an edge the expression itself draws, so the bound only stops
        /// a shape that folds back onto itself.
        const max_escape_depth = 16;

        fn markEscapedInExprWith(
            self: *_Engine,
            state: *ProgramState,
            expr_node: u32,
            current_cfg: *const Cfg,
            history: ReleaseHistory,
            depth: u8,
        ) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const main_tokens = tree.nodes.items(.main_token);
            const token_tags = tree.tokens.items(.tag);

            if (expr_node >= tags.len or depth >= max_escape_depth) return;

            switch (tags[expr_node]) {
                .identifier => {
                    if (_Engine.VarResolution.resolveVarIdFromIdentifier(self, expr_node, current_cfg)) |var_id| {
                        // Escaping drops the record that says whether the
                        // block is still held, and with it the release the
                        // block already carries. Returning a freed pointer is
                        // still handing out a freed pointer, so the release is
                        // put back once the escape has done its work.
                        const keep_release = history == .keep and regionAlreadyReleased(state, var_id);
                        try state.trackEscapeOwned(var_id);
                        state.trackEscape(var_id);
                        const token = main_tokens[expr_node];
                        if (ids.varIndex(var_id) == token and token < token_tags.len and token_tags[token] == .identifier) {
                            const name = tree.tokenSlice(token);
                            try state.trackEscapeByName(tree, name);
                        }
                        if (keep_release) try state.trackFree(var_id, null);
                    }
                    // A binding a pointer-preserving cast initialized names the
                    // very block that cast names: the cast hands back the
                    // allocation it was given, so the copy is not a second
                    // claim on it but the same one written under another name.
                    // The escape therefore continues past the copy, into the
                    // block behind it.
                    if (castBoundOperand(self, tree, expr_node, current_cfg)) |value| {
                        try markEscapedInExprWith(self, state, value, current_cfg, history, depth + 1);
                    }
                },
                .grouped_expression, .unwrap_optional => {
                    const data = datas[expr_node].node_and_token;
                    try markEscapedInExprWith(self, state, @intFromEnum(data[0]), current_cfg, history, depth + 1);
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr_node)) orelse return;
                    try markEscapedInExprWith(self, state, @intFromEnum(slice.ast.sliced), current_cfg, history, depth + 1);
                },
                .array_access => {
                    const pair = datas[expr_node].node_and_node;
                    try markEscapedInExprWith(self, state, @intFromEnum(pair[0]), current_cfg, history, depth + 1);
                },
                .field_access => {
                    const data = datas[expr_node].node_and_token;
                    try markEscapedInExprWith(self, state, @intFromEnum(data[0]), current_cfg, history, depth + 1);
                },
                .address_of, .deref, .@"try" => {
                    const child = datas[expr_node].node;
                    try markEscapedInExprWith(self, state, @intFromEnum(child), current_cfg, history, depth + 1);
                },
                .@"catch" => {
                    const pair = datas[expr_node].node_and_node;
                    try markEscapedInExprWith(self, state, @intFromEnum(pair[0]), current_cfg, history, depth + 1);
                    try markEscapedInExprWith(self, state, @intFromEnum(pair[1]), current_cfg, history, depth + 1);
                },
                .@"if", .if_simple => {
                    // A selection is a transfer only when every arm carries the
                    // block: an arm that cannot carry it drops it, and the
                    // escape walk has to keep naming it as this frame's to
                    // release.
                    const full_if = tree.fullIf(@enumFromInt(expr_node)) orelse return;
                    const else_node = full_if.ast.else_expr.unwrap() orelse return;
                    if (!expressionCarriesRegion(self, state, tree, @intFromEnum(full_if.ast.then_expr), current_cfg, depth)) return;
                    if (!expressionCarriesRegion(self, state, tree, @intFromEnum(else_node), current_cfg, depth)) return;
                    try markEscapedInExprWith(self, state, @intFromEnum(full_if.ast.then_expr), current_cfg, history, depth + 1);
                    try markEscapedInExprWith(self, state, @intFromEnum(else_node), current_cfg, history, depth + 1);
                },
                .@"switch", .switch_comma => {
                    const full_switch = tree.switchFull(@enumFromInt(expr_node));
                    for (full_switch.ast.cases) |case_node| {
                        const full_case = tree.fullSwitchCase(case_node) orelse return;
                        if (!expressionCarriesRegion(self, state, tree, @intFromEnum(full_case.ast.target_expr), current_cfg, depth)) return;
                    }
                    for (full_switch.ast.cases) |case_node| {
                        const full_case = tree.fullSwitchCase(case_node) orelse return;
                        try markEscapedInExprWith(self, state, @intFromEnum(full_case.ast.target_expr), current_cfg, history, depth + 1);
                    }
                },
                .@"orelse" => {
                    // `value orelse fallback` hands the caller whatever it
                    // holds, and the fallback stands only for the case where it
                    // holds nothing, so the block the value names leaves with
                    // the value whichever of the two the caller receives.
                    const value = @intFromEnum(datas[expr_node].node_and_node[0]);
                    if (!expressionCarriesRegion(self, state, tree, value, current_cfg, depth)) return;
                    try markEscapedInExprWith(self, state, value, current_cfg, history, depth + 1);
                },
                .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const struct_init = tree.fullStructInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (struct_init.ast.fields) |field| {
                        try markEscapedInExprWith(self, state, @intFromEnum(field), current_cfg, history, depth + 1);
                    }
                },
                .container_field, .container_field_init, .container_field_align => {
                    const field = tree.fullContainerField(@enumFromInt(expr_node)) orelse return;
                    if (field.ast.value_expr.unwrap()) |value_expr| {
                        try markEscapedInExprWith(self, state, @intFromEnum(value_expr), current_cfg, history, depth + 1);
                    } else if (field.ast.tuple_like) {
                        if (field.ast.type_expr.unwrap()) |value_expr| {
                            try markEscapedInExprWith(self, state, @intFromEnum(value_expr), current_cfg, history, depth + 1);
                        }
                    }
                },
                .array_init, .array_init_comma, .array_init_one, .array_init_one_comma, .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const array_init = tree.fullArrayInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (array_init.ast.elements) |elem| {
                        try markEscapedInExprWith(self, state, @intFromEnum(elem), current_cfg, history, depth + 1);
                    }
                },
                else => {},
            }
            if (pointerCastOperand(tree, expr_node)) |value| {
                try markEscapedInExprWith(self, state, value, current_cfg, history, depth + 1);
            }
        }

        /// Whether `expr` can hand on a block this frame holds, which is what
        /// decides a selection over it. An arm that cannot carry the block
        /// drops it, so a selection whose arms all carry one is a transfer and
        /// a selection with an arm that cannot is not.
        fn expressionCarriesRegion(
            self: *_Engine,
            state: *const ProgramState,
            tree: *const std.zig.Ast,
            expr: u32,
            current_cfg: *const Cfg,
            depth: u8,
        ) bool {
            if (expr == 0 or expr >= tree.nodes.items(.tag).len or depth >= max_escape_depth) return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            switch (tags[expr]) {
                .identifier => {
                    const var_id = _Engine.VarResolution.resolveVarIdFromIdentifier(self, expr, current_cfg) orelse return false;
                    if (state.getRegionState(var_id) != null) return true;
                    const value = castBoundOperand(self, tree, expr, current_cfg) orelse return false;
                    return expressionCarriesRegion(self, state, tree, value, current_cfg, depth + 1);
                },
                .grouped_expression, .unwrap_optional => {
                    return expressionCarriesRegion(self, state, tree, @intFromEnum(datas[expr].node_and_token[0]), current_cfg, depth + 1);
                },
                .address_of, .deref, .@"try" => {
                    return expressionCarriesRegion(self, state, tree, @intFromEnum(datas[expr].node), current_cfg, depth + 1);
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr)) orelse return false;
                    return expressionCarriesRegion(self, state, tree, @intFromEnum(slice.ast.sliced), current_cfg, depth + 1);
                },
                .array_access => {
                    return expressionCarriesRegion(self, state, tree, @intFromEnum(datas[expr].node_and_node[0]), current_cfg, depth + 1);
                },
                .field_access => {
                    return expressionCarriesRegion(self, state, tree, @intFromEnum(datas[expr].node_and_token[0]), current_cfg, depth + 1);
                },
                .@"orelse" => {
                    return expressionCarriesRegion(self, state, tree, @intFromEnum(datas[expr].node_and_node[0]), current_cfg, depth + 1);
                },
                .@"catch" => {
                    const pair = datas[expr].node_and_node;
                    return expressionCarriesRegion(self, state, tree, @intFromEnum(pair[0]), current_cfg, depth + 1) and
                        expressionCarriesRegion(self, state, tree, @intFromEnum(pair[1]), current_cfg, depth + 1);
                },
                .@"if", .if_simple => {
                    const full_if = tree.fullIf(@enumFromInt(expr)) orelse return false;
                    const else_node = full_if.ast.else_expr.unwrap() orelse return false;
                    return expressionCarriesRegion(self, state, tree, @intFromEnum(full_if.ast.then_expr), current_cfg, depth + 1) and
                        expressionCarriesRegion(self, state, tree, @intFromEnum(else_node), current_cfg, depth + 1);
                },
                .@"switch", .switch_comma => {
                    const full_switch = tree.switchFull(@enumFromInt(expr));
                    for (full_switch.ast.cases) |case_node| {
                        const full_case = tree.fullSwitchCase(case_node) orelse return false;
                        if (!expressionCarriesRegion(self, state, tree, @intFromEnum(full_case.ast.target_expr), current_cfg, depth + 1)) return false;
                    }
                    return true;
                },
                else => {
                    const value = pointerCastOperand(tree, expr) orelse return false;
                    return expressionCarriesRegion(self, state, tree, value, current_cfg, depth + 1);
                },
            }
        }

        /// The value a binding's own declaration handed it through a
        /// pointer-preserving cast, or null when it was handed something else.
        ///
        /// A cast returns the very allocation its argument names, so a binding
        /// a cast initialized is another name for that allocation rather than a
        /// second claim on it. Anything else a declaration wrote - a call, a
        /// plain copy, no initializer at all - proves nothing and answers null.
        fn castBoundOperand(self: *_Engine, tree: *const std.zig.Ast, identifier: u32, current_cfg: *const Cfg) ?u32 {
            const decl = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, identifier, current_cfg) orelse return null;
            const full = tree.fullVarDecl(@enumFromInt(decl.decl_node)) orelse return null;
            const init: u32 = @intFromEnum(full.ast.init_node.unwrap() orelse return null);
            return pointerCastOperand(tree, init);
        }

        /// Value operand of a builtin that hands back the very pointer it was
        /// given, so the block keeps its ordinary ownership origin across the
        /// cast.
        ///
        /// `@as` names its type first and its value second; the other casts in
        /// the set take exactly one value. Builtins that re-derive a pointer
        /// from an integer, such as `@intFromPtr`, own nothing the caller has
        /// to release and are deliberately absent. Only a real builtin token
        /// qualifies, so a function a program happens to call `ptrCast` proves
        /// nothing.
        pub fn pointerCastOperand(tree: *const std.zig.Ast, expr_node: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (expr_node >= tags.len) return null;
            switch (tags[expr_node]) {
                .builtin_call_two, .builtin_call_two_comma, .builtin_call, .builtin_call_comma => {},
                else => return null,
            }
            const token = tree.nodes.items(.main_token)[expr_node];
            if (token >= tree.tokens.len) return null;
            if (tree.tokenTag(token) != .builtin) return null;
            const name = builtinName(tree.tokenSlice(token));

            var buffer: [2]std.zig.Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&buffer, @enumFromInt(expr_node)) orelse return null;
            const value: ?std.zig.Ast.Node.Index = if (std.mem.eql(u8, name, "as")) blk: {
                if (params.len != 2) break :blk null;
                break :blk params[1];
            } else blk: {
                if (!isPointerPreservingCast(name)) break :blk null;
                if (params.len != 1) break :blk null;
                break :blk params[0];
            };
            const operand = value orelse return null;
            return @intFromEnum(operand);
        }

        /// Name of a builtin token without its `@` sigil. `@"ptrCast"` is an
        /// identifier a program may declare, so it is not a builtin name.
        fn builtinName(slice: []const u8) []const u8 {
            if (slice.len < 2 or slice[0] != '@') return "";
            return import_resolver.normalizeIdentifier(slice[1..]);
        }

        /// The casts that hand back the pointer they were given. Every one of
        /// them keeps the address and only changes how it is typed, so the
        /// operand still names the block it came from.
        fn isPointerPreservingCast(name: []const u8) bool {
            const casts = [_][]const u8{ "ptrCast", "alignCast", "constCast", "volatileCast" };
            for (casts) |cast| {
                if (std.mem.eql(u8, name, cast)) return true;
            }
            return false;
        }

        /// A `return` whose declared type cannot hold a reference hands no
        /// ownership to the caller. `return bytes.len` names the allocation but
        /// returns an integer, so the block is still this function's to
        /// release.
        pub fn markEscapedAtReturn(self: *_Engine, state: *ProgramState, expr_node: u32, current_cfg: *const Cfg) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            if (current_cfg.fn_ast_node) |fn_node| {
                if (returnTypeCarriesNoReference(tree, ids.astIndex(fn_node))) return;
            }
            try markEscapedInExprWith(self, state, expr_node, current_cfg, .keep, 0);
        }

        /// True when the declared return type is a Zig primitive, an optional
        /// of one, or an error union wrapping either, so the returned value
        /// cannot carry a reference to the block. A type this cannot resolve
        /// proves nothing and keeps the current, escaping, treatment.
        pub fn returnTypeCarriesNoReference(tree: *const std.zig.Ast, fn_node: u32) bool {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const proto = tree.fullFnProto(&buffer, @enumFromInt(fn_node)) orelse return false;
            const return_type = proto.ast.return_type.unwrap() orelse return false;
            return typeNodeCarriesNoReference(tree, @intFromEnum(return_type));
        }

        /// True when a written type cannot hold a reference: a primitive, an
        /// optional of one, or an error union wrapping either. A type this
        /// cannot resolve proves nothing and carries one, so an unresolved
        /// type never silences a leak.
        fn typeNodeCarriesNoReference(tree: *const std.zig.Ast, written: u32) bool {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const max_index: u32 = @intCast(tags.len);
            var node: u32 = written;

            var depth: u8 = 0;
            while (depth < 16) : (depth += 1) {
                if (node == 0 or node >= max_index) return false;
                switch (tags[node]) {
                    .error_union => node = @intFromEnum(datas[node].node_and_node[1]),
                    .optional_type => node = @intFromEnum(datas[node].node),
                    .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
                    else => break,
                }
            }
            if (node == 0 or node >= max_index) return false;
            // Only a primitive spelled as a plain name. `?*anyopaque` unwraps
            // to the pointer type and stops there, so a nullable opaque
            // pointer keeps the escaping treatment a returned reference needs.
            if (tags[node] != .identifier) return false;
            const token = tree.nodes.items(.main_token)[node];
            if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return false;
            const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));
            for (scalar_return_types) |scalar| {
                if (std.mem.eql(u8, name, scalar)) return true;
            }
            return false;
        }

        /// The primitive types that cannot carry a reference. A name missing
        /// here - an alias, a container, anything this list does not spell -
        /// is treated as carrying one, so an unresolved type never silences a
        /// leak.
        const scalar_return_types = [_][]const u8{
            "void",         "noreturn", "bool",    "comptime_int", "comptime_float",
            "isize",        "usize",    "i8",      "i16",          "i32",
            "i64",          "i128",     "u8",      "u16",          "u32",
            "u64",          "u128",     "f16",     "f32",          "f64",
            "f80",          "f128",     "type",    "anyerror",     "anyopaque",
            "anyframe",     "c_char",   "c_short", "c_ushort",     "c_int",
            "c_uint",       "c_long",   "c_ulong", "c_longlong",   "c_ulonglong",
            "c_longdouble",
        };

        /// Record the blocks a call hands to something that outlives them.
        ///
        /// An allocation that runs out halfway through this must abort the
        /// analysis rather than leave the frame holding an escape it never
        /// recorded: a partially applied escape is a state no source produces,
        /// and every question asked of the run afterwards would be answered
        /// from it.
        pub fn trackEscapesFromCall(self: *_Engine, state: *ProgramState, call_node: u32, current_cfg: *const Cfg) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const main_tokens = tree.nodes.items(.main_token);
            const token_tags = tree.tokens.items(.tag);

            if (call_node >= tags.len) return;

            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const full_call = switch (tags[call_node]) {
                .call, .call_comma, .call_one, .call_one_comma => tree.fullCall(&call_buf, @enumFromInt(call_node)),
                else => null,
            } orelse return;

            const callee_node: u32 = @intFromEnum(full_call.ast.fn_expr);
            if (callee_node >= tags.len) return;

            const fn_name = blk: {
                switch (tags[callee_node]) {
                    .field_access => {
                        const field_access_data = datas[callee_node].node_and_token;
                        const field_token = field_access_data[1];
                        if (field_token >= token_tags.len or token_tags[field_token] != .identifier) break :blk null;
                        break :blk tree.tokenSlice(field_token);
                    },
                    .identifier => {
                        const fn_token = main_tokens[callee_node];
                        if (fn_token >= token_tags.len or token_tags[fn_token] != .identifier) break :blk null;
                        break :blk tree.tokenSlice(fn_token);
                    },
                    else => break :blk null,
                }
            } orelse return;

            if (std.mem.eql(u8, fn_name, "append") or
                std.mem.eql(u8, fn_name, "appendAssumeCapacity") or
                std.mem.eql(u8, fn_name, "appendSlice") or
                std.mem.eql(u8, fn_name, "appendSliceAssumeCapacity") or
                std.mem.eql(u8, fn_name, "insert") or
                std.mem.eql(u8, fn_name, "insertSlice") or
                std.mem.eql(u8, fn_name, "insertAssumeCapacity"))
            {
                if (full_call.ast.params.len == 0) return;
                const item_node = @intFromEnum(full_call.ast.params[full_call.ast.params.len - 1]);
                // Receiver is the base of the `<receiver>.append(...)` field access.
                // Must run before markEscapedInExpr because the latter clears the
                // deferred-free tracking we rely on here.
                if (tags[callee_node] == .field_access) {
                    const receiver_node = @intFromEnum(datas[callee_node].node_and_token[0]);
                    // *Slice methods (appendSlice / appendSliceAssumeCapacity /
                    // insertSlice) iterate the argument and copy each element. A
                    // direct slice arg (`appendSlice(out, tmp)` or `tmp[start..end]`)
                    // is consumed in the call; freeing `tmp` afterwards is safe.
                    // Nested references (`appendSlice(out, &.{tmp})` etc.) retain
                    // a reference, so they still go through the escape check.
                    const is_slice_store = std.mem.eql(u8, fn_name, "appendSlice") or
                        std.mem.eql(u8, fn_name, "appendSliceAssumeCapacity") or
                        std.mem.eql(u8, fn_name, "insertSlice");
                    const skip_escape_check = is_slice_store and isDirectSliceCopyArgument(tree, tags, datas, item_node);
                    if (!skip_escape_check) {
                        try checkDeferFreesEscapeeIntoContainer(self, state, call_node, receiver_node, item_node, current_cfg);
                    }
                }
                try markEscapedInExpr(self, state, item_node, current_cfg);
                return;
            }

            if (std.mem.eql(u8, fn_name, "put") or
                std.mem.eql(u8, fn_name, "putNoClobber") or
                std.mem.eql(u8, fn_name, "putAssumeCapacity") or
                std.mem.eql(u8, fn_name, "putNoClobberAssumeCapacity"))
            {
                if (full_call.ast.params.len >= 1) {
                    const key_node = @intFromEnum(full_call.ast.params[0]);
                    try markEscapedInExpr(self, state, key_node, current_cfg);
                }
                if (full_call.ast.params.len >= 2) {
                    const value_node = @intFromEnum(full_call.ast.params[1]);
                    try markEscapedInExpr(self, state, value_node, current_cfg);
                }
                return;
            }

            if (std.mem.startsWith(u8, fn_name, "init") or
                std.mem.startsWith(u8, fn_name, "setup") or
                std.mem.startsWith(u8, fn_name, "set") or
                std.mem.startsWith(u8, fn_name, "store") or
                std.mem.startsWith(u8, fn_name, "register") or
                std.mem.startsWith(u8, fn_name, "add") or
                std.mem.startsWith(u8, fn_name, "push"))
            {
                for (full_call.ast.params) |param| {
                    const param_node = @intFromEnum(param);
                    try markEscapedInExpr(self, state, param_node, current_cfg);
                }
            }
        }

        fn isDirectSliceCopyArgument(
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            expr_node: u32,
        ) bool {
            if (expr_node >= tags.len) return false;

            switch (tags[expr_node]) {
                .identifier => return true,
                .grouped_expression, .unwrap_optional => {
                    const data = datas[expr_node].node_and_token;
                    return isDirectSliceCopyArgument(tree, tags, datas, @intFromEnum(data[0]));
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr_node)) orelse return false;
                    return isDirectSliceCopyArgument(tree, tags, datas, @intFromEnum(slice.ast.sliced));
                },
                else => return false,
            }
        }

        /// Detect the "defer frees an escapee" pattern: a resource with a queued
        /// deferred-free is appended into a container whose declaration outlives
        /// the defer's enclosing block. When the block exits the defer fires and
        /// the container is left holding a dangling slice — a future use-after-free.
        ///
        /// `receiver_node` is the LHS of the `<receiver>.append(...)` field
        /// access; `item_expr_node` is the value being appended.
        pub fn checkDeferFreesEscapeeIntoContainer(
            self: *_Engine,
            state: *ProgramState,
            call_node: u32,
            receiver_node: u32,
            item_expr_node: u32,
            current_cfg: *const Cfg,
        ) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const parent_map = try self.getParentMap(tree);
            const tags = tree.nodes.items(.tag);

            const call_token = _Engine.Ownership.resolveCallToken(self, call_node);

            var seen: std.AutoHashMap(ids.VarId, void) = .init(self.allocator);
            defer seen.deinit();

            try collectEscapeeViolations(
                self,
                state,
                tree,
                tags,
                parent_map,
                receiver_node,
                item_expr_node,
                call_token,
                current_cfg,
                &seen,
            );
        }

        fn collectEscapeeViolations(
            self: *_Engine,
            state: *ProgramState,
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            parent_map: []const u32,
            receiver_node: u32,
            expr_node: u32,
            call_token: ?u32,
            current_cfg: *const Cfg,
            seen: *std.AutoHashMap(ids.VarId, void),
        ) EngineError!void {
            const datas = tree.nodes.items(.data);
            if (expr_node >= tags.len) return;

            switch (tags[expr_node]) {
                .identifier => {
                    const var_id = _Engine.VarResolution.resolveVarIdFromIdentifier(self, expr_node, current_cfg) orelse return;
                    if (seen.contains(var_id)) return;
                    try seen.put(var_id, {});
                    const defer_scope = state.store.pendingDeferredFreeScope(var_id) orelse return;
                    // Same-block locals are safe (defers fire in reverse declaration
                    // order, so the container is destroyed before the resource).
                    // Parameters, top-level decls, and any container declared outside
                    // the defer's scope are not. The bare-slice carve-out for the
                    // appendSlice / insertSlice family already excludes the byte-slice
                    // copy idiom upstream, so the remaining append/insert call shapes
                    // store by reference and a dangling escape is a real UAF.
                    if (containerOutlivesDeferScope(self, tree, tags, parent_map, receiver_node, defer_scope, current_cfg)) {
                        try state.store.recordDeferFreesEscapee(var_id, call_token);
                        state.invalidateCache();
                    }
                },
                .grouped_expression, .unwrap_optional => {
                    const data = datas[expr_node].node_and_token;
                    try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(data[0]), call_token, current_cfg, seen);
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr_node)) orelse return;
                    try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(slice.ast.sliced), call_token, current_cfg, seen);
                },
                .array_access => {
                    const pair = datas[expr_node].node_and_node;
                    try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(pair[0]), call_token, current_cfg, seen);
                },
                .field_access => {
                    const data = datas[expr_node].node_and_token;
                    try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(data[0]), call_token, current_cfg, seen);
                },
                .address_of, .deref, .@"try" => {
                    const child = datas[expr_node].node;
                    try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(child), call_token, current_cfg, seen);
                },
                .@"catch" => {
                    const pair = datas[expr_node].node_and_node;
                    try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(pair[0]), call_token, current_cfg, seen);
                    try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(pair[1]), call_token, current_cfg, seen);
                },
                .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const struct_init = tree.fullStructInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (struct_init.ast.fields) |field| {
                        try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(field), call_token, current_cfg, seen);
                    }
                },
                .container_field, .container_field_init, .container_field_align => {
                    const field = tree.fullContainerField(@enumFromInt(expr_node)) orelse return;
                    if (field.ast.value_expr.unwrap()) |value_expr| {
                        try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(value_expr), call_token, current_cfg, seen);
                    } else if (field.ast.tuple_like) {
                        if (field.ast.type_expr.unwrap()) |value_expr| {
                            try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(value_expr), call_token, current_cfg, seen);
                        }
                    }
                },
                .array_init, .array_init_comma, .array_init_one, .array_init_one_comma, .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const array_init = tree.fullArrayInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (array_init.ast.elements) |elem| {
                        try collectEscapeeViolations(self, state, tree, tags, parent_map, receiver_node, @intFromEnum(elem), call_token, current_cfg, seen);
                    }
                },
                else => {},
            }
        }

        /// The container outlives the defer scope when its declaration is not
        /// inside the block whose exit will fire the defer. Parameters and
        /// top-level decls outlive by construction. If we can't pin the
        /// receiver to an identifier (e.g. `getList().append(...)`), stay
        /// conservative and don't fire.
        fn containerOutlivesDeferScope(
            self: *_Engine,
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            parent_map: []const u32,
            receiver_node: u32,
            defer_scope: u32,
            current_cfg: *const Cfg,
        ) bool {
            const root_ident_node = findRootIdentifierNode(tags, tree.nodes.items(.data), receiver_node) orelse return false;
            const decl_info = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, root_ident_node, current_cfg) orelse return true;
            if (decl_info.is_top_level) return true;
            return !ast_walk.isAncestor(defer_scope, decl_info.decl_node, parent_map);
        }

        fn findRootIdentifierNode(
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            expr_node: u32,
        ) ?u32 {
            var current = expr_node;
            var depth: u32 = 0;
            while (depth < 64) : (depth += 1) {
                if (current >= tags.len) return null;
                switch (tags[current]) {
                    .identifier => return current,
                    .field_access => current = @intFromEnum(datas[current].node_and_token[0]),
                    .grouped_expression, .unwrap_optional => current = @intFromEnum(datas[current].node_and_token[0]),
                    .address_of, .deref, .@"try" => current = @intFromEnum(datas[current].node),
                    else => return null,
                }
            }
            return null;
        }

        /// Record ownership when passing resources to functions that take a pointer as first argument.
        /// This handles patterns like `initCache(cache, entries, ...)` where entries becomes owned by cache.
        pub fn recordOwnershipFromCall(self: *_Engine, state: *ProgramState, call_node: u32, current_cfg: *const Cfg) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const main_tokens = tree.nodes.items(.main_token);
            const token_tags = tree.tokens.items(.tag);

            if (call_node >= tags.len) return;

            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const full_call = switch (tags[call_node]) {
                .call, .call_comma, .call_one, .call_one_comma => tree.fullCall(&call_buf, @enumFromInt(call_node)),
                else => null,
            } orelse return;

            if (full_call.ast.params.len < 2) return;

            const first_arg_node = @intFromEnum(full_call.ast.params[0]);
            const first_arg_var = _Engine.VarResolution.resolveVarIdFromExpr(self, first_arg_node, current_cfg) orelse return;

            const first_arg_is_ptr = blk: {
                if (self.type_context) |type_ctx| {
                    const token = ids.varIndex(first_arg_var);
                    if (token < token_tags.len and token_tags[token] == .identifier) {
                        const name = tree.tokenSlice(token);
                        if (type_ctx.getDeclType(name)) |type_info| {
                            if (type_info.kind == .pointer) break :blk true;
                        }
                    }
                }
                if (first_arg_node < tags.len and tags[first_arg_node] == .address_of) {
                    break :blk true;
                }
                if (state.getRegionState(first_arg_var)) |rs| {
                    if (rs == .allocated) break :blk true;
                }
                break :blk false;
            };

            const callee_is_init_fn = blk: {
                const callee_node: u32 = @intFromEnum(full_call.ast.fn_expr);
                if (callee_node >= tags.len) break :blk false;
                const fn_name_token = switch (tags[callee_node]) {
                    .identifier => main_tokens[callee_node],
                    .field_access => datas[callee_node].node_and_token[1],
                    else => break :blk false,
                };
                if (fn_name_token >= token_tags.len or token_tags[fn_name_token] != .identifier) break :blk false;
                const fn_name = tree.tokenSlice(fn_name_token);
                break :blk std.mem.startsWith(u8, fn_name, "init");
            };

            for (full_call.ast.params[1..]) |param| {
                const param_node = @intFromEnum(param);
                if (_Engine.VarResolution.resolveVarIdFromExpr(self, param_node, current_cfg)) |param_var| {
                    if (state.getRegionState(param_var)) |rs| {
                        if (rs == .allocated or rs == .open) {
                            if (first_arg_is_ptr or callee_is_init_fn) {
                                try state.trackOwnership(param_var, first_arg_var);
                                try state.trackEscapeOwned(param_var);
                                state.trackEscape(param_var);
                            }
                        }
                    }
                }
            }
        }

        /// Walk an expression for the calls it makes, recording the escapes
        /// each of them settles. A call's own allocation failure propagates,
        /// for the reason `trackEscapesFromCall` gives.
        pub fn trackEscapesInExpr(self: *_Engine, state: *ProgramState, expr_node: u32, current_cfg: *const Cfg) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (expr_node >= tags.len) return;

            switch (tags[expr_node]) {
                .call, .call_comma, .call_one, .call_one_comma => {
                    try trackEscapesFromCall(self, state, expr_node, current_cfg);
                },
                .grouped_expression, .unwrap_optional => {
                    const data = datas[expr_node].node_and_token;
                    try trackEscapesInExpr(self, state, @intFromEnum(data[0]), current_cfg);
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr_node)) orelse return;
                    try trackEscapesInExpr(self, state, @intFromEnum(slice.ast.sliced), current_cfg);
                },
                .array_access => {
                    const pair = datas[expr_node].node_and_node;
                    try trackEscapesInExpr(self, state, @intFromEnum(pair[0]), current_cfg);
                },
                .field_access => {
                    const data = datas[expr_node].node_and_token;
                    try trackEscapesInExpr(self, state, @intFromEnum(data[0]), current_cfg);
                },
                .address_of, .deref, .@"try" => {
                    const child = datas[expr_node].node;
                    try trackEscapesInExpr(self, state, @intFromEnum(child), current_cfg);
                },
                .@"catch" => {
                    const pair = datas[expr_node].node_and_node;
                    try trackEscapesInExpr(self, state, @intFromEnum(pair[0]), current_cfg);
                    try trackEscapesInExpr(self, state, @intFromEnum(pair[1]), current_cfg);
                },
                .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const struct_init = tree.fullStructInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (struct_init.ast.fields) |field| {
                        try trackEscapesInExpr(self, state, @intFromEnum(field), current_cfg);
                    }
                },
                .array_init, .array_init_comma, .array_init_one, .array_init_one_comma, .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const array_init = tree.fullArrayInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (array_init.ast.elements) |elem| {
                        try trackEscapesInExpr(self, state, @intFromEnum(elem), current_cfg);
                    }
                },
                else => {},
            }
        }

        pub fn recordOwnershipFromExpr(
            self: *_Engine,
            state: *ProgramState,
            expr_node: u32,
            container_var: ids.VarId,
            current_cfg: *const Cfg,
        ) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (expr_node >= tags.len) return;

            switch (tags[expr_node]) {
                .struct_init,
                .struct_init_comma,
                .struct_init_one,
                .struct_init_one_comma,
                .struct_init_dot,
                .struct_init_dot_comma,
                .struct_init_dot_two,
                .struct_init_dot_two_comma,
                => try recordOwnershipFromStructInit(self, state, expr_node, container_var, current_cfg),
                .grouped_expression, .unwrap_optional => {
                    const data = datas[expr_node].node_and_token;
                    try recordOwnershipFromExpr(self, state, @intFromEnum(data[0]), container_var, current_cfg);
                },
                .@"try" => try recordOwnershipFromExpr(self, state, @intFromEnum(datas[expr_node].node), container_var, current_cfg),
                .@"catch" => {
                    const pair = datas[expr_node].node_and_node;
                    try recordOwnershipFromExpr(self, state, @intFromEnum(pair[0]), container_var, current_cfg);
                    try recordOwnershipFromExpr(self, state, @intFromEnum(pair[1]), container_var, current_cfg);
                },
                else => {},
            }
        }

        pub fn recordOwnershipFromStructInit(
            self: *_Engine,
            state: *ProgramState,
            struct_node: u32,
            container_var: ids.VarId,
            current_cfg: *const Cfg,
        ) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);

            if (struct_node >= tags.len) return;

            var buf: [2]std.zig.Ast.Node.Index = undefined;
            const struct_init = tree.fullStructInit(&buf, @enumFromInt(struct_node)) orelse return;

            for (struct_init.ast.fields) |field| {
                const field_idx = @intFromEnum(field);
                if (field_idx >= tags.len) continue;

                switch (tags[field_idx]) {
                    .container_field, .container_field_init, .container_field_align => {
                        const full_field = tree.fullContainerField(@enumFromInt(field_idx)) orelse continue;
                        if (full_field.ast.value_expr.unwrap()) |value_expr| {
                            if (_Engine.VarResolution.resolveVarIdFromExpr(self, @intFromEnum(value_expr), current_cfg)) |var_id| {
                                try state.trackOwnership(var_id, container_var);
                            }
                        } else if (full_field.ast.tuple_like) {
                            if (full_field.ast.type_expr.unwrap()) |value_expr| {
                                if (_Engine.VarResolution.resolveVarIdFromExpr(self, @intFromEnum(value_expr), current_cfg)) |var_id| {
                                    try state.trackOwnership(var_id, container_var);
                                }
                            }
                        }
                    },
                    else => {
                        if (_Engine.VarResolution.resolveVarIdFromExpr(self, field_idx, current_cfg)) |var_id| {
                            try state.trackOwnership(var_id, container_var);
                        }
                    },
                }
            }
        }

        fn baseEscapes(
            self: *_Engine,
            state: *ProgramState,
            tree: *const std.zig.Ast,
            base_node: u32,
            container_var: ids.VarId,
        ) bool {
            const tags = tree.nodes.items(.tag);
            const main_tokens = tree.nodes.items(.main_token);
            const token_tags = tree.tokens.items(.tag);

            if (base_node < tags.len and tags[base_node] == .identifier) {
                const token = main_tokens[base_node];
                if (token < token_tags.len and token_tags[token] == .identifier) {
                    const name = tree.tokenSlice(token);
                    if (std.mem.eql(u8, name, "self")) {
                        return true;
                    }
                }
            }

            if (self.type_context) |type_ctx| {
                const token = ids.varIndex(container_var);
                if (token < token_tags.len and token_tags[token] == .identifier) {
                    const var_name = tree.tokenSlice(token);
                    if (type_ctx.getDeclType(var_name)) |type_info| {
                        if (type_info.kind == .pointer) {
                            return true;
                        }
                    }
                }
            }

            return state.getRegionState(container_var) == null;
        }

        pub fn escapeOwnedFromFieldBase(
            self: *_Engine,
            state: *ProgramState,
            tree: *const std.zig.Ast,
            base_node: u32,
            container_var: ids.VarId,
            resource_var: ids.VarId,
        ) EngineError!void {
            if (baseEscapes(self, state, tree, base_node, container_var)) {
                try state.trackEscapeOwned(resource_var);
                state.trackEscape(resource_var);
            }
        }

        pub fn recordOwnershipFromFieldAssign(
            self: *_Engine,
            state: *ProgramState,
            lhs_node: u32,
            rhs_node: u32,
            current_cfg: *const Cfg,
        ) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (lhs_node >= tags.len or tags[lhs_node] != .field_access) return;

            const field_access_data = datas[lhs_node].node_and_token;
            const base_node = @intFromEnum(field_access_data[0]);
            const container_var = _Engine.VarResolution.resolveVarIdFromExpr(self, base_node, current_cfg) orelse return;
            const resource_var = _Engine.VarResolution.resolveVarIdFromExpr(self, rhs_node, current_cfg) orelse return;
            try state.trackOwnership(resource_var, container_var);
            try _Engine.Ownership.escapeOwnedFromFieldBase(self, state, tree, base_node, container_var, resource_var);
        }

        /// `pointee.* = value` writes `value` into the block the pointer names,
        /// so everything the stored value carries belongs to the pointee from
        /// then on and leaves with it when the pointer does.
        ///
        /// The store is not a release. A pointee this frame owns keeps its
        /// resources reported, because the leak check still sees them as held.
        /// A pointee the caller owns is the other way round: the payload lands
        /// in a block outside this frame and rides out with it, so the store
        /// hands it over rather than holding it.
        ///
        /// Returns true when this store settled the right side, which it does
        /// only once the block it writes into is named. A destination this
        /// cannot place records no ownership, and reporting that store as
        /// settled would drop the escape the caller owes the right side and
        /// silence a leak no ownership record accounts for. False leaves the
        /// assignment to that handling, which is what an untracked destination
        /// has always got and what a block belonging to the caller now gets.
        pub fn recordOwnershipFromDerefAssign(
            self: *_Engine,
            state: *ProgramState,
            lhs_node: u32,
            rhs_node: u32,
            current_cfg: *const Cfg,
        ) EngineError!bool {
            const src = self.source orelse return false;
            const tree = src.ast() catch return false;
            const tags = tree.nodes.items(.tag);
            if (lhs_node >= tags.len or tags[lhs_node] != .deref) return false;

            const base_node = @intFromEnum(tree.nodes.items(.data)[lhs_node].node);
            var destination = derefAssignDestination(self, tree, base_node, current_cfg, 0) orelse return false;
            // A field destination writes into the block the field's own
            // pointer names, so the binding that block belongs to is what the
            // store hands the value to - but only while the field still holds
            // what its declaration put there.
            if (destination.base_var != null) {
                destination.pointee_var = fieldDestinationPointee(self, tree, destination.expr, lhs_node, current_cfg);
            }
            // A pointee that cannot hold a reference keeps nothing, so the
            // store hands it no ownership to move and the payload stays this
            // frame's to release, whoever owns the block it went into.
            if (pointeeCarriesNoReference(self, tree, destination.expr, current_cfg)) return true;
            // The block a parameter names is a block in the caller's frame,
            // so what this store writes into it leaves this function with
            // nothing released. Recording ownership against it would keep the
            // payload reported against a block this frame never owned and
            // cannot free from; the escape the caller's handling applies is
            // what says the payload is gone from here.
            if (parameterNodeOf(self, tree, destination.expr) != null) return false;
            try recordOwnershipFromStoredValue(self, state, tree, rhs_node, destination.container(), current_cfg, 0);
            return true;
        }

        /// The block a dereference store writes into.
        const DerefDestination = struct {
            /// Name the block is reached through, which is what the pointee's
            /// own type is read from - a wrapper that keeps the pointer is read
            /// past, so this is the name and not its parenthesized spelling.
            expr: u32,
            var_id: ids.VarId,
            /// Binding that carries the block when the destination reaches it
            /// through a field. Null when the block is named directly.
            base_var: ?ids.VarId,
            /// Binding whose region is the block itself, when the field is
            /// still filled with a pointer this can name. Null when the
            /// destination names its block directly, and when nothing proves
            /// which block the field points at.
            pointee_var: ?ids.VarId,

            /// Binding a stored value is handed to.
            ///
            /// The block a field destination writes into is the one its
            /// pointer names, so that block's own binding is what the payload
            /// belongs to: `const cache: Cache = .{ .entry = entry }` records
            /// `entry`'s block under `cache`, and a store that hands the
            /// payload to `entry` rides out of this function with either
            /// binding - as a returned `cache` through that recorded link,
            /// or as a returned `entry` directly. Linking only the root keeps
            /// the first route and loses the second, which reports bytes the
            /// caller does release.
            ///
            /// The root is what a destination that cannot name its block
            /// falls back to: escaping it carries the pointee with it, and a
            /// root that never leaves this frame leaves the payload still
            /// reported. The field name itself resolves to a hash this file
            /// cannot trace back to a binding, so it is the last resort and
            /// connects nothing that escapes.
            fn container(destination: DerefDestination) ids.VarId {
                return destination.pointee_var orelse destination.base_var orelse destination.var_id;
            }
        };

        /// The block `pointee.* = value` writes into, when this store names it.
        ///
        /// `resolveVarIdFromExpr` already reads a name, the address of a name,
        /// and a field or an element of one. Two shapes reach the same block
        /// and keep its address, each the fact a path above already relies on
        /// pointed at the destination instead of the value: a
        /// pointer-preserving cast hands back the pointer it was given, and a
        /// callee that returns exactly one of its parameters hands back that
        /// parameter's block. So `(@as(*Slot, &slot)).*` and
        /// `slotAddress(&slot).*` name `slot` the way `(&slot).*` does, and the
        /// store hands over what it carries in all three.
        /// Wrappers that hand back the very pointer they were given name the
        /// same block, so the destination is read past them before it is
        /// resolved: `(slot).*` and `slot.?.*` write into the block `slot.*`
        /// writes into, and the pointee's own type can only be read from the
        /// declaration behind the wrapper. Left as the destination, the
        /// wrapper proves nothing about its pointee, so a store of a number
        /// into a heap `usize` hands over a payload that block cannot hold -
        /// which records the bytes under it and silences the leak the store
        /// leaves behind.
        ///
        /// Nothing else proves a block: a callee this file does not declare, a
        /// callee that returns two parameters or a value it built, a cast that
        /// re-derives an address from an integer. Those yield null, which
        /// leaves the assignment to the caller's escape handling instead of
        /// naming an owner that was never resolved.
        fn derefAssignDestination(
            self: *_Engine,
            tree: *const std.zig.Ast,
            base_expr: u32,
            current_cfg: *const Cfg,
            depth: u8,
        ) ?DerefDestination {
            const tags = tree.nodes.items(.tag);
            if (depth >= max_return_depth or base_expr == 0 or base_expr >= tags.len) return null;
            if (transparentPointerChild(tree, base_expr)) |child| {
                return derefAssignDestination(self, tree, child, current_cfg, depth + 1);
            }
            if (_Engine.VarResolution.resolveVarIdFromExpr(self, base_expr, current_cfg)) |var_id| {
                return .{
                    .expr = base_expr,
                    .var_id = var_id,
                    .base_var = if (tags[base_expr] == .field_access)
                        fieldAccessBaseVar(self, tree, base_expr, current_cfg)
                    else
                        null,
                    .pointee_var = null,
                };
            }
            if (pointerCastOperand(tree, base_expr)) |value| {
                return derefAssignDestination(self, tree, value, current_cfg, depth + 1);
            }
            if (call_utils.isCallNode(tags[base_expr])) {
                const argument = returnedParamArgument(self, tree, base_expr) orelse return null;
                return derefAssignDestination(self, tree, argument, current_cfg, depth + 1);
            }
            const child = storedValueChild(tree, base_expr) orelse return null;
            return derefAssignDestination(self, tree, child, current_cfg, depth + 1);
        }

        /// The name a pointer destination is read through, past the wrappers
        /// that hand back the very pointer they were given.
        ///
        /// `(slot)` is the pointer `slot` holds and `slot.?` is the pointer an
        /// optional holds, so both name the block behind them. The block is
        /// the pointee of the binding at the end of that walk, which is what
        /// `pointeeCarriesNoReference` needs the declaration of.
        ///
        /// Nothing that changes the block qualifies. A second deref reaches
        /// the pointee of the pointee, `&slot` addresses `slot` itself rather
        /// than the block its pointer names, and a field or an element is a
        /// region of its own; each stops the walk, and the wrapper stays the
        /// destination exactly as before.
        fn transparentPointerChild(tree: *const std.zig.Ast, expr: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (expr == 0 or expr >= tags.len) return null;
            switch (tags[expr]) {
                .grouped_expression, .unwrap_optional => return @intFromEnum(datas[expr].node_and_token[0]),
                else => return null,
            }
        }

        /// Binding a field-access destination falls back to.
        ///
        /// `cache.entry.* = value` writes into the block `cache.entry` points
        /// at, and that pointer is held by `cache`, so the root of the chain
        /// carries it. `a.b.entry.*` reaches the same place through `a`.
        ///
        /// A chain whose root is not a plain name proves nothing and yields
        /// null, which leaves the field name as the only container - the
        /// treatment this store had before, so the payload stays reported.
        fn fieldAccessBaseVar(
            self: *_Engine,
            tree: *const std.zig.Ast,
            field_expr: u32,
            current_cfg: *const Cfg,
        ) ?ids.VarId {
            const root = fieldAccessRootIdentifier(tree, field_expr) orelse return null;
            return _Engine.VarResolution.resolveVarIdFromIdentifier(self, root, current_cfg);
        }

        /// The name at the end of a field-access chain, which is the binding
        /// that carries the pointer the chain reaches the block through.
        ///
        /// `cache.entry` reaches `cache` and `a.b.entry` reaches `a`. A chain
        /// that reaches anything else - a call, an element, a cast - proves
        /// nothing and yields null.
        fn fieldAccessRootIdentifier(tree: *const std.zig.Ast, field_expr: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            var node: u32 = field_expr;
            var depth: u8 = 0;
            while (depth < max_return_depth) : (depth += 1) {
                if (node >= tags.len) return null;
                switch (tags[node]) {
                    .field_access => node = @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                    .identifier => return node,
                    else => return null,
                }
            }
            return null;
        }

        /// Binding whose region is the block a field destination writes into.
        ///
        /// `cache.entry.* = value` writes into the block the pointer in
        /// `cache.entry` names, and the declaration that filled the field is
        /// what says which binding that is: `const cache: Cache = .{ .entry =
        /// entry }` put `entry`'s block there. What the store writes belongs to
        /// that block and rides out of this function with whichever binding
        /// carries it - a returned `cache`, a returned `cache.entry`, or a
        /// returned `entry` - and a link to the root alone only carries the
        /// first of those.
        ///
        /// Only a field this can read answers, so the block is named by the
        /// declaration's own initializer naming that field. A field filled by
        /// a call, by an element, by a block this does not declare - a
        /// parameter, a global - and a field no initializer spells all yield
        /// null, as does a store that comes after anything writing either
        /// binding again: what the field names is the whole of what this
        /// proves, and a later write moves it. Every one of those leaves the
        /// root as the container and the payload still reported.
        fn fieldDestinationPointee(
            self: *_Engine,
            tree: *const std.zig.Ast,
            field_expr: u32,
            store_node: u32,
            current_cfg: *const Cfg,
        ) ?ids.VarId {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (field_expr >= tags.len or tags[field_expr] != .field_access) return null;
            const holder = fieldAccessRootIdentifier(tree, field_expr) orelse return null;
            const decl = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, holder, current_cfg) orelse return null;
            // A holder declared at container scope is written from anywhere,
            // so its own body proves nothing about what its field still names.
            if (decl.is_top_level) return null;
            const full = tree.fullVarDecl(@enumFromInt(decl.decl_node)) orelse return null;
            const init: u32 = @intFromEnum(full.ast.init_node.unwrap() orelse return null);
            const field_token = datas[field_expr].node_and_token[1];
            const stored = structInitFieldValueByName(tree, init, field_token) orelse return null;
            const pointer = pointerBindingIdentifier(tree, stored) orelse return null;
            const main_tokens = tree.nodes.items(.main_token);
            const untouched = [_][]const u8{
                identifierNameAt(tree, main_tokens, holder) orelse return null,
                identifierNameAt(tree, main_tokens, pointer) orelse return null,
            };
            if (!declaredBindingsReachStore(self, tree, decl.decl_node, store_node, &untouched)) return null;
            return _Engine.VarResolution.resolveVarIdFromIdentifier(self, pointer, current_cfg);
        }

        /// Identifier naming the binding a stored pointer expression names,
        /// and null when the expression is not a binding at all.
        ///
        /// `entry`, `&entry` and `(entry)` all name `entry`; a field filled
        /// with a call, a literal or an element names nothing and yields null.
        fn pointerBindingIdentifier(tree: *const std.zig.Ast, expr: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            var node: u32 = expr;
            var depth: u8 = 0;
            while (depth < max_return_depth) : (depth += 1) {
                if (node == 0 or node >= tags.len) return null;
                switch (tags[node]) {
                    .identifier => return node,
                    .address_of, .deref, .@"try" => node = @intFromEnum(datas[node].node),
                    .grouped_expression, .unwrap_optional => node = @intFromEnum(datas[node].node_and_token[0]),
                    else => return null,
                }
            }
            return null;
        }

        /// Value a struct initializer stores in one named field, read through
        /// the wrappers that keep the initializer itself.
        ///
        /// `const cache: Cache = .{ .entry = entry }` declares the field and
        /// its value, and the initializer this declaration names is that one.
        /// A wrapper around it - a `try`, a cast that hands back the value it
        /// was given - is the same initializer under another spelling.
        ///
        /// The field named at the store and the field written by the
        /// initializer are two spellings of one name in two places, so they
        /// are matched by the name itself: the tokens differ even when the
        /// field is the same one.
        fn structInitFieldValueByName(tree: *const std.zig.Ast, expr: u32, field_token: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (field_token >= tree.tokens.len or tree.tokenTag(field_token) != .identifier) return null;
            const wanted = import_resolver.normalizeIdentifier(tree.tokenSlice(field_token));
            var node: u32 = expr;
            var depth: u8 = 0;
            while (depth < max_return_depth) : (depth += 1) {
                if (node == 0 or node >= tags.len) return null;
                var buf: [2]std.zig.Ast.Node.Index = undefined;
                if (tree.fullStructInit(&buf, @enumFromInt(node))) |init| {
                    for (init.ast.fields) |field| {
                        const field_node: u32 = @intFromEnum(field);
                        const name_token = structInitFieldNameToken(tree, field_node) orelse continue;
                        if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), wanted)) continue;
                        return structInitFieldValue(tree, field_node);
                    }
                    return null;
                }
                node = pointerCastOperand(tree, node) orelse storedValueChild(tree, node) orelse return null;
            }
            return null;
        }

        /// Token of the field name one entry of a struct initializer writes.
        ///
        /// An initializer keeps the value each field stores rather than the
        /// field it belongs to, so the name is the token the `=` follows:
        /// `.{ .entry = entry }` keeps `entry` as the entry's value, `entry`
        /// is the identifier right after the `.equal`, and the name is the
        /// identifier before it. An entry written any other way - a field
        /// given a type or an alignment, a positional value - yields null,
        /// which leaves that field unmatched rather than matched to the wrong
        /// name.
        fn structInitFieldNameToken(tree: *const std.zig.Ast, field_node: u32) ?u32 {
            const first = tree.firstToken(@enumFromInt(field_node));
            if (first < 3 or first >= tree.tokens.len) return null;
            if (tree.tokenTag(first - 1) != .equal) return null;
            if (tree.tokenTag(first - 2) != .identifier) return null;
            if (tree.tokenTag(first - 3) != .period) return null;
            return first - 2;
        }

        /// True when nothing between a declaration and one store writes any of
        /// the named bindings again, so the field that declaration filled
        /// still holds what it was given when the store runs.
        ///
        /// A later write to the holder - to the field itself or to the whole
        /// binding - moves whatever it stores into the field, and a call that
        /// takes the holder can write it as well. A later write to the pointer
        /// the field was filled with leaves the field pointing at the block it
        /// already names, but hands this binding a different one to account
        /// for. Either one takes away what the declaration proved, which is
        /// the same as the field never having been read: the root stays the
        /// container and the payload stays reported.
        fn declaredBindingsReachStore(
            self: *_Engine,
            tree: *const std.zig.Ast,
            decl_node: u32,
            store_node: u32,
            names: []const []const u8,
        ) bool {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const main_tokens = tree.nodes.items(.main_token);
            const declared_at = tree.firstToken(@enumFromInt(decl_node));
            const stored_at = tree.firstToken(@enumFromInt(store_node));
            if (declared_at >= stored_at) return false;
            for (tags, 0..) |tag, node| {
                const at = tree.firstToken(@enumFromInt(node));
                if (at <= declared_at or at >= stored_at) continue;
                if (call_utils.isCallNode(tag)) {
                    if (callNamesAnyOf(self, tree, tags, datas, main_tokens, @intCast(node), names)) return false;
                    continue;
                }
                if (!call_resolver.isAssignTag(tag)) continue;
                const lhs: u32 = @intFromEnum(datas[node].node_and_node[0]);
                if (namesAnyOf(tree, tags, datas, main_tokens, lhs, names)) return false;
            }
            return true;
        }

        /// True when a call takes any of `names` as its receiver or as one of
        /// its arguments, which is what lets it write through that binding.
        ///
        /// A proven allocator release is the one call allowed through: it
        /// disposes of what it is given rather than writing into it.
        fn callNamesAnyOf(
            self: *_Engine,
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            main_tokens: []const std.zig.Ast.TokenIndex,
            call_node: u32,
            names: []const []const u8,
        ) bool {
            var buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buf, @enumFromInt(call_node)) orelse return false;
            const release = isAllocatorReleaseCall(self, tree, call);
            if (namesAnyOf(tree, tags, datas, main_tokens, @intFromEnum(call.ast.fn_expr), names)) return true;
            for (call.ast.params) |param| {
                const param_node: u32 = @intFromEnum(param);
                if (!namesAnyOf(tree, tags, datas, main_tokens, param_node, names)) continue;
                if (release) continue;
                return true;
            }
            return false;
        }

        /// True when `node` names any of `names`.
        fn namesAnyOf(
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            main_tokens: []const std.zig.Ast.TokenIndex,
            node: u32,
            names: []const []const u8,
        ) bool {
            for (names) |name| {
                if (expressionNames(tree, tags, datas, main_tokens, node, name)) return true;
            }
            return false;
        }

        /// The argument a callee hands straight back. `slotAddress(&slot)`
        /// reaches `slot` because the callee returns the pointer it was given.
        /// `slot.firstOf(slot, other)` reaches it the same way through a
        /// method: the receiver the call site never writes is still one of the
        /// callee's declared parameters, and the position accounting is what
        /// tells the two apart. `slot.address()` reaches it through the
        /// receiver itself, which is a returned parameter too. A callee that
        /// returns two of its parameters - a receiver and a written argument,
        /// or two written arguments - names no single block and yields null.
        fn returnedParamArgument(self: *_Engine, tree: *const std.zig.Ast, call_node: u32) ?u32 {
            const returned = calleeReturnedParams(self, tree, call_node) orelse return null;
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return null;
            // The receiver is a parameter the call site never writes, so it is
            // one more candidate for the single block this names: a method
            // that returns its receiver and a written argument together names
            // two blocks and still yields null.
            var found: ?u32 = returnedReceiverExpr(returned, tree, call_node);
            for (call.ast.params, 0..) |param, position| {
                if (!returned.retainsArgument(position)) continue;
                if (found != null) return null;
                found = @intFromEnum(param);
            }
            return found;
        }

        /// True when the block `destination_expr` points at cannot hold a
        /// reference, so a dereference store into it hands it nothing to own.
        ///
        /// `p.* = bytes.len` writes a length; returning `p` afterwards carries
        /// that integer out and leaves the bytes exactly where they were.
        /// `length.* = bytes.len` is that store written through an
        /// out-parameter, and the caller's block cannot hold the bytes either.
        ///
        /// Both halves have to be written out for the answer to hold. A
        /// pointee whose type this cannot read carries a reference and keeps
        /// the transferring treatment, so an untyped `p.* = value` still moves
        /// what it stores.
        fn pointeeCarriesNoReference(
            self: *_Engine,
            tree: *const std.zig.Ast,
            destination_expr: u32,
            current_cfg: *const Cfg,
        ) bool {
            const tags = tree.nodes.items(.tag);
            if (destination_expr >= tags.len or tags[destination_expr] != .identifier) return false;
            // A parameter carries no declaration of its own, so the type it was
            // written with is read where it is written: in its prototype.
            if (parameterNodeOf(self, tree, destination_expr)) |param| {
                const written = parameterTypeNode(tree, param) orelse return false;
                const pointee = pointeeTypeNode(tree, written) orelse return false;
                return typeNodeCarriesNoReference(tree, pointee);
            }
            const decl = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, destination_expr, current_cfg) orelse return false;
            if (decl.is_top_level) return false;
            const full = tree.fullVarDecl(@enumFromInt(decl.decl_node)) orelse return false;
            const pointee = pointeeTypeNodeOf(self, tree, full) orelse return false;
            return typeNodeCarriesNoReference(tree, pointee);
        }

        /// Parameter an identifier names, when the binding it resolves to is
        /// one.
        ///
        /// `findBinding` places a name the way the enclosing scope does, so a
        /// use inside a function names that function's parameter even where a
        /// local of the same spelling shadows it further out, and a name
        /// declared after the use does not reach back for it. Nothing else in
        /// this file can answer that: a parameter is bound from its prototype
        /// and carries no declaration node, so every declaration lookup misses
        /// it - which is why `pointeeCarriesNoReference` has to ask this
        /// question before it reads a declaration.
        ///
        /// Null is the fail-closed answer, and it is what every name that is
        /// not a parameter of this function gets: a local, a field, a global,
        /// and a use the index cannot place at all.
        fn parameterNodeOf(self: *_Engine, tree: *const std.zig.Ast, identifier: u32) ?u32 {
            const src = self.source orelse return null;
            const lexical = lexicalIndexFor(src, tree) orelse return null;
            const tags = tree.nodes.items(.tag);
            const main_tokens = tree.nodes.items(.main_token);
            const token_tags = tree.tokens.items(.tag);
            if (identifier >= tags.len or tags[identifier] != .identifier) return null;
            const token = main_tokens[identifier];
            if (token >= token_tags.len or token_tags[token] != .identifier) return null;
            const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));
            const binding = lexical.findBinding(name, token) orelse return null;
            if (binding.kind != .parameter) return null;
            return binding.node;
        }

        /// Type a parameter is written with, read through the two shapes a
        /// prototype spells one in.
        ///
        /// A prototype keeps one node per declared parameter, and that node is
        /// the type that was written: `fn store(length: *usize)` keeps the
        /// `*usize` itself. A parameter spelled as a declaration of its own
        /// keeps its type one step down from that node instead. Either way a
        /// parameter with no written type - `fn store(value: anytype)` - answers
        /// null, which leaves the caller on its transferring default.
        fn parameterTypeNode(tree: *const std.zig.Ast, param: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (param >= tags.len) return null;
            if (!import_resolver.isVarDeclTag(tags[param])) return param;
            const full = tree.fullVarDecl(@enumFromInt(param)) orelse return null;
            const written = full.ast.type_node.unwrap() orelse return null;
            return @intFromEnum(written);
        }

        /// The type the block a declaration points at is made of, whether the
        /// declaration writes that type down or infers it from the allocation
        /// it was made for.
        ///
        /// `const slot: *usize` writes the pointee as `usize`, and
        /// `const slot = try allocator.create(usize)` names the same pointee in
        /// the allocator's type argument. Reading it from the allocation is
        /// what keeps `slot.* = bytes.len` from handing the bytes to a block
        /// that can only hold a number.
        ///
        /// A declaration whose pointee neither spelling yields null, which
        /// leaves the caller on its transferring default.
        fn pointeeTypeNodeOf(
            self: *_Engine,
            tree: *const std.zig.Ast,
            full: std.zig.Ast.full.VarDecl,
        ) ?u32 {
            if (full.ast.type_node.unwrap()) |written| return pointeeTypeNode(tree, @intFromEnum(written));
            return allocatedTypeNode(self, tree, full);
        }

        /// Type argument of the allocator call that made a block, which is the
        /// type of the block itself.
        ///
        /// The proof is the allocation, not the method's name: the call has to
        /// resolve to a `std.mem.Allocator` allocation first, the same proof
        /// the engine uses to call the block a leak at all. A `create` on
        /// anything else - a container method of the same name, a receiver of
        /// an unrelated type - reads no type argument at all, and the pointee
        /// stays unknown.
        fn allocatedTypeNode(
            self: *_Engine,
            tree: *const std.zig.Ast,
            full: std.zig.Ast.full.VarDecl,
        ) ?u32 {
            const init: u32 = @intFromEnum(full.ast.init_node.unwrap() orelse return null);
            const call_node = storedValueCallNode(tree, init) orelse return null;
            const tags = tree.nodes.items(.tag);
            const allocation = _Engine.ResourceCalls.resolveResourceCallFromExpr(self, tree, call_node) orelse return null;
            if (allocation.kind != .alloc) return null;
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const full_call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return null;
            const callee: u32 = @intFromEnum(full_call.ast.fn_expr);
            if (callee >= tags.len or tags[callee] != .field_access) return null;
            const member = tree.nodes.items(.data)[callee].node_and_token[1];
            if (member >= tree.tokens.len or tree.tokenTag(member) != .identifier) return null;
            if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(member)), "create")) return null;
            return call_utils.callParam(tree, call_node, 0);
        }

        /// The allocator call a declaration's initializer makes, read through
        /// the wrappers that keep its pointer.
        ///
        /// `const slot = @as(*usize, try a.create(usize))` allocates the very
        /// block `const slot = try a.create(usize)` does: a
        /// pointer-preserving cast hands back the pointer it was given, and
        /// `try` only guards the call. Both are read through here for the
        /// same reason `derefAssignDestination` reads through them to name a
        /// block - a pointee spelled behind either one is the same pointee,
        /// and leaving it unknown would hand a `usize` store to a block that
        /// can only hold a number.
        ///
        /// Every step reads a strict child, so the walk ends on its own; the
        /// depth bound stops a shape this cannot read. An initializer that
        /// reaches no call yields null, which leaves the pointee unknown and
        /// the caller on its transferring default.
        fn storedValueCallNode(tree: *const std.zig.Ast, expr: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            var node: u32 = expr;
            var depth: u8 = 0;
            while (depth < max_return_depth) : (depth += 1) {
                if (node == 0 or node >= tags.len) return null;
                if (call_utils.isCallNode(tags[node])) return node;
                node = pointerCastOperand(tree, node) orelse storedValueChild(tree, node) orelse return null;
            }
            return null;
        }

        /// The type a written pointer type points at, one level down. `*usize`
        /// yields `usize`. Anything not written as a pointer yields null, which
        /// leaves the caller on its default.
        fn pointeeTypeNode(tree: *const std.zig.Ast, written: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (written >= tags.len) return null;
            switch (tags[written]) {
                .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                    const ptr = tree.fullPtrType(@enumFromInt(written)) orelse return null;
                    return @intFromEnum(ptr.ast.child_type);
                },
                .grouped_expression => return pointeeTypeNode(tree, @intFromEnum(tree.nodes.items(.data)[written].node_and_token[0])),
                else => return null,
            }
        }

        /// Hand every region a stored value carries to `container_var`.
        fn recordOwnershipFromStoredValue(
            self: *_Engine,
            state: *ProgramState,
            tree: *const std.zig.Ast,
            expr: u32,
            container_var: ids.VarId,
            current_cfg: *const Cfg,
            depth: u8,
        ) EngineError!void {
            if (depth >= 16 or expr == 0 or expr >= tree.nodes.items(.tag).len) return;
            switch (tree.nodes.items(.tag)[expr]) {
                .identifier => {
                    const var_id = _Engine.VarResolution.resolveVarIdFromIdentifier(self, expr, current_cfg) orelse return;
                    try state.trackOwnership(var_id, container_var);
                },
                .field_access => {
                    const access = tree.nodes.items(.data)[expr].node_and_token;
                    try recordOwnershipFromStoredValue(self, state, tree, @intFromEnum(access[0]), container_var, current_cfg, depth + 1);
                },
                .array_access => {
                    const pair = tree.nodes.items(.data)[expr].node_and_node;
                    try recordOwnershipFromStoredValue(self, state, tree, @intFromEnum(pair[0]), container_var, current_cfg, depth + 1);
                },
                .call, .call_comma, .call_one, .call_one_comma => {
                    const returned = calleeReturnedParams(self, tree, expr) orelse return;
                    if (returned.mask == 0) return;
                    // A receiver the callee hands back is retained by the store
                    // on the same terms as a written argument, so a container
                    // that keeps the returned value keeps both when the callee
                    // returns both.
                    if (returnedReceiverExpr(returned, tree, expr)) |receiver| {
                        try recordOwnershipFromStoredValue(self, state, tree, receiver, container_var, current_cfg, depth + 1);
                    }
                    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
                    const call = tree.fullCall(&call_buf, @enumFromInt(expr)) orelse return;
                    for (call.ast.params, 0..) |param, position| {
                        // Only an argument the callee hands back is retained by
                        // the store; the rest stay the caller's to release.
                        if (!returned.retainsArgument(position)) continue;
                        try recordOwnershipFromStoredValue(self, state, tree, @intFromEnum(param), container_var, current_cfg, depth + 1);
                    }
                },
                .struct_init,
                .struct_init_comma,
                .struct_init_one,
                .struct_init_one_comma,
                .struct_init_dot,
                .struct_init_dot_comma,
                .struct_init_dot_two,
                .struct_init_dot_two_comma,
                => try _Engine.Ownership.recordOwnershipFromExpr(self, state, expr, container_var, current_cfg),
                else => {
                    const child = pointerCastOperand(tree, expr) orelse storedValueChild(tree, expr) orelse return;
                    try recordOwnershipFromStoredValue(self, state, tree, child, container_var, current_cfg, depth + 1);
                },
            }
        }

        /// Child expression a stored value reads through without naming a new
        /// region of its own.
        fn storedValueChild(tree: *const std.zig.Ast, expr: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (expr >= tags.len) return null;
            switch (tags[expr]) {
                .address_of, .deref, .@"try" => return @intFromEnum(tree.nodes.items(.data)[expr].node),
                .grouped_expression, .unwrap_optional => return @intFromEnum(tree.nodes.items(.data)[expr].node_and_token[0]),
                .@"catch", .@"orelse" => {
                    return @intFromEnum(tree.nodes.items(.data)[expr].node_and_node[0]);
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr)) orelse return null;
                    return @intFromEnum(slice.ast.sliced);
                },
                else => return null,
            }
        }

        /// Parameters a callee hands back to its caller, or null when the callee
        /// proves nothing.
        ///
        /// `parseInto(src)` returning `.{ .src = src }` returns its first
        /// parameter and nothing else, so a caller storing that result may
        /// charge the first argument - and only the first argument - to
        /// whatever it stores into. `keepFirst(src, extra)` returning
        /// `.{ .src = src }` leaves `extra` the caller's to release even though
        /// the same store moved something into the pointee.
        ///
        /// `mask` counts positions in the callee's own prototype, which for a
        /// method starts with the receiver the call site does not write.
        /// `implicit_self_count` is how many of those leading positions the
        /// receiver fills, so the argument written at `i` sits at position
        /// `i + implicit_self_count`. Counting the call's arguments against the
        /// prototype directly would read `slot.firstOf(slot, other)`'s
        /// returned `target` as `other`, and hand the store to the wrong block.
        /// The leading positions name the receiver expression rather than an
        /// argument, so a callee that returns one of them is read through
        /// `returnedReceiverExpr`.
        ///
        /// The mask is a union over the callee's returns: a function may hand a
        /// parameter back on one path and not on another, and the union is the
        /// set of arguments a caller has to stop tracking. A return that
        /// carries nothing - an error, or a bare `return;` - adds no bit.
        ///
        /// Null is the fail-closed answer. A callee this cannot resolve, one
        /// that returns a value built from anything it was not given - a fresh
        /// allocation, an opaque call, a constant - and one whose parameters
        /// cannot be lined up with its argument positions all prove nothing,
        /// which leaves every argument owned by the caller and still reported.
        fn calleeReturnedParams(self: *_Engine, tree: *const std.zig.Ast, call_node: u32) ?ReturnedParams {
            var storage: [1]import_resolver.File = undefined;
            const files = projectFiles(self, tree, &storage) orelse return null;
            const start_index = fileIndexOf(files, tree) orelse return null;
            const resolver = call_resolver.ProjectTypeResolver{ .files = files, .file_index = start_index };
            const callable = resolver.resolveCallableAtCall(call_node) orelse return null;
            if (callable.file_index >= files.len) return null;
            const callee_file = files[callable.file_index];
            const callee_tree = callee_file.tree;
            if (callee_tree.errors.len != 0) return null;
            const lexical = callee_file.lexical_index orelse return null;
            const fn_decl = fnDeclOfProto(callee_tree, callable.proto_node) orelse return null;

            var params: [max_returned_params]std.zig.Ast.TokenIndex = undefined;
            const param_count = declaredParamNameTokens(callee_tree, callable.proto_node, &params) orelse return null;

            var mask: u32 = 0;
            const tags = callee_tree.nodes.items(.tag);
            for (tags, 0..) |tag, node_index| {
                if (tag != .@"return") continue;
                const node: u32 = @intCast(node_index);
                // A `return` written inside a function nested in the callee
                // belongs to that nested function, not to the callee.
                if (lexical.enclosingFunction(callee_tree.nodeMainToken(@enumFromInt(node))) != fn_decl) continue;
                const value: ?std.zig.Ast.Node.Index = callee_tree.nodes.items(.data)[node].opt_node.unwrap();
                const expr: ?u32 = if (value) |index| @intFromEnum(index) else null;
                const shape = returnShape(lexical, callee_tree, expr, params[0..param_count], 0);
                switch (shape.kind) {
                    .carries_nothing => {},
                    .parameters => mask |= shape.mask,
                    .other => return null,
                }
            }
            return .{ .mask = mask, .implicit_self_count = callable.implicit_self_count };
        }

        /// One callee's returned parameters, in the two coordinate systems its
        /// callers have to line up.
        const ReturnedParams = struct {
            /// One bit per declared position of the callee's prototype.
            mask: u32,
            /// Leading prototype positions the call site fills through the
            /// receiver rather than through its argument list. Zero for a
            /// plain function or for a call through a type namespace, because
            /// neither writes a receiver argument.
            implicit_self_count: usize,

            /// True when the argument the call site writes at
            /// `explicit_position` is one the callee hands back.
            fn retainsArgument(returned: ReturnedParams, explicit_position: usize) bool {
                const position = explicit_position + returned.implicit_self_count;
                if (position >= max_returned_params) return false;
                return returned.mask & (@as(u32, 1) << @intCast(position)) != 0;
            }

            /// True when the callee hands back the block its receiver names,
            /// which is what `fn address(self: *Box) *Box { return self; }`
            /// does. The leading positions all name the one receiver
            /// expression, so any of them being returned retains that single
            /// block.
            fn retainsReceiver(returned: ReturnedParams) bool {
                if (returned.implicit_self_count == 0) return false;
                for (0..returned.implicit_self_count) |position| {
                    if (returned.mask & (@as(u32, 1) << @intCast(position)) != 0) return true;
                }
                return false;
            }
        };

        /// Receiver expression a method call hands to its callee without
        /// writing it, when the callee hands that block straight back.
        ///
        /// `slot.address().*` names `slot` the way `(&slot).*` does, because
        /// the callee returns exactly the pointer it was given. That makes the
        /// receiver a returned parameter like any other, reached through the
        /// call's own callee expression.
        ///
        /// Null is the fail-closed answer, and it is what a plain function and
        /// a call through a type namespace - `Box.make()` - get: neither
        /// writes a receiver, and the resolver reports no implicit self for
        /// either, so nothing here shifts an argument's position either.
        fn returnedReceiverExpr(returned: ReturnedParams, tree: *const std.zig.Ast, call_node: u32) ?u32 {
            if (!returned.retainsReceiver()) return null;
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return null;
            const callee: u32 = @intFromEnum(call.ast.fn_expr);
            const tags = tree.nodes.items(.tag);
            if (callee >= tags.len or tags[callee] != .field_access) return null;
            return @intFromEnum(tree.nodes.items(.data)[callee].node_and_token[0]);
        }

        /// Project file list the callee walk may follow. Prefers the whole
        /// project resolver so a callee reached through a namespace or a
        /// re-export is still read from the file that declares it; without one
        /// the walk is confined to the analyzed file and simply finds nothing
        /// to prove.
        fn projectFiles(
            self: *_Engine,
            tree: *const std.zig.Ast,
            storage: *[1]import_resolver.File,
        ) ?[]const import_resolver.File {
            if (self.type_context) |type_ctx| {
                if (type_ctx.project_resolver) |project| {
                    if (project.files.len != 0) return project.files;
                }
            }
            const source = self.source orelse return null;
            storage[0] = .{
                .path = source.getFilePath(),
                .tree = tree,
                .lexical_index = lexicalIndexFor(source, tree),
            };
            return storage[0..1];
        }

        fn fileIndexOf(files: []const import_resolver.File, tree: *const std.zig.Ast) ?usize {
            for (files, 0..) |file, index| {
                if (file.tree == tree) return index;
            }
            return null;
        }

        /// What one returned value carries. `mask` is meaningful only for
        /// `.parameters`, where it names the callee parameters the value was
        /// built from.
        const ReturnShape = struct {
            kind: enum { carries_nothing, parameters, other },
            mask: u32 = 0,
        };

        const max_returned_params = 32;
        const max_return_depth = 16;

        fn returnShape(
            lexical: *const LexicalIndex,
            tree: *const std.zig.Ast,
            expr: ?u32,
            params: []const std.zig.Ast.TokenIndex,
            depth: u8,
        ) ReturnShape {
            const node = expr orelse return .{ .kind = .carries_nothing };
            if (depth >= max_return_depth or node >= tree.nodes.items(.tag).len) return .{ .kind = .other };
            const tags = tree.nodes.items(.tag);
            switch (tags[node]) {
                .error_value => return .{ .kind = .carries_nothing },
                .identifier => {
                    const position = returnedParamPosition(lexical, tree, node, params) orelse return .{ .kind = .other };
                    return .{ .kind = .parameters, .mask = @as(u32, 1) << @intCast(position) };
                },
                .grouped_expression, .unwrap_optional => return returnShape(lexical, tree, storedValueChild(tree, node), params, depth + 1),
                .@"try" => return returnShape(lexical, tree, @intFromEnum(tree.nodes.items(.data)[node].node), params, depth + 1),
                .struct_init,
                .struct_init_comma,
                .struct_init_one,
                .struct_init_one_comma,
                .struct_init_dot,
                .struct_init_dot_comma,
                .struct_init_dot_two,
                .struct_init_dot_two_comma,
                => {
                    var buffer: [2]std.zig.Ast.Node.Index = undefined;
                    const struct_init = tree.fullStructInit(&buffer, @enumFromInt(node)) orelse return .{ .kind = .other };
                    var shape: ReturnShape = .{ .kind = .carries_nothing };
                    for (struct_init.ast.fields) |field| {
                        const value = structInitFieldValue(tree, @intFromEnum(field)) orelse return .{ .kind = .other };
                        const field_shape = returnShape(lexical, tree, value, params, depth + 1);
                        if (field_shape.kind == .other) return .{ .kind = .other };
                        if (field_shape.kind == .parameters) {
                            shape.kind = .parameters;
                            shape.mask |= field_shape.mask;
                        }
                    }
                    return shape;
                },
                else => return .{ .kind = .other },
            }
        }

        /// Value expression one field of a struct initializer carries. A field
        /// written out is a `container_field` node; the anonymous
        /// `.{ .src = src }` stores the field's value expression itself, so any
        /// other node is already the value.
        fn structInitFieldValue(tree: *const std.zig.Ast, field_node: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (field_node >= tags.len) return null;
            switch (tags[field_node]) {
                .container_field, .container_field_init, .container_field_align => {
                    const full_field = tree.fullContainerField(@enumFromInt(field_node)) orelse return null;
                    return @intFromEnum(full_field.ast.value_expr.unwrap() orelse return null);
                },
                else => return field_node,
            }
        }

        /// Position of the parameter an identifier in a `return` names.
        ///
        /// The use is resolved to its declaration first. Two occurrences of one
        /// spelling are two different tokens, so the use's own token says
        /// nothing about which declaration it means; the declaration's token is
        /// what lines up with the parameter list.
        fn returnedParamPosition(
            lexical: *const LexicalIndex,
            tree: *const std.zig.Ast,
            node: u32,
            params: []const std.zig.Ast.TokenIndex,
        ) ?usize {
            const token = tree.nodes.items(.main_token)[node];
            const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));
            const binding = lexical.findBinding(name, token) orelse return null;
            if (binding.kind != .parameter) return null;
            for (params, 0..) |declared, position| {
                if (declared == binding.name_token) return position;
            }
            return null;
        }

        /// Name token of every declared parameter, in prototype order.
        ///
        /// The prototype's own parameter iterator is the count, because it is
        /// what knows that `anytype T` and `...` take a declared position
        /// without appearing in the prototype's parameter list: skipping them
        /// would shift every position after them and hand the caller the wrong
        /// argument. A parameter whose name cannot be read leaves the answer
        /// null for the same reason.
        fn declaredParamNameTokens(
            tree: *const std.zig.Ast,
            proto: u32,
            out: *[max_returned_params]std.zig.Ast.TokenIndex,
        ) ?usize {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const full_proto = tree.fullFnProto(&buffer, @enumFromInt(proto)) orelse return null;
            var declared = full_proto.iterate(tree);
            var count: usize = 0;
            while (declared.next()) |param| {
                if (count >= out.len) return null;
                out[count] = param.name_token orelse return null;
                count += 1;
            }
            return count;
        }

        /// Declaration that owns a prototype. The lexical index answers a
        /// function by its prototype node, and a prototype carries no link back
        /// to the declaration - which is the node a return's enclosing function
        /// names. A prototype that was never declared has no returns to read.
        fn fnDeclOfProto(tree: *const std.zig.Ast, proto: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            for (tags, 0..) |tag, node| {
                if (tag != .fn_decl) continue;
                if (@intFromEnum(datas[node].node_and_node[0]) == proto) return @intCast(node);
            }
            return null;
        }

        /// The source's own syntax facts, borrowed for the AST they describe. A
        /// foreign tree or a source that cannot index answers null, which
        /// leaves the caller on the unindexed behavior instead of failing a
        /// query. The source stays the sole owner of that storage.
        fn lexicalIndexFor(source: *Source, tree: *const std.zig.Ast) ?*const LexicalIndex {
            const source_tree = source.ast() catch return null;
            if (tree != source_tree) return null;
            return source.lexicalIndex() catch null;
        }

        /// `allocator.realloc(buf, n)` hands the block to the new one, so the
        /// original no longer exists once the call succeeds. On failure the
        /// original is untouched and any errdefer still owns it, which is why
        /// this is only applied where the engine has proven the success edge.
        pub fn consumeReallocSourceInExpr(
            self: *_Engine,
            state: *ProgramState,
            expr: u32,
            current_cfg: *const Cfg,
        ) EngineError!bool {
            const src = self.source orelse return false;
            const tree = src.ast() catch return false;
            const realloc = _Engine.ResourceCalls.resolveResourceCallFromExpr(self, tree, expr) orelse return false;
            if (realloc.kind != .realloc) return false;
            const source_expr = realloc.target_expr orelse return false;
            const source_var = _Engine.VarResolution.resolveVarIdFromExpr(self, source_expr, current_cfg) orelse return false;
            try state.trackFree(source_var, _Engine.Ownership.resolveCallToken(self, realloc.call_node));
            return true;
        }

        /// `aggregate[index] = payload` hands the payload's contents to the
        /// aggregate, so the resources the payload holds belong to the
        /// aggregate from then on and travel with it. Without this a returned
        /// aggregate reports its own payload's resources as leaked, because
        /// they still name the local payload as their owner.
        ///
        /// The transfer is made only when `storeKeepsPayloadReachable` can
        /// prove the store keeps the payload reachable and nothing later
        /// drops it. Every case it cannot prove - an index it does not
        /// recognise, a second write through the aggregate, an opaque call
        /// that takes it - leaves the resources owned by the payload, so they
        /// keep leaking.
        ///
        /// One of those cases is the aggregate itself being replaced: the
        /// element the store wrote went in with the block and leaves with it,
        /// so the replacement's report of the block it dropped is the report
        /// for what the store put in it. `payloadIsLostWithAggregate` reads
        /// that shape off the function.
        ///
        /// Returns true when this store settles the payload, which is only
        /// for a payload that owns something: storing into an aggregate moves
        /// a value's contents, it does not make the value escape, so the
        /// caller must not apply its own escape handling here. Every other
        /// assignment returns false and is left to that handling.
        pub fn recordOwnershipFromAggregateStore(
            self: *_Engine,
            state: *ProgramState,
            lhs_node: u32,
            rhs_node: u32,
            current_cfg: *const Cfg,
        ) EngineError!bool {
            const src = self.source orelse return false;
            const tree = src.ast() catch return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (lhs_node >= tags.len or tags[lhs_node] != .array_access) return false;

            const pair = datas[lhs_node].node_and_node;
            const base_node: u32 = @intFromEnum(pair[0]);
            const index_node: u32 = @intFromEnum(pair[1]);

            const payload = _Engine.VarResolution.resolveVarIdFromExpr(self, rhs_node, current_cfg) orelse return false;
            // A plain value stored into an aggregate owns nothing, so nothing
            // moves and an allocation that is stored but never released is
            // still reported against the value that leaked it.
            if (!state.hasOwnedResources(payload)) return false;
            if (base_node >= tags.len or tags[base_node] != .identifier) return true;

            const aggregate = _Engine.VarResolution.resolveVarIdFromExpr(self, base_node, current_cfg) orelse return false;
            // A whole-place replacement of the aggregate drops the element
            // this store filled, so the payload's resources leave with it
            // rather than staying behind as a second claim on one lost write.
            if (payloadIsLostWithAggregate(self, tree, current_cfg, base_node, lhs_node)) {
                try state.trackEscapeOwned(payload);
                return true;
            }
            if (index_node >= tags.len or tags[index_node] != .identifier) return true;

            // An unproven store is a decided store: the payload keeps what it
            // owns, so the resources it drops here are still reported.
            if (!storeKeepsPayloadReachable(self, tree, current_cfg, base_node, index_node, lhs_node)) return true;

            state.adoptOwnedResources(payload, aggregate);
            return true;
        }

        /// True when the function replaces `dst`'s whole binding after the
        /// store into it and nothing in it outlives that replacement, so what
        /// `dst[index] = payload` put in the aggregate leaves the frame with
        /// the block the replacement drops.
        ///
        /// A name that outlives the replacement decides it against that: a
        /// second binding handed the aggregate, or a call that takes it - a
        /// release included, which disposes of the block and leaves the
        /// payload's own acquisition standing - keeps the frame able to reach
        /// what the store put in it, and that acquisition is then the one to
        /// report. Only a plain assignment replaces the whole binding; an
        /// element or field store writes through it and leaves the aggregate
        /// where it is.
        fn payloadIsLostWithAggregate(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            dst_node: u32,
            destination_node: u32,
        ) bool {
            const fn_node = current_cfg.fn_ast_node orelse return false;
            const fn_index = ids.astIndex(fn_node);
            const parent_map = self.getParentMap(tree) catch return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const main_tokens = tree.nodes.items(.main_token);
            const dst_name = identifierNameAt(tree, main_tokens, dst_node) orelse return false;
            const stored_at = tree.firstToken(@enumFromInt(destination_node));

            var replaced = false;
            for (tags, 0..) |tag, node| {
                const index: u32 = @intCast(node);
                if (!ast_walk.isAncestor(fn_index, index, parent_map)) continue;
                // Whatever the frame wrote before the store cannot have been
                // handed the aggregate after the store filled it.
                if (tree.firstToken(@enumFromInt(index)) <= stored_at) continue;

                if (call_utils.isCallNode(tag)) {
                    if (callNamesAggregate(tree, tags, datas, main_tokens, index, dst_name)) return false;
                    continue;
                }
                if (import_resolver.isVarDeclTag(tag)) {
                    const full = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
                    const init = full.ast.init_node.unwrap() orelse continue;
                    if (expressionNames(tree, tags, datas, main_tokens, @intFromEnum(init), dst_name)) return false;
                    continue;
                }
                if (tag != .assign) continue;
                const lhs: u32 = @intFromEnum(datas[index].node_and_node[0]);
                if (lhs >= tags.len or tags[lhs] != .identifier) continue;
                if (tokenIsNamed(tree, main_tokens[lhs], dst_name)) replaced = true;
            }
            return replaced;
        }

        /// True when a call names `name` as its receiver or as any of its
        /// arguments, a proven allocator release included.
        ///
        /// `callTakesName` lets a release through because it disposes of what
        /// it is given rather than writing into it. This question is the
        /// other one: a release settles the block it is handed and leaves
        /// everything stored in that block standing, so it stands for a name
        /// that outlives the store.
        fn callNamesAggregate(
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            main_tokens: []const std.zig.Ast.TokenIndex,
            call_node: u32,
            name: []const u8,
        ) bool {
            var buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buf, @enumFromInt(call_node)) orelse return false;
            if (expressionNames(tree, tags, datas, main_tokens, @intFromEnum(call.ast.fn_expr), name)) return true;
            for (call.ast.params) |param| {
                if (expressionNames(tree, tags, datas, main_tokens, @intFromEnum(param), name)) return true;
            }
            return false;
        }

        /// Prove `dst[index] = payload` lands in a fresh slot that stays
        /// reachable, so handing the payload's resources to `dst` cannot hide
        /// a lost one.
        ///
        /// The proof is the shape config.zig actually has - a loop that fills
        /// an aggregate and advances a cursor as its last act:
        ///
        /// ```
        /// for (...) |item| {
        ///     ...
        ///     dst[index] = payload;   // penultimate statement
        ///     index += 1;              // last statement, literal one
        /// }
        /// ```
        ///
        /// Requires all of: the store is the penultimate statement of a `for`
        /// body; that body's last statement is `<index> += 1`; `dst` and
        /// `index` are declared outside the loop; and nothing else in the
        /// function writes the index or reaches `dst` - no other store, no
        /// field or whole-place assignment, no deref write, and no call that
        /// takes `dst` or `index` by value or address (a proven allocator
        /// release is the one call allowed through).
        ///
        /// Any other shape - an index advanced by zero or by a non-literal,
        /// an increment outside the loop body, a second write, an opaque call
        /// - is rejected, so the payload keeps its own resources and they keep
        /// leaking.
        fn storeKeepsPayloadReachable(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            dst_node: u32,
            index_node: u32,
            store_node: u32,
        ) bool {
            const fn_node = current_cfg.fn_ast_node orelse return false;
            const fn_index = ids.astIndex(fn_node);
            const parent_map = self.getParentMap(tree) catch return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const main_tokens = tree.nodes.items(.main_token);

            const dst_name = identifierNameAt(tree, main_tokens, dst_node) orelse return false;
            const index_name = identifierNameAt(tree, main_tokens, index_node) orelse return false;

            // The store sits inside a `for` body, one statement from the end.
            if (store_node >= parent_map.len) return false;
            const assignment = parent_map[store_node];
            if (assignment >= tags.len or tags[assignment] != .assign or assignment >= parent_map.len) return false;
            const body = parent_map[assignment];
            if (body >= tags.len or body >= parent_map.len) return false;
            const loop_node = parent_map[body];
            if (loop_node >= tags.len) return false;
            if (tags[loop_node] != .@"for" and tags[loop_node] != .for_simple) return false;

            var scratch: [2]u32 = undefined;
            const statements = blockStatements(tree, tags, datas, body, &scratch) orelse return false;
            if (statements.len < 2) return false;
            const cursor_step = statements[statements.len - 1];
            if (statements[statements.len - 2] != assignment) return false;
            if (!isCursorStep(tree, tags, datas, main_tokens, cursor_step, index_name)) return false;

            // Both bindings are declared outside the loop that advances them.
            const decl_info = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, dst_node, current_cfg) orelse return false;
            if (decl_info.is_top_level) return false;
            const index_decl = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, index_node, current_cfg) orelse return false;
            if (index_decl.is_top_level) return false;
            if (ast_walk.isAncestor(loop_node, decl_info.decl_node, parent_map)) return false;
            if (ast_walk.isAncestor(loop_node, index_decl.decl_node, parent_map)) return false;

            // Nothing else touches either name.
            for (tags, 0..) |tag, node| {
                if (!ast_walk.isAncestor(fn_index, @intCast(node), parent_map)) continue;
                if (call_utils.isCallNode(tag)) {
                    if (callTakesName(self, tree, tags, datas, main_tokens, @intCast(node), dst_name)) return false;
                    if (callTakesName(self, tree, tags, datas, main_tokens, @intCast(node), index_name)) return false;
                    continue;
                }
                if (!call_resolver.isAssignTag(tag)) continue;
                if (node == assignment or node == cursor_step) continue;

                const lhs: u32 = @intFromEnum(datas[node].node_and_node[0]);
                if (lhs >= tags.len) continue;
                switch (tags[lhs]) {
                    .identifier => {
                        if (tokenIsNamed(tree, main_tokens[lhs], dst_name)) return false;
                        if (tokenIsNamed(tree, main_tokens[lhs], index_name)) return false;
                    },
                    .array_access, .field_access, .deref, .unwrap_optional => {
                        if (expressionNames(tree, tags, datas, main_tokens, lhs, dst_name)) return false;
                        if (expressionNames(tree, tags, datas, main_tokens, lhs, index_name)) return false;
                    },
                    else => {},
                }
            }
            return true;
        }

        /// True for `<name> += 1` and nothing else: a cursor that actually
        /// moves by one on every pass.
        fn isCursorStep(
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            main_tokens: []const std.zig.Ast.TokenIndex,
            node: u32,
            name: []const u8,
        ) bool {
            if (node >= tags.len or tags[node] != .assign_add) return false;
            const pair = datas[node].node_and_node;
            const lhs: u32 = @intFromEnum(pair[0]);
            const rhs: u32 = @intFromEnum(pair[1]);
            if (lhs >= tags.len or tags[lhs] != .identifier) return false;
            if (rhs >= tags.len or tags[rhs] != .number_literal) return false;
            if (!tokenIsNamed(tree, main_tokens[lhs], name)) return false;
            return std.mem.eql(u8, tree.tokenSlice(tree.firstToken(@enumFromInt(rhs))), "1");
        }

        /// Borrowed statement list of a block-shaped node; a node that is
        /// already a single expression counts as one statement.
        fn blockStatements(
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            node: u32,
            scratch: *[2]u32,
        ) ?[]const u32 {
            if (node >= tags.len) return null;
            switch (tags[node]) {
                .block, .block_semicolon => {
                    const range = datas[node].extra_range;
                    const start: usize = @intFromEnum(range.start);
                    const end: usize = @intFromEnum(range.end);
                    return tree.extra_data[start..end];
                },
                .block_two, .block_two_semicolon => {
                    const opt_nodes = datas[node].opt_node_and_opt_node;
                    var count: usize = 0;
                    if (opt_nodes[0].unwrap()) |first| {
                        scratch[count] = @intFromEnum(first);
                        count += 1;
                    }
                    if (opt_nodes[1].unwrap()) |second| {
                        scratch[count] = @intFromEnum(second);
                        count += 1;
                    }
                    return scratch[0..count];
                },
                else => {
                    scratch[0] = node;
                    return scratch[0..1];
                },
            }
        }

        /// True when a call takes `name` (or `&name`) as receiver or argument.
        /// Releasing the aggregate is not aliasing it, so a proven allocator
        /// release is the one call shape allowed through.
        fn callTakesName(
            self: *_Engine,
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            main_tokens: []const std.zig.Ast.TokenIndex,
            call_node: u32,
            name: []const u8,
        ) bool {
            return callNamesAnyOf(self, tree, tags, datas, main_tokens, call_node, &.{name});
        }

        fn isAllocatorReleaseCall(
            self: *_Engine,
            tree: *const std.zig.Ast,
            call: std.zig.Ast.full.Call,
        ) bool {
            const tags = tree.nodes.items(.tag);
            const callee: u32 = @intFromEnum(call.ast.fn_expr);
            if (callee >= tags.len or tags[callee] != .field_access) return false;
            const access = tree.nodes.items(.data)[callee].node_and_token;
            const member = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
            if (!std.mem.eql(u8, member, "free") and !std.mem.eql(u8, member, "destroy")) return false;
            return allocator_utils.isAllocatorExpr(tree, self.type_context, @intFromEnum(access[0]));
        }

        /// True when `name` occurs as an identifier anywhere in `node`.
        fn expressionNames(
            tree: *const std.zig.Ast,
            tags: []const std.zig.Ast.Node.Tag,
            datas: []const std.zig.Ast.Node.Data,
            main_tokens: []const std.zig.Ast.TokenIndex,
            node: u32,
            name: []const u8,
        ) bool {
            if (node >= tags.len) return false;
            switch (tags[node]) {
                .identifier => return tokenIsNamed(tree, main_tokens[node], name),
                .field_access => {
                    const pair = datas[node].node_and_token;
                    return expressionNames(tree, tags, datas, main_tokens, @intFromEnum(pair[0]), name);
                },
                .array_access => {
                    const pair = datas[node].node_and_node;
                    return expressionNames(tree, tags, datas, main_tokens, @intFromEnum(pair[0]), name) or
                        expressionNames(tree, tags, datas, main_tokens, @intFromEnum(pair[1]), name);
                },
                .deref, .address_of, .@"try", .optional_type => return expressionNames(
                    tree,
                    tags,
                    datas,
                    main_tokens,
                    @intFromEnum(datas[node].node),
                    name,
                ),
                .grouped_expression, .unwrap_optional => return expressionNames(
                    tree,
                    tags,
                    datas,
                    main_tokens,
                    @intFromEnum(datas[node].node_and_token[0]),
                    name,
                ),
                else => return false,
            }
        }

        fn identifierNameAt(tree: *const std.zig.Ast, main_tokens: []const std.zig.Ast.TokenIndex, node: u32) ?[]const u8 {
            if (node >= main_tokens.len) return null;
            const token = main_tokens[node];
            if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return null;
            return import_resolver.normalizeIdentifier(tree.tokenSlice(token));
        }

        fn tokenIsNamed(tree: *const std.zig.Ast, token: std.zig.Ast.TokenIndex, name: []const u8) bool {
            if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return false;
            return std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(token)), name);
        }

        pub fn escapeReturnedVars(self: *_Engine, state: *ProgramState, fn_node: ids.AstNodeId, current_cfg: *const Cfg) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const fn_index = ids.astIndex(fn_node);
            if (fn_index >= tags.len or tags[fn_index] != .fn_decl) return;
            const fn_data = tree.nodes.items(.data)[fn_index];
            const body_node = @intFromEnum(fn_data.node_and_node[1]);
            if (body_node == 0) return;
            try escapeReturnedVarsInNode(self, state, body_node, current_cfg, tree);
        }

        pub fn escapeReturnedVarsInNode(
            self: *_Engine,
            state: *ProgramState,
            node: u32,
            current_cfg: *const Cfg,
            tree: *const std.zig.Ast,
        ) EngineError!void {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (node == 0 or node >= tags.len) return;

            switch (tags[node]) {
                .@"return" => {
                    if (datas[node].opt_node.unwrap()) |ret_expr| {
                        try markEscapedAtReturn(self, state, @intFromEnum(ret_expr), current_cfg);
                    }
                },
                .block, .block_semicolon, .block_two, .block_two_semicolon => {
                    var statements: []const u32 = &.{};
                    var scratch_buf: [2]u32 = undefined;

                    switch (tags[node]) {
                        .block, .block_semicolon => {
                            const extra_range = datas[node].extra_range;
                            const start = @intFromEnum(extra_range.start);
                            const end = @intFromEnum(extra_range.end);
                            statements = tree.extra_data[start..end];
                        },
                        .block_two, .block_two_semicolon => {
                            const opt_nodes = datas[node].opt_node_and_opt_node;
                            var count: usize = 0;
                            if (opt_nodes[0].unwrap()) |n| {
                                scratch_buf[count] = @intFromEnum(n);
                                count += 1;
                            }
                            if (opt_nodes[1].unwrap()) |n| {
                                scratch_buf[count] = @intFromEnum(n);
                                count += 1;
                            }
                            statements = scratch_buf[0..count];
                        },
                        else => {},
                    }

                    for (statements) |stmt| {
                        try escapeReturnedVarsInNode(self, state, stmt, current_cfg, tree);
                    }
                },
                .@"if", .if_simple => {
                    const full_if = tree.fullIf(@enumFromInt(node)) orelse return;
                    try escapeReturnedVarsInNode(self, state, @intFromEnum(full_if.ast.then_expr), current_cfg, tree);
                    if (full_if.ast.else_expr.unwrap()) |else_node| {
                        try escapeReturnedVarsInNode(self, state, @intFromEnum(else_node), current_cfg, tree);
                    }
                },
                .@"while", .while_simple, .while_cont => {
                    const full_while = tree.fullWhile(@enumFromInt(node)) orelse return;
                    try escapeReturnedVarsInNode(self, state, @intFromEnum(full_while.ast.then_expr), current_cfg, tree);
                    if (full_while.ast.else_expr.unwrap()) |else_node| {
                        try escapeReturnedVarsInNode(self, state, @intFromEnum(else_node), current_cfg, tree);
                    }
                    if (full_while.ast.cont_expr.unwrap()) |cont_node| {
                        try escapeReturnedVarsInNode(self, state, @intFromEnum(cont_node), current_cfg, tree);
                    }
                },
                .@"for", .for_simple => {
                    const full_for = tree.fullFor(@enumFromInt(node)) orelse return;
                    try escapeReturnedVarsInNode(self, state, @intFromEnum(full_for.ast.then_expr), current_cfg, tree);
                    if (full_for.ast.else_expr.unwrap()) |else_node| {
                        try escapeReturnedVarsInNode(self, state, @intFromEnum(else_node), current_cfg, tree);
                    }
                },
                .@"switch", .switch_comma => {
                    const full_switch = tree.switchFull(@enumFromInt(node));
                    for (full_switch.ast.cases) |case_node| {
                        const full_case = tree.fullSwitchCase(case_node) orelse continue;
                        try escapeReturnedVarsInNode(self, state, @intFromEnum(full_case.ast.target_expr), current_cfg, tree);
                    }
                },
                else => {},
            }
        }
    };
}

const TestEngine = @import("engine.zig").AnalysisEngine;
const TestCfgBuilder = @import("../../cfg.zig").CfgBuilder;
const TestTypeContext = @import("../../type_context.zig").TypeContext;

/// What one run of the first function `code` declares left reported, with the
/// region the source bound `binding` to read out of the source itself.
const AggregateStoreRun = struct {
    /// How many distinct states the function's exit node was reached in.
    exit_states: usize,
    /// Region the source bound `binding` to.
    bound_region: ids.VarId,
    /// Every region a `resource_leak` names anywhere in the graph. A violation
    /// recorded on one node rides along in the states after it, so the answer
    /// is the set of regions named rather than the number of states carrying
    /// them.
    leaked: std.AutoHashMap(ids.VarId, void),

    fn deinit(self: *AggregateStoreRun) void {
        self.leaked.deinit();
    }
};

/// Analyses the first function `code` declares and reads back what it left
/// reported as a leak.
///
/// Nothing here answers "there was nothing to look at": a snippet that does
/// not parse, declares no such function, binds no such name or builds no
/// control flow fails the test instead of passing quietly.
fn runAggregateStore(
    allocator: std.mem.Allocator,
    code: [:0]const u8,
    binding: []const u8,
) !AggregateStoreRun {
    var source = Source.init(allocator, "aggregate-store.zig", code);
    defer source.deinit();
    // The engine reads a binding's declared type to recognize that an arena's
    // own `deinit` releases what was allocated through it, and the analyzer
    // hands it that context for every file it runs. Without those facts an
    // allocation is still charged to the arena - `arena_provenance` proves
    // that from the constructor it was written with - while the arena's own
    // release stays invisible, so a block the arena settles reads as lost.
    var type_context = TestTypeContext.init(allocator, &source);
    defer type_context.deinit();
    const tree = try source.ast();
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);

    var fn_node: ?ids.AstNodeId = null;
    var bound: ?ids.VarId = null;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        // The declarations are nested under the function they belong to, so
        // the scan has to pass the function node on its way to them.
        if (tag == .fn_decl and fn_node == null) fn_node = ids.astId(@intCast(index));
        if (!import_resolver.isVarDeclTag(tag)) continue;
        const full = tree.fullVarDecl(@enumFromInt(index)) orelse continue;
        const name_token = full.ast.mut_token + 1;
        if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) continue;
        if (std.mem.eql(u8, tree.tokenSlice(name_token), binding)) bound = ids.varId(name_token);
    }
    const fn_idx = fn_node orelse return error.NoFunctionToAnalyse;

    var builder = TestCfgBuilder.init(allocator);
    var cfg = (try builder.buildFromFn(&source, fn_idx)) orelse return error.NoControlFlowToAnalyse;
    defer cfg.deinit();
    var engine = TestEngine.initWithSource(allocator, &cfg, &source);
    defer engine.deinit();
    engine.setTypeContext(&type_context);
    try engine.run();

    var run = AggregateStoreRun{
        .exit_states = 0,
        .bound_region = bound orelse return error.NoBindingToAnalyse,
        .leaked = .init(allocator),
    };
    errdefer run.deinit();
    for (engine.getGraph().nodes.items) |node| {
        for (node.state.getStoreViolations()) |violation| {
            if (violation.kind != .resource_leak) continue;
            try run.leaked.put(violation.region, {});
        }
        if (node.point.kind != .post) continue;
        const cfg_node = cfg.getNode(node.point.node_index) orelse continue;
        if (cfg_node.ir_node.tag != .fn_exit) continue;
        run.exit_states += 1;
    }
    return run;
}

test "a whole-aggregate replacement reports the loss once, against the aggregate" {
    // The store put the payload in the aggregate, so the aggregate's own block
    // is the acquisition that is lost and the replacement is what reports it.
    // The payload rode into that block, so it is the same lost write seen from
    // the element it went into, not a second claim on it.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const ResourceModel = struct {
        \\    kind: u8,
        \\    method_name: ?[]const u8 = null,
        \\};
        \\fn wholeOverwrite(allocator: std.mem.Allocator) ![]ResourceModel {
        \\    var models = try allocator.alloc(ResourceModel, 2);
        \\    var slot: usize = 0;
        \\    var model = ResourceModel{ .kind = 0 };
        \\    model.method_name = try allocator.dupe(u8, "method");
        \\    models[slot] = model;
        \\    models = try allocator.alloc(ResourceModel, 2);
        \\    return models;
        \\}
    ;

    var run = try runAggregateStore(std.testing.allocator, code, "models");
    defer run.deinit();
    try std.testing.expect(run.exit_states >= 1);
    try std.testing.expectEqual(@as(usize, 1), run.leaked.count());
    try std.testing.expect(run.leaked.contains(run.bound_region));
}

test "a whole-aggregate replacement an owner outlives leaves nothing behind" {
    // Same stores, allocated through an arena this frame disposes of. The
    // replacement hands the old aggregate to that owner rather than dropping
    // it, and the arena releases both it and the payload that rode in, so
    // nothing is lost and nothing is reported - not the aggregate, and not the
    // payload the store put in it either.
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const ResourceModel = struct {
        \\    kind: u8,
        \\    method_name: ?[]const u8 = null,
        \\};
        \\fn wholeOverwriteOwned(allocator: std.mem.Allocator) ![]ResourceModel {
        \\    var arena: std.heap.ArenaAllocator = std.heap.ArenaAllocator.init(allocator);
        \\    defer arena.deinit();
        \\    const arena_allocator = arena.allocator();
        \\    var models = try arena_allocator.alloc(ResourceModel, 2);
        \\    var slot: usize = 0;
        \\    var model = ResourceModel{ .kind = 0 };
        \\    model.method_name = try arena_allocator.dupe(u8, "method");
        \\    models[slot] = model;
        \\    models = try arena_allocator.alloc(ResourceModel, 2);
        \\    return models;
        \\}
    ;

    var run = try runAggregateStore(std.testing.allocator, code, "models");
    defer run.deinit();
    try std.testing.expect(run.exit_states >= 1);
    try std.testing.expectEqual(@as(usize, 0), run.leaked.count());
}
