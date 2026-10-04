const std = @import("std");
const ids = @import("../../ids.zig");
const ast_walk = @import("../../ast_walk.zig");
const allocator_utils = @import("../../analysis/allocator_utils.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
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
                else => {},
            }
        }

        pub fn markEscapedInExpr(self: *_Engine, state: *ProgramState, expr_node: u32, current_cfg: *const Cfg) EngineError!void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const main_tokens = tree.nodes.items(.main_token);
            const token_tags = tree.tokens.items(.tag);

            if (expr_node >= tags.len) return;

            switch (tags[expr_node]) {
                .identifier => {
                    if (_Engine.VarResolution.resolveVarIdFromIdentifier(self, expr_node, current_cfg)) |var_id| {
                        try state.trackEscapeOwned(var_id);
                        state.trackEscape(var_id);
                        const token = main_tokens[expr_node];
                        if (ids.varIndex(var_id) == token and token < token_tags.len and token_tags[token] == .identifier) {
                            const name = tree.tokenSlice(token);
                            try state.trackEscapeByName(tree, name);
                        }
                    }
                },
                .grouped_expression, .unwrap_optional => {
                    const data = datas[expr_node].node_and_token;
                    try markEscapedInExpr(self, state, @intFromEnum(data[0]), current_cfg);
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr_node)) orelse return;
                    try markEscapedInExpr(self, state, @intFromEnum(slice.ast.sliced), current_cfg);
                },
                .array_access => {
                    const pair = datas[expr_node].node_and_node;
                    try markEscapedInExpr(self, state, @intFromEnum(pair[0]), current_cfg);
                },
                .field_access => {
                    const data = datas[expr_node].node_and_token;
                    try markEscapedInExpr(self, state, @intFromEnum(data[0]), current_cfg);
                },
                .address_of, .deref, .@"try" => {
                    const child = datas[expr_node].node;
                    try markEscapedInExpr(self, state, @intFromEnum(child), current_cfg);
                },
                .@"catch" => {
                    const pair = datas[expr_node].node_and_node;
                    try markEscapedInExpr(self, state, @intFromEnum(pair[0]), current_cfg);
                    try markEscapedInExpr(self, state, @intFromEnum(pair[1]), current_cfg);
                },
                .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const struct_init = tree.fullStructInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (struct_init.ast.fields) |field| {
                        try markEscapedInExpr(self, state, @intFromEnum(field), current_cfg);
                    }
                },
                .container_field, .container_field_init, .container_field_align => {
                    const field = tree.fullContainerField(@enumFromInt(expr_node)) orelse return;
                    if (field.ast.value_expr.unwrap()) |value_expr| {
                        try markEscapedInExpr(self, state, @intFromEnum(value_expr), current_cfg);
                    } else if (field.ast.tuple_like) {
                        if (field.ast.type_expr.unwrap()) |value_expr| {
                            try markEscapedInExpr(self, state, @intFromEnum(value_expr), current_cfg);
                        }
                    }
                },
                .array_init, .array_init_comma, .array_init_one, .array_init_one_comma, .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const array_init = tree.fullArrayInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (array_init.ast.elements) |elem| {
                        try markEscapedInExpr(self, state, @intFromEnum(elem), current_cfg);
                    }
                },
                else => {},
            }
        }

        pub fn trackEscapesFromCall(self: *_Engine, state: *ProgramState, call_node: u32, current_cfg: *const Cfg) void {
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
                        checkDeferFreesEscapeeIntoContainer(self, state, call_node, receiver_node, item_node, current_cfg) catch return;
                    }
                }
                markEscapedInExpr(self, state, item_node, current_cfg) catch return;
                return;
            }

            if (std.mem.eql(u8, fn_name, "put") or
                std.mem.eql(u8, fn_name, "putNoClobber") or
                std.mem.eql(u8, fn_name, "putAssumeCapacity") or
                std.mem.eql(u8, fn_name, "putNoClobberAssumeCapacity"))
            {
                if (full_call.ast.params.len >= 1) {
                    const key_node = @intFromEnum(full_call.ast.params[0]);
                    markEscapedInExpr(self, state, key_node, current_cfg) catch return;
                }
                if (full_call.ast.params.len >= 2) {
                    const value_node = @intFromEnum(full_call.ast.params[1]);
                    markEscapedInExpr(self, state, value_node, current_cfg) catch return;
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
                    markEscapedInExpr(self, state, param_node, current_cfg) catch return;
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

        pub fn trackEscapesInExpr(self: *_Engine, state: *ProgramState, expr_node: u32, current_cfg: *const Cfg) void {
            const src = self.source orelse return;
            const tree = src.ast() catch return;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (expr_node >= tags.len) return;

            switch (tags[expr_node]) {
                .call, .call_comma, .call_one, .call_one_comma => {
                    trackEscapesFromCall(self, state, expr_node, current_cfg);
                },
                .grouped_expression, .unwrap_optional => {
                    const data = datas[expr_node].node_and_token;
                    trackEscapesInExpr(self, state, @intFromEnum(data[0]), current_cfg);
                },
                .slice, .slice_open, .slice_sentinel => {
                    const slice = tree.fullSlice(@enumFromInt(expr_node)) orelse return;
                    trackEscapesInExpr(self, state, @intFromEnum(slice.ast.sliced), current_cfg);
                },
                .array_access => {
                    const pair = datas[expr_node].node_and_node;
                    trackEscapesInExpr(self, state, @intFromEnum(pair[0]), current_cfg);
                },
                .field_access => {
                    const data = datas[expr_node].node_and_token;
                    trackEscapesInExpr(self, state, @intFromEnum(data[0]), current_cfg);
                },
                .address_of, .deref, .@"try" => {
                    const child = datas[expr_node].node;
                    trackEscapesInExpr(self, state, @intFromEnum(child), current_cfg);
                },
                .@"catch" => {
                    const pair = datas[expr_node].node_and_node;
                    trackEscapesInExpr(self, state, @intFromEnum(pair[0]), current_cfg);
                    trackEscapesInExpr(self, state, @intFromEnum(pair[1]), current_cfg);
                },
                .struct_init, .struct_init_comma, .struct_init_one, .struct_init_one_comma, .struct_init_dot, .struct_init_dot_comma, .struct_init_dot_two, .struct_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const struct_init = tree.fullStructInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (struct_init.ast.fields) |field| {
                        trackEscapesInExpr(self, state, @intFromEnum(field), current_cfg);
                    }
                },
                .array_init, .array_init_comma, .array_init_one, .array_init_one_comma, .array_init_dot, .array_init_dot_comma, .array_init_dot_two, .array_init_dot_two_comma => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const array_init = tree.fullArrayInit(&buf, @enumFromInt(expr_node)) orelse return;
                    for (array_init.ast.elements) |elem| {
                        trackEscapesInExpr(self, state, @intFromEnum(elem), current_cfg);
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
            if (index_node >= tags.len or tags[index_node] != .identifier) return true;

            const aggregate = _Engine.VarResolution.resolveVarIdFromExpr(self, base_node, current_cfg) orelse return false;
            // An unproven store is a decided store: the payload keeps what it
            // owns, so the resources it drops here are still reported.
            if (!storeKeepsPayloadReachable(self, tree, current_cfg, base_node, index_node, lhs_node)) return true;

            state.adoptOwnedResources(payload, aggregate);
            return true;
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
            var buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buf, @enumFromInt(call_node)) orelse return false;
            if (expressionNames(tree, tags, datas, main_tokens, @intFromEnum(call.ast.fn_expr), name)) return true;
            // Releasing the aggregate is not aliasing it, so a proven
            // allocator release is the one call shape allowed through.
            const release = isAllocatorReleaseCall(self, tree, call);
            for (call.ast.params) |param| {
                const param_node: u32 = @intFromEnum(param);
                if (!expressionNames(tree, tags, datas, main_tokens, param_node, name)) continue;
                if (release) continue;
                return true;
            }
            return false;
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
                        try markEscapedInExpr(self, state, @intFromEnum(ret_expr), current_cfg);
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
