const std = @import("std");
const call_utils = @import("../../analysis/call_utils.zig");
const allocator_utils = @import("../../analysis/allocator_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");

pub fn Mixin(comptime _Engine: type) type {
    return struct {
        const ResourceCallKind = enum {
            alloc,
            free,
            free_owned,
            open,
            close,
        };

        const ResourceCall = struct {
            kind: ResourceCallKind,
            target_expr: ?u32,
            call_node: u32,
        };

        pub fn resolveResourceCall(self: *_Engine, expr_node: u32) ?ResourceCall {
            const src = self.source orelse return null;
            const tree = src.ast() catch return null;
            return resolveResourceCallFromExpr(self, tree, expr_node);
        }

        pub fn isDefinitelyNonAlloc(self: *_Engine, expr_node: u32) bool {
            const src = self.source orelse return false;
            const tree = src.ast() catch return false;
            return isDefinitelyNonAllocExpr(self, tree, expr_node);
        }

        pub fn resolveResourceCallFromExpr(self: *_Engine, tree: *const std.zig.Ast, expr_node: u32) ?ResourceCall {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (expr_node >= tags.len) return null;
            const tag = tags[expr_node];

            return switch (tag) {
                .call, .call_comma, .call_one, .call_one_comma => resolveResourceCallFromCall(self, tree, expr_node),
                .@"try" => resolveResourceCallFromExpr(self, tree, @intFromEnum(datas[expr_node].node)),
                .@"catch" => blk: {
                    const pair = datas[expr_node].node_and_node;
                    if (resolveResourceCallFromExpr(self, tree, @intFromEnum(pair[0]))) |call_info| {
                        break :blk call_info;
                    }
                    break :blk resolveResourceCallFromExpr(self, tree, @intFromEnum(pair[1]));
                },
                .unwrap_optional, .grouped_expression => resolveResourceCallFromExpr(self, tree, @intFromEnum(datas[expr_node].node_and_token[0])),
                .slice, .slice_open, .slice_sentinel => blk: {
                    const slice = tree.fullSlice(@enumFromInt(expr_node)) orelse break :blk null;
                    break :blk resolveResourceCallFromExpr(self, tree, @intFromEnum(slice.ast.sliced));
                },
                else => null,
            };
        }

        pub fn resolveResourceCallFromCall(self: *_Engine, tree: *const std.zig.Ast, call_ast_node: u32) ?ResourceCall {
            const tags = tree.nodes.items(.tag);

            if (call_ast_node >= tags.len) return null;
            const call_info = call_utils.resolveCall(tree, self.type_context, call_ast_node, &self.fqn_buffer) orelse return null;

            const first_arg: ?u32 = if (call_info.param_count > 0)
                call_utils.callParam(tree, call_ast_node, 0)
            else
                null;

            // Priority 1: Config-driven resource models
            if (self.config) |config| {
                // Get return type info if available
                var return_type_str: ?[]const u8 = null;
                if (self.type_context) |type_ctx| {
                    if (type_ctx.getExpressionType(call_ast_node)) |ti| {
                        return_type_str = ti.type_str;
                    }
                }

                // Match against config resource models
                if (config.matchResourceModel(call_info.method_name, call_info.receiver_type, return_type_str, call_info.fqn)) |model_kind| {
                    const kind: ResourceCallKind = switch (model_kind) {
                        .alloc => .alloc,
                        .free => .free,
                        .free_owned => .free_owned,
                        .open => .open,
                        .close => .close,
                    };
                    const target_expr: ?u32 = switch (kind) {
                        .free, .close => if (first_arg) |arg| arg else call_info.base_node,
                        .free_owned => if (call_info.base_node) |base| base else first_arg,
                        else => null,
                    };
                    return .{ .kind = kind, .target_expr = target_expr, .call_node = call_ast_node };
                }
            }
            // Priority 2: Built-in heuristics (allocator methods)
            if (call_info.base_node) |base_node| {
                if (allocator_utils.isAllocatorExpr(tree, self.type_context, base_node)) {
                    if (std.mem.eql(u8, call_info.method_name, "alloc") or
                        std.mem.eql(u8, call_info.method_name, "dupe") or
                        std.mem.eql(u8, call_info.method_name, "create"))
                    {
                        return .{ .kind = .alloc, .target_expr = null, .call_node = call_ast_node };
                    }
                    if (std.mem.eql(u8, call_info.method_name, "free") or std.mem.eql(u8, call_info.method_name, "destroy")) {
                        return .{ .kind = .free, .target_expr = first_arg, .call_node = call_ast_node };
                    }
                }
            }

            if (std.mem.eql(u8, call_info.method_name, "allocPrint")) {
                if (first_arg) |arg_node| {
                    if (allocator_utils.isAllocatorExpr(tree, self.type_context, arg_node)) {
                        return .{ .kind = .alloc, .target_expr = null, .call_node = call_ast_node };
                    }
                }
            }

            // Priority 3: Type-based open detection with strict type info.
            const type_status = classifyResourceReturningCall(self, call_ast_node);
            if (type_status == .resource) {
                return .{ .kind = .open, .target_expr = null, .call_node = call_ast_node };
            }

            // Priority 4: Name-based open detection with known base types (only when type info is missing).
            if (type_status == .unknown) {
                if (call_info.base_node) |base_node| {
                    if ((std.mem.eql(u8, call_info.method_name, "open") or
                        std.mem.eql(u8, call_info.method_name, "openFile") or
                        std.mem.eql(u8, call_info.method_name, "openDir") or
                        std.mem.eql(u8, call_info.method_name, "openIterableDir") or
                        std.mem.eql(u8, call_info.method_name, "createFile")) and
                        isKnownOpenBase(self, tree, base_node))
                    {
                        return .{ .kind = .open, .target_expr = null, .call_node = call_ast_node };
                    }
                }
            }

            if (std.mem.eql(u8, call_info.method_name, "close")) {
                if (first_arg == null) {
                    if (call_info.base_node) |base_node| {
                        if (isKnownResourceType(call_info.receiver_type)) {
                            return .{ .kind = .close, .target_expr = base_node, .call_node = call_ast_node };
                        }
                    }
                }
                if (call_info.fqn) |fqn| {
                    if (std.mem.eql(u8, fqn, "std.posix.close")) {
                        if (first_arg) |arg| {
                            return .{ .kind = .close, .target_expr = arg, .call_node = call_ast_node };
                        }
                    }
                }
            }
            return null;
        }

        fn isKnownResourceType(type_name: ?[]const u8) bool {
            var name = type_name orelse return false;
            while (name.len > 0 and (name[0] == '?' or name[0] == '*')) {
                name = name[1..];
            }
            while (std.mem.startsWith(u8, name, "const ")) {
                name = name["const ".len..];
            }
            while (std.mem.startsWith(u8, name, "volatile ")) {
                name = name["volatile ".len..];
            }
            return std.mem.eql(u8, name, "std.fs.File") or
                std.mem.eql(u8, name, "std.posix.fd_t") or
                std.mem.eql(u8, name, "std.fs.Dir") or
                std.mem.eql(u8, name, "std.fs.IterableDir");
        }
        const ResourceReturnStatus = enum {
            unknown,
            resource,
            non_resource,
        };

        /// Classify whether a call returns a known resource type.
        /// Uses strict type information and avoids name-only heuristics.
        pub fn classifyResourceReturningCall(self: *_Engine, call_ast_node: u32) ResourceReturnStatus {
            const type_ctx = self.type_context orelse return .unknown;
            if (type_ctx.getExpressionTypeStrict(call_ast_node)) |strict_info| {
                if (strict_info.type_str) |type_str| {
                    if (std.mem.eql(u8, type_str, "std.fs.File") or
                        std.mem.eql(u8, type_str, "std.posix.fd_t") or
                        std.mem.eql(u8, type_str, "std.fs.Dir") or
                        std.mem.eql(u8, type_str, "std.fs.IterableDir"))
                    {
                        return .resource;
                    }
                    return .non_resource;
                }

                return switch (strict_info.kind) {
                    .int,
                    .uint,
                    .float,
                    .bool_type,
                    .void_type,
                    .error_union,
                    => .non_resource,
                    else => .unknown,
                };
            }

            if (type_ctx.getExpressionType(call_ast_node)) |loose_info| {
                if (loose_info.type_str) |type_str| {
                    if (std.mem.eql(u8, type_str, "std.fs.File") or
                        std.mem.eql(u8, type_str, "std.posix.fd_t") or
                        std.mem.eql(u8, type_str, "std.fs.Dir") or
                        std.mem.eql(u8, type_str, "std.fs.IterableDir"))
                    {
                        return .resource;
                    }
                }
            }

            return .unknown;
        }

        pub fn isKnownOpenBase(self: *_Engine, tree: *const std.zig.Ast, base_node: u32) bool {
            return isKnownOpenBaseDepth(self, tree, base_node, 0);
        }

        fn isKnownOpenBaseDepth(self: *_Engine, tree: *const std.zig.Ast, base_node: u32, depth: u8) bool {
            if (depth >= 16 or base_node >= tree.nodes.len) return false;
            const source = self.source orelse return false;
            const files = [_]import_resolver.File{.{ .path = source.getFilePath(), .tree = tree }};
            const resolver = call_resolver.ProjectTypeResolver{ .files = &files, .file_index = 0 };
            const node: std.zig.Ast.Node.Index = @enumFromInt(base_node);
            switch (tree.nodeTag(node)) {
                .identifier => {
                    const declaration = resolver.resolveDeclarationNode(base_node) orelse return false;
                    const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return false;
                    if (tree.tokenTag(full.ast.mut_token) != .keyword_const) return false;
                    const init = full.ast.init_node.unwrap() orelse return false;
                    return isKnownOpenBaseDepth(self, tree, @intFromEnum(init), depth + 1);
                },
                .field_access => {
                    const access = tree.nodeData(node).node_and_token;
                    const member = tree.tokenSlice(access[1]);
                    if (!std.mem.eql(u8, member, "posix") and !std.mem.eql(u8, member, "fs")) return false;
                    const base = @intFromEnum(access[0]);
                    if (import_resolver.importPathFromBuiltinCall(tree, base)) |path| {
                        return std.mem.eql(u8, path, "std");
                    }
                    return resolver.isVerifiedImportBinding(base, "std");
                },
                else => return false,
            }
        }

        pub fn isDefinitelyNonAllocExpr(self: *_Engine, tree: *const std.zig.Ast, expr_node: u32) bool {
            if (resolveResourceCallFromExpr(self, tree, expr_node)) |call_info| {
                return call_info.kind != .alloc and call_info.kind != .open;
            }

            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);

            if (expr_node >= tags.len) return false;
            return switch (tags[expr_node]) {
                .slice,
                .slice_open,
                .slice_sentinel,
                .address_of,
                .array_mult,
                .array_cat,
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
                => true,
                .grouped_expression, .unwrap_optional => blk: {
                    const data = datas[expr_node].node_and_token;
                    break :blk isDefinitelyNonAllocExpr(self, tree, @intFromEnum(data[0]));
                },
                .@"try" => isDefinitelyNonAllocExpr(self, tree, @intFromEnum(datas[expr_node].node)),
                .@"catch" => blk: {
                    const pair = datas[expr_node].node_and_node;
                    const left = isDefinitelyNonAllocExpr(self, tree, @intFromEnum(pair[0]));
                    const right = isDefinitelyNonAllocExpr(self, tree, @intFromEnum(pair[1]));
                    break :blk left and right;
                },
                else => false,
            };
        }
    };
}
