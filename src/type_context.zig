const std = @import("std");
const ast_walk = @import("ast_walk.zig");
const Source = @import("source.zig").Source;
const zir_bridge_mod = @import("zir_bridge.zig");
const call_resolver = @import("analysis/call_resolver.zig");
const import_resolver = @import("analysis/import_resolver.zig");

pub const TypeInfo = zir_bridge_mod.TypeInfo;
pub const DeclInfo = zir_bridge_mod.DeclInfo;
pub const ZirBridge = zir_bridge_mod.ZirBridge;

/// TypeContext provides a unified interface for type information queries.
/// It wraps ZirBridge and provides convenient methods for checkers and rules
/// to query type information during analysis.
///
/// The context supports:
/// - Declaration type lookups by name
/// - AST node to type mappings
/// - Type kind queries (is this an error union? optional? pointer?)
/// - Project AST identity for imported declarations and payload types
pub const TypeContext = struct {
    allocator: std.mem.Allocator,
    source: *Source,
    project_resolver: ?call_resolver.ProjectTypeResolver = null,

    /// Cache for frequently queried types by AST node index.
    /// This avoids repeated ZIR lookups for the same nodes.
    node_type_cache: std.AutoHashMap(u32, TypeInfo),
    /// Strict results never share heuristic types or CFG-provided hints.
    strict_type_cache: std.AutoHashMap(u32, ?TypeInfo),
    resolution_failed: bool = false,

    /// AST nodes currently being resolved. Guards the
    /// identifier -> declaration -> initializer -> identifier cycle
    /// (e.g. a switch target whose case values name a local whose
    /// initializer is that same switch).
    resolving: std.AutoHashMap(u32, void),

    pub fn init(allocator: std.mem.Allocator, source: *Source) TypeContext {
        return .{
            .allocator = allocator,
            .source = source,
            .node_type_cache = std.AutoHashMap(u32, TypeInfo).init(allocator),
            .strict_type_cache = std.AutoHashMap(u32, ?TypeInfo).init(allocator),
            .resolving = std.AutoHashMap(u32, void).init(allocator),
        };
    }

    pub fn deinit(self: *TypeContext) void {
        self.node_type_cache.deinit();
        self.strict_type_cache.deinit();
        self.resolving.deinit();
    }

    // =========================================================================
    // Core Type Query API
    // =========================================================================

    /// Require type information while preserving frontend and allocation errors.
    pub fn ensureAvailable(self: *TypeContext) zir_bridge_mod.ZirBridgeError!void {
        _ = try self.source.requireZirBridge();
    }

    /// Check if type information is available.
    pub fn isAvailable(self: *TypeContext) bool {
        return self.source.hasTypeInfo();
    }

    /// Get the ZirBridge if available.
    pub fn getZirBridge(self: *TypeContext) ?*const ZirBridge {
        return self.source.zirBridge();
    }

    // =========================================================================
    // Declaration Queries
    // =========================================================================

    /// Find type information for a declaration by name.
    pub fn getDeclType(self: *TypeContext, name: []const u8) ?TypeInfo {
        return self.source.findDeclType(name);
    }

    /// Find full declaration information by name.
    pub fn getDecl(self: *TypeContext, name: []const u8) ?DeclInfo {
        return self.source.findDecl(name);
    }

    /// Check if a declaration exists.
    pub fn hasDecl(self: *TypeContext, name: []const u8) bool {
        return self.source.findDecl(name) != null;
    }

    /// Check if a declaration is a function.
    pub fn isDeclFunction(self: *TypeContext, name: []const u8) bool {
        return self.source.isDeclFunction(name);
    }

    /// Check if a declaration is a type (struct, enum, union, type).
    pub fn isDeclType(self: *TypeContext, name: []const u8) bool {
        return self.source.isDeclType(name);
    }

    /// Check if a declaration is public.
    pub fn isDeclPublic(self: *TypeContext, name: []const u8) bool {
        return self.source.isDeclPublic(name);
    }

    /// Check if a declaration is a constant.
    pub fn isDeclConst(self: *TypeContext, name: []const u8) bool {
        return self.source.isDeclConst(name);
    }

    /// Get all declarations.
    pub fn getAllDecls(self: *TypeContext, result: *std.ArrayList(DeclInfo)) !void {
        const count = self.source.getDeclCount();
        for (0..count) |i| {
            if (self.source.getDecl(i)) |decl| {
                try result.append(self.allocator, decl);
            }
        }
    }

    // =========================================================================
    // AST Node Type Queries
    // =========================================================================

    /// Get type information for an AST node by index.
    /// Uses caching to avoid repeated lookups.
    pub fn getNodeType(self: *TypeContext, ast_node: u32) ?TypeInfo {
        // Check cache first
        if (self.node_type_cache.get(ast_node)) |cached| {
            return cached;
        }

        // Try to find type from ZirBridge
        const bridge = self.source.zirBridge() orelse return null;

        // Search declarations for matching AST node
        const count = bridge.getDeclCount();
        for (0..count) |i| {
            if (bridge.getDecl(i)) |decl| {
                if (decl.ast_node == ast_node) {
                    // Cache and return
                    self.node_type_cache.put(ast_node, decl.type_info) catch |err| {
                        std.debug.assert(err == error.OutOfMemory);
                    };
                    return decl.type_info;
                }
            }
        }

        return null;
    }

    /// Get type information for an expression node (call, return, etc.).
    /// This extends getNodeType to handle expression nodes that aren't declarations.
    pub fn getExpressionType(self: *TypeContext, ast_node: u32) ?TypeInfo {
        return self.getExpressionTypeInternal(ast_node, true, true);
    }

    /// Strict expression type query that avoids name-only heuristics.
    /// Use this when the result should only be driven by resolved type information.
    pub fn getExpressionTypeStrict(self: *TypeContext, ast_node: u32) ?TypeInfo {
        // Nested queries can hit a recursion guard and yield incomplete results.
        if (self.resolving.count() != 0) {
            return self.getExpressionTypeInternal(ast_node, false, false);
        }
        if (self.strict_type_cache.get(ast_node)) |cached| return cached;

        self.resolution_failed = false;
        const result = self.getExpressionTypeInternal(ast_node, false, false);
        if (!self.resolution_failed) {
            self.strict_type_cache.put(ast_node, result) catch |err| {
                std.debug.assert(err == error.OutOfMemory);
            };
        }
        return result;
    }

    pub fn isStructExpression(self: *TypeContext, expression: u32) bool {
        var info = self.getExpressionTypeStrict(expression) orelse return false;
        for (0..8) |_| {
            if (info.kind != .pointer) return info.kind == .@"struct";
            info = self.getPayloadType(info);
        }
        return false;
    }

    fn getExpressionTypeInternal(self: *TypeContext, ast_node: u32, use_known_methods: bool, use_cache: bool) ?TypeInfo {
        if (use_cache) {
            if (self.node_type_cache.get(ast_node)) |cached| {
                return cached;
            }
        }
        if (self.resolving.contains(ast_node)) return null;
        self.resolving.put(ast_node, {}) catch {
            self.resolution_failed = true;
            return null;
        };
        defer _ = self.resolving.remove(ast_node);

        const tree = self.source.ast() catch {
            self.resolution_failed = true;
            return null;
        };
        const tags = tree.nodes.items(.tag);

        if (ast_node >= tags.len) return null;

        const type_info: ?TypeInfo = switch (tags[ast_node]) {
            .call, .call_comma, .call_one, .call_one_comma => self.getCallExpressionType(tree, ast_node, use_known_methods, use_cache),
            .@"try" => self.getTryExpressionType(tree, ast_node, use_known_methods, use_cache),
            .@"catch" => self.getCatchExpressionType(tree, ast_node, use_known_methods, use_cache),
            .@"orelse" => self.getOrelseExpressionType(tree, ast_node, use_known_methods, use_cache),
            .@"switch", .switch_comma => self.getSwitchExpressionType(tree, ast_node, use_known_methods, use_cache),
            .error_value => TypeInfo.initErrorUnion(),
            .identifier => self.getIdentifierType(tree, ast_node, use_known_methods, use_cache),
            .array_access => self.getArrayAccessType(tree, ast_node, use_known_methods, use_cache),
            .deref => blk: {
                const operand = @intFromEnum(tree.nodes.items(.data)[ast_node].node);
                const pointer = self.getExpressionTypeInternal(operand, use_known_methods, use_cache) orelse break :blk null;
                if (pointer.kind != .pointer) break :blk null;
                break :blk self.getPayloadType(pointer);
            },
            .address_of => TypeInfo.initPointer(),
            .field_access => self.getFieldAccessType(tree, ast_node, use_known_methods, use_cache),
            .block, .block_semicolon, .block_two, .block_two_semicolon => self.getBlockExpressionType(tree, ast_node, use_known_methods, use_cache),
            else => null,
        };

        if (use_cache) {
            if (type_info) |ti| {
                self.node_type_cache.put(ast_node, ti) catch |err| {
                    std.debug.assert(err == error.OutOfMemory);
                };
                return ti;
            }
        }

        return type_info;
    }

    fn getSwitchExpressionType(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        switch_node: u32,
        use_known_methods: bool,
        use_cache: bool,
    ) ?TypeInfo {
        const full_switch = tree.switchFull(@enumFromInt(switch_node));
        var result: ?TypeInfo = null;

        for (full_switch.ast.cases) |case_node| {
            const full_case = tree.fullSwitchCase(case_node) orelse return null;
            const target = @intFromEnum(full_case.ast.target_expr);
            if (isTerminatingExpression(tree, target)) continue;

            const branch = self.getExpressionTypeInternal(
                target,
                use_known_methods,
                use_cache,
            ) orelse return null;
            if (result) |existing| {
                if (!self.compatibleBranchTypes(existing, branch)) return null;
            } else {
                result = branch;
            }
        }

        return result;
    }

    fn getBlockExpressionType(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        block_node: u32,
        use_known_methods: bool,
        use_cache: bool,
    ) ?TypeInfo {
        var inline_statements: [2]u32 = undefined;
        const statements = ast_walk.getBlockStatements(tree, block_node, &inline_statements) orelse return null;
        var result: ?TypeInfo = null;
        for (statements) |statement| {
            if (isTerminatingExpression(tree, statement)) return null;
            result = self.getExpressionTypeInternal(statement, use_known_methods, use_cache);
        }
        return result;
    }

    fn isTerminatingExpression(tree: *const std.zig.Ast, node: u32) bool {
        if (node >= tree.nodes.len) return false;
        return switch (tree.nodeTag(@enumFromInt(node))) {
            .@"return", .@"break", .@"continue", .unreachable_literal => true,
            else => false,
        };
    }

    fn compatibleBranchTypes(self: *TypeContext, left: TypeInfo, right: TypeInfo) bool {
        if (left.kind == .unknown or right.kind == .unknown) return false;
        if (left.kind != right.kind) return false;

        return switch (left.kind) {
            .int, .uint, .float => left.size_bits == right.size_bits and
                left.is_signed == right.is_signed,
            .bool_type, .void_type => true,
            else => self.sameTypeIdentity(left, right),
        };
    }

    fn sameTypeIdentity(self: *TypeContext, left: TypeInfo, right: TypeInfo) bool {
        if (left.kind == .unknown or right.kind == .unknown) return false;
        if (left.kind != right.kind) return false;
        switch (left.kind) {
            .int, .uint, .float => return left.size_bits == right.size_bits and
                left.is_signed == right.is_signed,
            .bool_type, .void_type => return true,
            else => {},
        }

        const left_ast = left.type_ast orelse return false;
        const right_ast = right.type_ast orelse return false;
        const left_node = left.type_node orelse return false;
        const right_node = right.type_node orelse return false;
        if (left_ast == right_ast and left_node == right_node) return true;

        var left_files: [1]import_resolver.File = undefined;
        var right_files: [1]import_resolver.File = undefined;
        const left_resolver = self.resolverForTree(left_ast, &left_files) orelse return false;
        const right_resolver = self.resolverForTree(right_ast, &right_files) orelse return false;
        const left_resolved = left_resolver.resolveTypeNode(left_node) orelse return false;
        const right_resolved = right_resolver.resolveTypeNode(right_node) orelse return false;
        return call_resolver.resolvedTypesEqual(left_resolved, right_resolved);
    }

    fn catchResultType(self: *TypeContext, success: TypeInfo, fallback: TypeInfo) ?TypeInfo {
        if (self.sameTypeIdentity(success, fallback)) return success;
        if (fallback.kind == .optional and self.sameTypeIdentity(success, self.getPayloadType(fallback))) {
            return fallback;
        }
        return null;
    }

    /// Verified std.Io Future methods have no source type node, so compare their
    /// resolved call contracts instead of trusting a type-name string.
    fn isVerifiedIoFutureExpression(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        node: u32,
        use_known_methods: bool,
        use_cache: bool,
        value_result_only: bool,
    ) bool {
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return false;

        return switch (tags[node]) {
            .grouped_expression => self.isVerifiedIoFutureExpression(
                tree,
                @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                use_known_methods,
                use_cache,
                value_result_only,
            ),
            .call, .call_comma, .call_one, .call_one_comma => self.isVerifiedIoFutureCall(
                tree,
                node,
                use_known_methods,
                use_cache,
                value_result_only,
            ),
            .@"switch", .switch_comma => {
                const full_switch = tree.switchFull(@enumFromInt(node));
                var found_value_case = false;
                for (full_switch.ast.cases) |case_node| {
                    const full_case = tree.fullSwitchCase(case_node) orelse return false;
                    const target = @intFromEnum(full_case.ast.target_expr);
                    if (isTerminatingExpression(tree, target)) continue;
                    found_value_case = true;
                    if (!self.isVerifiedIoFutureExpression(
                        tree,
                        target,
                        use_known_methods,
                        use_cache,
                        value_result_only,
                    )) return false;
                }
                return found_value_case;
            },
            else => false,
        };
    }

    fn isVerifiedIoFutureCall(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        call_node: u32,
        use_known_methods: bool,
        use_cache: bool,
        value_result_only: bool,
    ) bool {
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var call_buf: [1]std.zig.Ast.Node.Index = undefined;
        const full_call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return false;
        const callee = @intFromEnum(full_call.ast.fn_expr);
        if (callee >= tags.len or tags[callee] != .field_access) return false;

        const access = datas[callee].node_and_token;
        const method_name = tree.tokenSlice(access[1]);
        const is_async = std.mem.eql(u8, method_name, "async");
        const is_concurrent = std.mem.eql(u8, method_name, "concurrent");
        if (!is_async and !is_concurrent) return false;
        if (value_result_only and is_concurrent) return false;

        const receiver = @intFromEnum(access[0]);
        const receiver_info = self.getExpressionTypeInternal(
            receiver,
            use_known_methods,
            use_cache,
        ) orelse return false;
        return self.isVerifiedImportedType(receiver_info, "std", "Io");
    }

    fn getOrelseExpressionType(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        node: u32,
        use_known_methods: bool,
        use_cache: bool,
    ) ?TypeInfo {
        const pair = tree.nodes.items(.data)[node].node_and_node;
        const optional = self.getExpressionTypeInternal(@intFromEnum(pair[0]), use_known_methods, use_cache) orelse return null;
        if (optional.kind != .optional) return null;
        const payload = self.getPayloadType(optional);
        const fallback = @intFromEnum(pair[1]);
        switch (tree.nodes.items(.tag)[fallback]) {
            .@"return", .@"break", .@"continue" => return payload,
            else => {},
        }
        const fallback_type = self.getExpressionTypeInternal(fallback, use_known_methods, use_cache) orelse return null;
        if (fallback_type.kind == .optional and
            self.sameTypeIdentity(payload, self.getPayloadType(fallback_type)))
            return optional;
        if (self.sameTypeIdentity(fallback_type, payload)) return payload;
        return null;
    }

    fn getPayloadType(self: *TypeContext, info: TypeInfo) TypeInfo {
        if (info.payload_node) |node| {
            const tree = info.type_ast orelse (self.source.ast() catch return TypeInfo.initUnknown());
            if (self.getTypeFromTree(tree, node, 0)) |payload| return payload;
        }
        var payload = info;
        payload.kind = info.payload_kind orelse .unknown;
        payload.payload_kind = null;
        payload.type_node = null;
        payload.payload_node = null;
        return payload;
    }

    fn getArrayAccessType(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        node: u32,
        use_known_methods: bool,
        use_cache: bool,
    ) ?TypeInfo {
        const base = @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]);
        const container = self.getExpressionTypeInternal(base, use_known_methods, use_cache) orelse return null;
        if (container.kind != .slice and container.kind != .array) return null;
        return self.getPayloadType(container);
    }

    /// Get the return type of a call expression.
    fn getCallExpressionType(self: *TypeContext, tree: *const std.zig.Ast, call_node: u32, use_known_methods: bool, use_cache: bool) ?TypeInfo {
        const tags = tree.nodes.items(.tag);

        // Get the callee (function being called)
        var call_buf: [1]std.zig.Ast.Node.Index = undefined;
        const full_call = switch (tags[call_node]) {
            .call, .call_comma, .call_one, .call_one_comma => tree.fullCall(&call_buf, @enumFromInt(call_node)),
            else => return null,
        } orelse return null;

        const callee_node: u32 = @intFromEnum(full_call.ast.fn_expr);
        if (callee_node >= tags.len) return null;

        // Resolve the callable declaration before any name-based fallback.
        // This keeps local shadows and same-spelled methods distinct.
        if (self.getResolvedCallReturnType(tree, call_node)) |info| return info;

        // If the callee is a field access (method call), use verified
        // standard-library knowledge or current-file method declarations.
        if (tags[callee_node] == .field_access) {
            return self.getMethodReturnType(tree, callee_node, use_known_methods, use_cache);
        }

        return null;
    }

    fn getResolvedCallReturnType(self: *TypeContext, tree: *const std.zig.Ast, call_node: u32) ?TypeInfo {
        var files: [1]import_resolver.File = undefined;
        const resolver = self.resolverForTree(tree, &files) orelse return null;
        const resolved = resolver.resolveCallReturnTypeNode(call_node) orelse return null;
        return self.resolvedReturnInfo(resolver, resolved);
    }

    fn resolvedReturnInfo(self: *TypeContext, resolver: call_resolver.ProjectTypeResolver, resolved: call_resolver.ResolvedTypeNode) ?TypeInfo {
        const tree = resolver.files[resolved.file_index].tree;
        var info = self.getTypeFromTree(tree, resolved.node_index, 0) orelse return null;
        if (resolved.inferred_error_union) {
            info.payload_kind = info.kind;
            info.payload_node = info.type_node;
            info.kind = .error_union;
        }
        return info;
    }

    /// Resolve the receiver's method contract before optional compatibility hints.
    fn getMethodReturnType(self: *TypeContext, tree: *const std.zig.Ast, field_node: u32, use_known_methods: bool, use_cache: bool) ?TypeInfo {
        const datas = tree.nodes.items(.data);
        const token_tags = tree.tokens.items(.tag);
        const token_starts = tree.tokens.items(.start);
        const source = self.source.getContent();

        const field_token = datas[field_node].node_and_token[1];
        if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return null;

        const method_name = extractIdentifier(source, token_starts[field_token]);
        if (self.getResolvedMethodReturnType(tree, field_node, method_name, use_known_methods, use_cache)) |info| return info;
        if (!use_known_methods) return null;

        if (use_known_methods) {
            // First check hardcoded known methods, then fall back to function lookup
            if (self.getKnownMethodReturnType(method_name)) |ti| {
                return ti;
            }
        }

        return null;
    }

    fn isVerifiedStandardType(self: *TypeContext, info: TypeInfo) bool {
        const tree = info.type_ast orelse (self.source.ast() catch return false);
        const type_node: u32 = if (info.kind == .pointer)
            info.payload_node orelse return false
        else
            info.type_node orelse return false;
        var node: std.zig.Ast.Node.Index = @enumFromInt(type_node);
        while (tree.nodeTag(node) == .field_access) node = tree.nodeData(node).node_and_token[0];
        var files: [1]import_resolver.File = undefined;
        const resolver = self.resolverForTree(tree, &files) orelse return false;
        return resolver.isVerifiedImportBinding(@intFromEnum(node), "std");
    }

    fn isVerifiedImportedType(
        self: *TypeContext,
        info: TypeInfo,
        import_path: []const u8,
        symbol_path: []const u8,
    ) bool {
        const tree = info.type_ast orelse (self.source.ast() catch return false);
        var type_node = info.type_node orelse return false;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var depth: u32 = 0;
        while (type_node < tags.len and depth < 16) : (depth += 1) {
            switch (tags[type_node]) {
                .grouped_expression => type_node = @intFromEnum(datas[type_node].node_and_token[0]),
                .optional_type => type_node = @intFromEnum(datas[type_node].node),
                .error_union => type_node = @intFromEnum(datas[type_node].node_and_node[1]),
                .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                    const ptr = tree.fullPtrType(@enumFromInt(type_node)) orelse return false;
                    type_node = @intFromEnum(ptr.ast.child_type);
                },
                else => break,
            }
        }

        var components: [16][]const u8 = undefined;
        const path = collectTypePath(tree, type_node, &components) orelse return false;
        return self.followImportedTypeAlias(
            tree,
            path.root_node,
            components[1..path.count],
            import_path,
            symbol_path,
            0,
        );
    }

    fn followImportedTypeAlias(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        alias_node: u32,
        suffix: []const []const u8,
        import_path: []const u8,
        symbol_path: []const u8,
        depth: u32,
    ) bool {
        if (depth >= 16) return false;
        const tags = tree.nodes.items(.tag);
        var files: [1]import_resolver.File = undefined;
        const resolver = self.resolverForTree(tree, &files) orelse return false;
        const declaration = resolver.resolveDeclarationNode(alias_node) orelse return false;
        if (declaration >= tags.len or !import_resolver.isVarDeclTag(tags[declaration])) return false;
        const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return false;
        const init_node = @intFromEnum(full.ast.init_node.unwrap() orelse return false);

        if (import_resolver.importPathFromBuiltinCall(tree, init_node)) |declared_path| {
            return std.mem.eql(u8, declared_path, import_path) and
                typePathMatches(suffix, symbol_path);
        }

        var init_components: [16][]const u8 = undefined;
        const init_path = collectTypePath(tree, init_node, &init_components) orelse return false;
        if (init_path.count == 0) return false;
        const init_suffix = init_components[1..init_path.count];
        var combined: [16][]const u8 = undefined;
        if (init_suffix.len + suffix.len > combined.len) return false;
        @memcpy(combined[0..init_suffix.len], init_suffix);
        @memcpy(combined[init_suffix.len .. init_suffix.len + suffix.len], suffix);
        return self.followImportedTypeAlias(
            tree,
            init_path.root_node,
            combined[0 .. init_suffix.len + suffix.len],
            import_path,
            symbol_path,
            depth + 1,
        );
    }

    const TypePath = struct {
        root_node: u32,
        count: usize,
    };

    fn collectTypePath(
        tree: *const std.zig.Ast,
        node: u32,
        components: *[16][]const u8,
    ) ?TypePath {
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        const main_tokens = tree.nodes.items(.main_token);
        var reverse: [16][]const u8 = undefined;
        var count: usize = 0;
        var current = node;
        while (current < tags.len and tags[current] == .field_access) {
            if (count >= reverse.len) return null;
            const field_token = datas[current].node_and_token[1];
            if (field_token >= tree.tokens.len) return null;
            reverse[count] = tree.tokenSlice(field_token);
            count += 1;
            current = @intFromEnum(datas[current].node_and_token[0]);
        }
        if (current >= tags.len or tags[current] != .identifier or current >= main_tokens.len) return null;
        if (count >= reverse.len) return null;
        reverse[count] = tree.tokenSlice(main_tokens[current]);
        count += 1;
        for (0..count) |index| components[index] = reverse[count - index - 1];
        return .{ .root_node = current, .count = count };
    }

    fn typePathMatches(parts: []const []const u8, expected: []const u8) bool {
        var iterator = std.mem.splitScalar(u8, expected, '.');
        var index: usize = 0;
        while (iterator.next()) |component| {
            if (index >= parts.len or !std.mem.eql(u8, parts[index], component)) return false;
            index += 1;
        }
        return index == parts.len;
    }

    fn getResolvedMethodReturnType(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        field_node: u32,
        method_name: []const u8,
        use_known_methods: bool,
        use_cache: bool,
    ) ?TypeInfo {
        const base = @intFromEnum(tree.nodes.items(.data)[field_node].node_and_token[0]);
        const info = self.getExpressionTypeInternal(base, use_known_methods, use_cache);
        if (info) |base_info| {
            // These imported methods are accepted only through verified type
            // aliases.  A same-spelled local method remains unknown.
            if (self.isVerifiedImportedType(base_info, "std", "Io")) {
                if (std.mem.eql(u8, method_name, "async")) {
                    return .{ .kind = .@"struct", .type_str = "std.Io.Future" };
                }
                if (std.mem.eql(u8, method_name, "concurrent")) {
                    return .{
                        .kind = .error_union,
                        .type_str = "std.Io.Future",
                        .payload_kind = .@"struct",
                    };
                }
            }

            if (self.isVerifiedImportedType(base_info, "std", "mem.Allocator")) {
                if (std.mem.eql(u8, method_name, "create")) return .{ .kind = .error_union, .payload_kind = .pointer };
                if (std.mem.eql(u8, method_name, "alloc") or std.mem.eql(u8, method_name, "dupe") or
                    std.mem.eql(u8, method_name, "dupeZ") or std.mem.eql(u8, method_name, "alignedAlloc") or
                    std.mem.eql(u8, method_name, "allocSentinel"))
                {
                    return .{ .kind = .error_union, .payload_kind = .slice };
                }
            }
        }
        const base_info = info orelse return null;
        const type_tree = base_info.type_ast orelse tree;
        const type_node = base_info.type_node orelse return null;
        var files: [1]import_resolver.File = undefined;
        const resolver = self.resolverForTree(type_tree, &files) orelse return null;
        const owner = resolver.resolveTypeNode(type_node) orelse return null;
        const resolved = resolver.resolveMemberReturnTypeNode(owner, method_name) orelse return null;
        return self.resolvedReturnInfo(resolver, resolved);
    }

    fn getFieldAccessType(self: *TypeContext, tree: *const std.zig.Ast, field_node: u32, use_known_methods: bool, use_cache: bool) ?TypeInfo {
        const access = tree.nodeData(@enumFromInt(field_node)).node_and_token;
        const base = @intFromEnum(access[0]);
        const name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
        var files: [1]import_resolver.File = undefined;
        if (self.resolverForTree(tree, &files)) |resolver| {
            if (resolver.resolveExprType(base)) |owner| {
                if (resolver.resolveFieldTypeNode(owner, name)) |field| {
                    return self.getTypeFromTree(resolver.files[field.file_index].tree, field.node_index, 0);
                }
            }
        }

        const info = self.getExpressionTypeInternal(base, use_known_methods, use_cache) orelse return null;
        const type_tree = info.type_ast orelse tree;
        const type_node = info.type_node orelse return null;
        if (std.mem.eql(u8, name, "items")) {
            if (self.arrayListElementTypeNode(type_tree, type_node)) |element| {
                return .{ .kind = .slice, .payload_node = element, .type_ast = type_tree };
            }
        }
        const resolver = self.resolverForTree(type_tree, &files) orelse return null;
        const owner = resolver.resolveTypeNode(type_node) orelse return null;
        const field = resolver.resolveFieldTypeNode(owner, name) orelse return null;
        return self.getTypeFromTree(resolver.files[field.file_index].tree, field.node_index, 0);
    }

    /// Get return type for known standard library methods.
    fn getKnownMethodReturnType(self: *TypeContext, method_name: []const u8) ?TypeInfo {
        _ = self;

        // File opening methods - return std.fs.File (wrapped in error union)
        if (std.mem.eql(u8, method_name, "openFile") or
            std.mem.eql(u8, method_name, "createFile"))
        {
            return .{ .kind = .error_union, .type_str = "std.fs.File" };
        }

        // Directory opening methods - return std.fs.Dir
        if (std.mem.eql(u8, method_name, "openDir")) {
            return .{ .kind = .error_union, .type_str = "std.fs.Dir" };
        }

        // Iterable directory methods
        if (std.mem.eql(u8, method_name, "openIterableDir")) {
            return .{ .kind = .error_union, .type_str = "std.fs.IterableDir" };
        }

        // Known methods that return error unions without specific type info
        if (std.mem.eql(u8, method_name, "alloc") or
            std.mem.eql(u8, method_name, "dupe") or
            std.mem.eql(u8, method_name, "create") or
            std.mem.eql(u8, method_name, "open") or
            std.mem.eql(u8, method_name, "read") or
            std.mem.eql(u8, method_name, "write") or
            std.mem.eql(u8, method_name, "readAll") or
            std.mem.eql(u8, method_name, "readToEndAlloc"))
        {
            return TypeInfo.initErrorUnion();
        }

        // Known methods that return optionals
        if (std.mem.eql(u8, method_name, "get") or
            std.mem.eql(u8, method_name, "getOrNull") or
            std.mem.eql(u8, method_name, "pop") or
            std.mem.eql(u8, method_name, "popOrNull"))
        {
            return TypeInfo.initOptional();
        }

        return null;
    }

    /// Get the type of a try expression (unwraps error union).
    fn getTryExpressionType(self: *TypeContext, tree: *const std.zig.Ast, try_node: u32, use_known_methods: bool, use_cache: bool) ?TypeInfo {
        const datas = tree.nodes.items(.data);
        const inner_node = @intFromEnum(datas[try_node].node);

        // The inner expression should be an error union
        const inner_type = self.getExpressionTypeInternal(inner_node, use_known_methods, use_cache);
        if (inner_type) |ti| {
            if (ti.kind == .error_union) {
                return self.getPayloadType(ti);
            }
        }
        return inner_type;
    }

    /// Get the type of a catch expression.
    /// Both the successful value and the fallback must have a compatible type.
    fn getCatchExpressionType(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        catch_node: u32,
        use_known_methods: bool,
        use_cache: bool,
    ) ?TypeInfo {
        const pair = tree.nodes.items(.data)[catch_node].node_and_node;
        const success_node = @intFromEnum(pair[0]);
        const left = self.getExpressionTypeInternal(success_node, use_known_methods, use_cache) orelse return null;
        const success = if (left.kind == .error_union) self.getPayloadType(left) else return null;
        const fallback_node = @intFromEnum(pair[1]);
        // Synthetic Future results lack AST type nodes.  This branch proves only
        // their non-null value family, never generic nominal type identity.
        if (success.kind == .@"struct" and
            self.isVerifiedIoFutureExpression(
                tree,
                success_node,
                use_known_methods,
                use_cache,
                false,
            ) and self.isVerifiedIoFutureExpression(
            tree,
            fallback_node,
            use_known_methods,
            use_cache,
            true,
        )) {
            return success;
        }
        if (self.getExpressionTypeInternal(fallback_node, use_known_methods, use_cache)) |fallback| {
            if (self.catchResultType(success, fallback)) |result| return result;
        }
        return null;
    }

    /// Get the type of an identifier by looking up its declaration.
    fn getIdentifierType(self: *TypeContext, tree: *const std.zig.Ast, ident_node: u32, use_known_methods: bool, use_cache: bool) ?TypeInfo {
        const main_tokens = tree.nodes.items(.main_token);
        const token_tags = tree.tokens.items(.tag);

        const ident_token = main_tokens[ident_node];
        if (ident_token >= token_tags.len or token_tags[ident_token] != .identifier) return null;

        const name = tree.tokenSlice(ident_token);

        if (self.getPayloadCaptureType(tree, ident_node, use_known_methods, use_cache)) |ti| {
            return ti;
        }

        if (self.getLocalVarType(tree, ident_node, name, use_known_methods, use_cache)) |ti| {
            return ti;
        }

        if (self.getDeclType(name)) |ti| {
            return ti;
        }

        return null;
    }

    fn getPayloadCaptureType(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        ident_node: u32,
        use_known_methods: bool,
        use_cache: bool,
    ) ?TypeInfo {
        const tags = tree.nodes.items(.tag);
        const main_tokens = tree.nodes.items(.main_token);
        const token_tags = tree.tokens.items(.tag);
        if (ident_node >= main_tokens.len) return null;
        const reference_token = main_tokens[ident_node];
        if (reference_token >= token_tags.len or token_tags[reference_token] != .identifier) return null;
        const name = tree.tokenSlice(reference_token);
        var best_span: usize = std.math.maxInt(usize);
        var result: ?TypeInfo = null;

        for (tags, 0..) |tag, node_index| {
            if (tag != .@"if" and tag != .if_simple) continue;
            const full = tree.fullIf(@enumFromInt(node_index)) orelse continue;
            const payload_token = full.payload_token orelse continue;
            if (payload_token >= token_tags.len or token_tags[payload_token] != .identifier) continue;
            if (!std.mem.eql(u8, tree.tokenSlice(payload_token), name)) continue;
            const then_node = @intFromEnum(full.ast.then_expr);
            const first = tree.firstToken(@enumFromInt(then_node));
            const last = tree.lastToken(@enumFromInt(then_node));
            if (reference_token < first or reference_token > last) continue;
            const condition = @intFromEnum(full.ast.cond_expr);
            const condition_type = self.getExpressionTypeInternal(condition, use_known_methods, use_cache) orelse continue;
            if (condition_type.kind != .optional) continue;
            const span = @as(usize, last) - @as(usize, first);
            if (span >= best_span) continue;
            best_span = span;
            result = self.getPayloadType(condition_type);
        }
        return result;
    }

    fn getParameterType(self: *TypeContext, tree: *const std.zig.Ast, ident_node: u32, name: []const u8) ?TypeInfo {
        const tags = tree.nodes.items(.tag);
        const reference_token = tree.nodes.items(.main_token)[ident_node];
        var best_start: std.zig.Ast.TokenIndex = 0;
        var result: ?TypeInfo = null;

        for (tags, 0..) |tag, node_index| {
            if (tag != .fn_decl) continue;
            const body = tree.nodes.items(.data)[node_index].node_and_node[1];
            const start = tree.firstToken(body);
            if (start > reference_token or start < best_start) continue;
            if (reference_token > tree.lastToken(body)) continue;

            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const proto = tree.fullFnProto(&buffer, @enumFromInt(node_index)) orelse continue;
            var params = proto.iterate(tree);
            while (params.next()) |param| {
                const name_token = param.name_token orelse continue;
                if (!std.mem.eql(u8, tree.tokenSlice(name_token), name)) continue;
                best_start = start;
                result = if (param.type_expr) |type_expr|
                    self.getTypeFromAstNode(@intFromEnum(type_expr)) orelse TypeInfo.initUnknown()
                else
                    TypeInfo.initUnknown();
                break;
            }
        }
        return result;
    }

    /// Resolve a local variable type from its declaration or initializer.
    /// This handles cases like `var pool = MyPool{}` and `const err: anyerror = error.SomeError;`.
    fn getLocalVarType(
        self: *TypeContext,
        tree: *const std.zig.Ast,
        ident_node: u32,
        name: []const u8,
        use_known_methods: bool,
        use_cache: bool,
    ) ?TypeInfo {
        var files: [1]import_resolver.File = undefined;
        const resolver = self.resolverForTree(tree, &files) orelse return null;
        const declaration_node = resolver.resolveDeclarationNode(ident_node) orelse return null;
        const full_decl = tree.fullVarDecl(@enumFromInt(declaration_node)) orelse
            return self.getParameterType(tree, ident_node, name);
        if (full_decl.ast.type_node.unwrap()) |type_node| {
            if (self.getTypeFromAstNode(@intFromEnum(type_node))) |info| return info;
        }
        if (full_decl.ast.init_node.unwrap()) |init_node| {
            if (tree.nodeTag(init_node) == .error_value) return TypeInfo.initErrorUnion();
            if (self.getTypeFromInit(tree, @intFromEnum(init_node), name, use_known_methods, use_cache)) |info| {
                return info;
            }
        }
        return TypeInfo.initUnknown();
    }

    /// Check if an expression type is an error union.
    pub fn isExpressionErrorUnion(self: *TypeContext, ast_node: u32) bool {
        const ti = self.getExpressionType(ast_node) orelse return false;
        return ti.kind == .error_union;
    }

    /// Check if an expression type is an optional.
    pub fn isExpressionOptional(self: *TypeContext, ast_node: u32) bool {
        const ti = self.getExpressionType(ast_node) orelse return false;
        return ti.kind == .optional;
    }

    /// Get the return type of the containing function for a return expression.
    pub fn getContainingFunctionReturnType(self: *TypeContext, fn_ast_node: u32) ?TypeInfo {
        const bridge = self.source.zirBridge() orelse return null;
        return bridge.getFunctionReturnType(fn_ast_node);
    }

    fn extractIdentifier(source: []const u8, start: usize) []const u8 {
        var end = start;
        while (end < source.len and (std.ascii.isAlphanumeric(source[end]) or source[end] == '_')) {
            end += 1;
        }
        return source[start..end];
    }

    pub fn getTypeFromAstNode(self: *TypeContext, ast_node: u32) ?TypeInfo {
        const tree = self.source.ast() catch return null;
        return self.getTypeFromTree(tree, ast_node, 0);
    }

    fn resolverForTree(self: *TypeContext, tree: *const std.zig.Ast, local: *[1]import_resolver.File) ?call_resolver.ProjectTypeResolver {
        if (self.project_resolver) |project| {
            if (project.files[project.file_index].tree == tree) return project;
            for (project.files, 0..) |file, index| {
                if (file.tree == tree) return .{ .files = project.files, .file_index = index };
            }
            return null;
        }
        if (tree != (self.source.ast() catch return null)) return null;
        local.* = .{.{ .path = self.source.file_path, .tree = tree }};
        return .{ .files = local, .file_index = 0 };
    }

    fn getTypeFromTree(self: *TypeContext, tree: *const std.zig.Ast, node: u32, depth: u8) ?TypeInfo {
        if (depth >= 64 or node >= tree.nodes.len) return null;
        const tag = tree.nodeTag(@enumFromInt(node));
        if (tag == .root) return .{ .kind = .@"struct", .type_ast = tree, .type_node = node };
        var info = ZirBridge.extractTypeFromAstNode(tree, node) orelse return null;
        var container_buffer: [2]std.zig.Ast.Node.Index = undefined;
        if (tree.fullContainerDecl(&container_buffer, @enumFromInt(node)) != null) {
            info.kind = switch (tree.tokenTag(tree.nodeMainToken(@enumFromInt(node)))) {
                .keyword_struct => .@"struct",
                .keyword_union => .@"union",
                .keyword_enum => .@"enum",
                else => .unknown,
            };
            return info;
        }
        if (self.arrayListElementTypeNode(tree, node) != null) {
            info.kind = .@"struct";
            return info;
        }
        if (info.kind != .unknown and tag != .field_access) return info;
        var files: [1]import_resolver.File = undefined;
        const resolver = self.resolverForTree(tree, &files) orelse return info;
        if (resolver.resolveTypeAliasNode(node)) |alias| {
            var resolved = self.getTypeFromTree(resolver.files[alias.file_index].tree, alias.node_index, depth + 1) orelse return null;
            if (resolved.type_str == null) resolved.type_str = info.type_str;
            return resolved;
        }
        if (tag == .field_access and !self.isVerifiedStandardType(info)) info.kind = .unknown;
        if (resolver.resolveTypeNode(node)) |resolved| {
            const owner_tree = resolver.files[resolved.file_index].tree;
            return self.getTypeFromTree(owner_tree, resolved.container_node orelse 0, depth + 1);
        }
        return info;
    }

    fn arrayListElementTypeNode(self: *TypeContext, tree: *const std.zig.Ast, type_node: u32) ?u32 {
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&buffer, @enumFromInt(type_node)) orelse return null;
        if (call.ast.params.len != 1 or tree.nodeTag(call.ast.fn_expr) != .field_access) return null;
        const callee = tree.nodeData(call.ast.fn_expr).node_and_token;
        const name = tree.tokenSlice(callee[1]);
        if (!std.mem.eql(u8, name, "ArrayList") and !std.mem.eql(u8, name, "ArrayListUnmanaged")) return null;
        var files: [1]import_resolver.File = undefined;
        const resolver = self.resolverForTree(tree, &files) orelse return null;
        if (!resolver.isVerifiedImportBinding(@intFromEnum(callee[0]), "std")) return null;
        return @intFromEnum(call.ast.params[0]);
    }

    fn getTypeFromInit(self: *TypeContext, tree: *const std.zig.Ast, init_node: u32, decl_name: []const u8, use_known_methods: bool, use_cache: bool) ?TypeInfo {
        const tags = tree.nodes.items(.tag);

        if (init_node >= tags.len) return null;

        switch (tags[init_node]) {
            .struct_init,
            .struct_init_comma,
            .struct_init_one,
            .struct_init_one_comma,
            .struct_init_dot,
            .struct_init_dot_comma,
            .struct_init_dot_two,
            .struct_init_dot_two_comma,
            => {
                var buf: [2]std.zig.Ast.Node.Index = undefined;
                const struct_init = tree.fullStructInit(&buf, @enumFromInt(init_node)) orelse return null;
                if (struct_init.ast.type_expr.unwrap()) |type_node| {
                    if (self.getTypeFromAstNode(@intFromEnum(type_node))) |ti| {
                        if (ti.kind != .unknown or ti.type_str != null) return ti;
                    }
                }
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
                var buf: [2]std.zig.Ast.Node.Index = undefined;
                const array_init = tree.fullArrayInit(&buf, @enumFromInt(init_node)) orelse return null;
                if (array_init.ast.type_expr.unwrap()) |type_node| {
                    if (self.getTypeFromAstNode(@intFromEnum(type_node))) |ti| {
                        if (ti.kind != .unknown or ti.type_str != null) return ti;
                    }
                }
            },
            .identifier => {
                const main_tokens = tree.nodes.items(.main_token);
                const token_tags = tree.tokens.items(.tag);
                const token = main_tokens[init_node];
                if (token < token_tags.len and token_tags[token] == .identifier) {
                    const name = tree.tokenSlice(token);
                    if (std.mem.eql(u8, name, decl_name)) {
                        return null;
                    }
                }
            },
            else => {},
        }

        if (self.getExpressionTypeInternal(init_node, use_known_methods, use_cache)) |ti| {
            if (ti.kind != .unknown or ti.type_str != null) return ti;
        }
        return null;
    }

    /// Cache a type for an AST node (useful when building CFG).
    pub fn cacheNodeType(self: *TypeContext, ast_node: u32, type_info: TypeInfo) void {
        self.node_type_cache.put(ast_node, type_info) catch |err| {
            std.debug.assert(err == error.OutOfMemory);
        };
    }

    // =========================================================================
    // Type Kind Queries (convenience methods)
    // =========================================================================

    /// Check if a declaration has an error union type.
    pub fn isDeclErrorUnion(self: *TypeContext, name: []const u8) bool {
        const ti = self.getDeclType(name) orelse return false;
        return ti.kind == .error_union;
    }

    /// Check if a declaration has an optional type.
    pub fn isDeclOptional(self: *TypeContext, name: []const u8) bool {
        const ti = self.getDeclType(name) orelse return false;
        return ti.kind == .optional;
    }

    /// Check if a declaration has a pointer type.
    pub fn isDeclPointer(self: *TypeContext, name: []const u8) bool {
        const ti = self.getDeclType(name) orelse return false;
        return ti.kind == .pointer;
    }

    /// Check if a declaration has an integer type (signed or unsigned).
    pub fn isDeclInteger(self: *TypeContext, name: []const u8) bool {
        const ti = self.getDeclType(name) orelse return false;
        return ti.kind == .int or ti.kind == .uint;
    }

    /// Check if a declaration has a slice type.
    pub fn isDeclSlice(self: *TypeContext, name: []const u8) bool {
        const ti = self.getDeclType(name) orelse return false;
        return ti.kind == .slice;
    }

    // =========================================================================
    // Identifier Classification (for rules like identifier-style)
    // =========================================================================

    /// Classify an identifier as a type, function, constant, or variable.
    pub const IdentifierKind = enum {
        type_decl, // struct, enum, union, type alias
        function,
        constant,
        variable,
        unknown,
    };

    /// Classify an identifier by name.
    pub fn classifyIdentifier(self: *TypeContext, name: []const u8) IdentifierKind {
        const decl = self.getDecl(name) orelse return .unknown;

        if (decl.is_fn) return .function;

        switch (decl.type_info.kind) {
            .@"struct", .@"enum", .@"union", .type_type => return .type_decl,
            else => {},
        }

        if (decl.is_const) return .constant;
        return .variable;
    }

    /// Check if an identifier should use PascalCase (types).
    pub fn shouldBePascalCase(self: *TypeContext, name: []const u8) bool {
        return self.classifyIdentifier(name) == .type_decl;
    }

    /// Check if an identifier should use camelCase (functions, methods).
    pub fn shouldBeCamelCase(self: *TypeContext, name: []const u8) bool {
        return self.classifyIdentifier(name) == .function;
    }

    /// Check if an identifier should use snake_case (variables, constants).
    pub fn shouldBeSnakeCase(self: *TypeContext, name: []const u8) bool {
        const kind = self.classifyIdentifier(name);
        return kind == .constant or kind == .variable;
    }
};

// ============================================================================
// Tests
// ============================================================================

test "TypeContext basic creation" {
    const allocator = std.testing.allocator;

    const code: [:0]const u8 = "const x: i32 = 42;";
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var ctx = TypeContext.init(allocator, &source);
    defer ctx.deinit();

    try std.testing.expect(ctx.isAvailable());
}

test "TypeContext required availability preserves frontend failure" {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "test.zig", "const x = @zwanzigUnsupportedBuiltin();");
    defer source.deinit();
    var context = TypeContext.init(allocator, &source);
    defer context.deinit();

    try std.testing.expect(!context.isAvailable());
    try std.testing.expectError(error.AstGenFailed, context.ensureAvailable());
}

test "TypeContext getDeclType" {
    const allocator = std.testing.allocator;

    const code: [:0]const u8 = "const x: i32 = 42;";
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var ctx = TypeContext.init(allocator, &source);
    defer ctx.deinit();

    const ti = ctx.getDeclType("x");
    try std.testing.expect(ti != null);
    if (ti) |t| {
        try std.testing.expectEqual(TypeInfo.TypeKind.int, t.kind);
    }
}

test "TypeContext classifyIdentifier" {
    const allocator = std.testing.allocator;

    const code: [:0]const u8 =
        \\pub fn myFunc() void {}
        \\const MY_CONST: i32 = 42;
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var ctx = TypeContext.init(allocator, &source);
    defer ctx.deinit();

    try std.testing.expectEqual(TypeContext.IdentifierKind.function, ctx.classifyIdentifier("myFunc"));
    try std.testing.expectEqual(TypeContext.IdentifierKind.constant, ctx.classifyIdentifier("MY_CONST"));
    try std.testing.expectEqual(TypeContext.IdentifierKind.unknown, ctx.classifyIdentifier("nonexistent"));
}

test "TypeContext caseRecommendations" {
    const allocator = std.testing.allocator;

    const code: [:0]const u8 =
        \\pub fn myFunc() void {}
        \\const MY_CONST: i32 = 42;
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var ctx = TypeContext.init(allocator, &source);
    defer ctx.deinit();

    try std.testing.expect(ctx.shouldBeCamelCase("myFunc"));
    try std.testing.expect(!ctx.shouldBePascalCase("myFunc"));
    try std.testing.expect(ctx.shouldBeSnakeCase("MY_CONST"));
}

test "TypeContext type kind queries" {
    const allocator = std.testing.allocator;

    const code: [:0]const u8 =
        \\const int_val: i32 = 42;
        \\const ptr_val: *i32 = undefined;
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var ctx = TypeContext.init(allocator, &source);
    defer ctx.deinit();

    try std.testing.expect(ctx.isDeclInteger("int_val"));
    try std.testing.expect(!ctx.isDeclPointer("int_val"));
    try std.testing.expect(!ctx.isDeclOptional("int_val"));
}

test "TypeContext getExpressionType for call returning error union" {
    const allocator = std.testing.allocator;

    const code: [:0]const u8 =
        \\fn mayFail() !i32 {
        \\    return 42;
        \\}
        \\fn caller() void {
        \\    const result = mayFail();
        \\    _ = result;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var ctx = TypeContext.init(allocator, &source);
    defer ctx.deinit();

    // Find the call expression in the AST
    const tree = source.ast() catch unreachable;
    const tags = tree.nodes.items(.tag);

    var call_node: ?u32 = null;
    for (0..tags.len) |i| {
        if (tags[i] == .call or tags[i] == .call_one) {
            call_node = @intCast(i);
            break;
        }
    }

    try std.testing.expect(call_node != null);
    if (call_node) |cn| {
        const ti = ctx.getExpressionType(cn);
        try std.testing.expect(ti != null);
        if (ti) |t| {
            try std.testing.expectEqual(TypeInfo.TypeKind.error_union, t.kind);
        }
    }
}

test "TypeContext isExpressionErrorUnion" {
    const allocator = std.testing.allocator;

    const code: [:0]const u8 =
        \\fn mayFail() !void {
        \\    return;
        \\}
        \\fn caller() void {
        \\    const x = mayFail();
        \\    _ = x;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var ctx = TypeContext.init(allocator, &source);
    defer ctx.deinit();

    const tree = source.ast() catch unreachable;
    const tags = tree.nodes.items(.tag);

    var call_node: ?u32 = null;
    for (0..tags.len) |i| {
        if (tags[i] == .call or tags[i] == .call_one) {
            call_node = @intCast(i);
            break;
        }
    }

    try std.testing.expect(call_node != null);
    if (call_node) |cn| {
        try std.testing.expect(ctx.isExpressionErrorUnion(cn));
    }
}

test "TypeContext getContainingFunctionReturnType" {
    const allocator = std.testing.allocator;

    const code: [:0]const u8 =
        \\fn errorReturningFn() !i32 {
        \\    return 42;
        \\}
    ;
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    var ctx = TypeContext.init(allocator, &source);
    defer ctx.deinit();

    const tree = source.ast() catch unreachable;
    const tags = tree.nodes.items(.tag);

    var fn_node: ?u32 = null;
    for (0..tags.len) |i| {
        if (tags[i] == .fn_decl) {
            fn_node = @intCast(i);
            break;
        }
    }

    try std.testing.expect(fn_node != null);
    if (fn_node) |fn_n| {
        const ti = ctx.getContainingFunctionReturnType(fn_n);
        try std.testing.expect(ti != null);
        if (ti) |t| {
            try std.testing.expectEqual(TypeInfo.TypeKind.error_union, t.kind);
        }
    }
}

test "skript residual: strict try queries preserve nullable payloads" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Factory = struct {
        \\    fn dupe(_: Factory, comptime T: type, _: []const T) !?[]T {
        \\        return null;
        \\    }
        \\};
        \\fn maybe() !?u8 { return null; }
        \\fn use(memory: std.mem.Allocator, factory: Factory) !void {
        \\    const allocated = try memory.dupe(u8, "x");
        \\    const possible = try maybe();
        \\    const maybe_slice = try factory.dupe(u8, "x");
        \\    _ = allocated;
        \\    _ = possible;
        \\    _ = maybe_slice;
        \\}
    ;
    var source = Source.init(std.testing.allocator, "payload.zig", code);
    defer source.deinit();
    var ctx = TypeContext.init(std.testing.allocator, &source);
    defer ctx.deinit();
    const tree = try source.ast();
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[index]);
        const expected: TypeInfo.TypeKind = if (std.mem.eql(u8, name, "allocated"))
            .slice
        else if (std.mem.eql(u8, name, "possible") or std.mem.eql(u8, name, "maybe_slice"))
            .optional
        else
            continue;
        const info = ctx.getExpressionTypeStrict(@intCast(index)) orelse return error.MissingType;
        try std.testing.expectEqual(expected, info.kind);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 3), checked);
}

test "skript residual: pointer fields and optional payloads retain declared storage types" {
    const code: [:0]const u8 =
        \\const Unit = @This();
        \\bytes: ?[]const u8,
        \\const Ref = struct { unit: ?*const Unit };
        \\fn text(reference: Ref) []const u8 {
        \\    const unit = reference.unit orelse return "";
        \\    const retained = unit.bytes orelse return "";
        \\    return retained;
        \\}
        \\fn nullable(value: ?u8, fallback: ?u8) ?u8 {
        \\    const possible = value orelse fallback;
        \\    return possible;
        \\}
    ;
    var source = Source.init(std.testing.allocator, "unit.zig", code);
    defer source.deinit();
    var ctx = TypeContext.init(std.testing.allocator, &source);
    defer ctx.deinit();
    const tree = try source.ast();
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[index]);
        const expected: TypeInfo.TypeKind = if (std.mem.eql(u8, name, "retained"))
            .slice
        else if (std.mem.eql(u8, name, "possible"))
            .optional
        else
            continue;
        const info = ctx.getExpressionTypeStrict(@intCast(index)) orelse return error.MissingType;
        try std.testing.expectEqual(expected, info.kind);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), checked);
}

test "skript residual: verified ArrayList elements preserve pointer versus value storage" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Record = struct { value: u8 };
        \\const State = struct {
        \\    pointers: std.ArrayList(*Record),
        \\    values: std.ArrayList(Record),
        \\};
        \\fn read(state: *State) void {
        \\    const pointer = state.pointers.items[0];
        \\    const value = state.values.items[0];
        \\    _ = pointer;
        \\    _ = value;
        \\}
    ;
    var source = Source.init(std.testing.allocator, "list.zig", code);
    defer source.deinit();
    var ctx = TypeContext.init(std.testing.allocator, &source);
    defer ctx.deinit();
    const tree = try source.ast();
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[index]);
        const expected: TypeInfo.TypeKind = if (std.mem.eql(u8, name, "pointer"))
            .pointer
        else if (std.mem.eql(u8, name, "value"))
            .@"struct"
        else
            continue;
        const info = ctx.getExpressionTypeStrict(@intCast(index)) orelse return error.MissingType;
        try std.testing.expectEqual(expected, info.kind);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), checked);
}

test "skript residual: custom ArrayList spelling does not imply standard storage" {
    const code: [:0]const u8 =
        \\const Record = struct { value: u8 };
        \\const std = struct {
        \\    fn ArrayList(comptime T: type) type {
        \\        return struct { items: []?T };
        \\    }
        \\};
        \\const State = struct { entries: std.ArrayList(*Record) };
        \\fn read(state: *State) void {
        \\    const possible = state.entries.items[0];
        \\    _ = possible;
        \\}
    ;
    var source = Source.init(std.testing.allocator, "custom-list.zig", code);
    defer source.deinit();
    var ctx = TypeContext.init(std.testing.allocator, &source);
    defer ctx.deinit();
    const tree = try source.ast();
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[index]);
        if (!std.mem.eql(u8, name, "possible")) continue;
        const info = ctx.getExpressionTypeStrict(@intCast(index));
        try std.testing.expect(info == null or info.?.kind == .unknown or info.?.kind == .optional);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), checked);
}

test "skript residual: custom allocator spelling cannot prove a non-null result" {
    const code: [:0]const u8 =
        \\const std = struct {
        \\    const mem = struct {
        \\        const Allocator = struct {
        \\            fn dupe(_: Allocator, comptime T: type, _: []const T) !?[]T {
        \\                return null;
        \\            }
        \\        };
        \\    };
        \\};
        \\fn read(allocator: std.mem.Allocator) !void {
        \\    const possible = try allocator.dupe(u8, "x");
        \\    _ = possible;
        \\}
    ;
    var source = Source.init(std.testing.allocator, "custom-allocator.zig", code);
    defer source.deinit();
    var ctx = TypeContext.init(std.testing.allocator, &source);
    defer ctx.deinit();
    const tree = try source.ast();
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[index]);
        if (!std.mem.eql(u8, name, "possible")) continue;
        const info = ctx.getExpressionTypeStrict(@intCast(index));
        try std.testing.expect(info == null or info.?.kind == .unknown or info.?.kind == .optional);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), checked);
}

test "imported return payloads and fields retain source identity" {
    const imported: [:0]const u8 =
        \\pub const Box = struct {
        \\    value: ?u8 = null,
        \\    pub fn make() !Box { return .{}; }
        \\    pub fn maybe() !?Box { return null; }
        \\};
        \\pub const Nullable = ?u8;
        \\pub fn alias() Nullable { return null; }
    ;
    const code: [:0]const u8 =
        \\const dep = @import("dep.zig");
        \\const Box = struct { value: []const u8 };
        \\const Nullable = u8;
        \\fn use() !void {
        \\    const stable = try dep.Box.make();
        \\    const possible = try dep.Box.maybe();
        \\    const field = stable.value;
        \\    const alias = dep.alias();
        \\    _ = stable;
        \\    _ = possible;
        \\    _ = field;
        \\    _ = alias;
        \\}
    ;
    var source = Source.init(std.testing.allocator, "main.zig", code);
    defer source.deinit();
    var dependency = Source.init(std.testing.allocator, "dep.zig", imported);
    defer dependency.deinit();
    const tree = try source.ast();
    const files = [_]import_resolver.File{
        .{ .path = source.file_path, .tree = tree },
        .{ .path = dependency.file_path, .tree = try dependency.ast() },
    };
    var ctx = TypeContext.init(std.testing.allocator, &source);
    defer ctx.deinit();
    ctx.project_resolver = .{ .files = &files, .file_index = 0 };
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[index]);
        const expected: TypeInfo.TypeKind = if (std.mem.eql(u8, name, "stable"))
            .@"struct"
        else if (std.mem.eql(u8, name, "possible") or std.mem.eql(u8, name, "field") or std.mem.eql(u8, name, "alias"))
            .optional
        else
            continue;
        const info = ctx.getExpressionTypeStrict(@intCast(index)) orelse return error.MissingType;
        try std.testing.expectEqual(expected, info.kind);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 5), checked);
}

test "nested containers keep distinct same-name method contracts" {
    const code: [:0]const u8 =
        \\const Safe = struct {
        \\    const Handle = struct { fn make() u8 { return 1; } };
        \\};
        \\const Maybe = struct {
        \\    const Handle = struct { fn make() ?u8 { return null; } };
        \\};
        \\fn use() void {
        \\    const sure = Safe.Handle.make();
        \\    const possible = Maybe.Handle.make();
        \\    _ = sure;
        \\    _ = possible;
        \\}
    ;
    var source = Source.init(std.testing.allocator, "nested.zig", code);
    defer source.deinit();
    var ctx = TypeContext.init(std.testing.allocator, &source);
    defer ctx.deinit();
    const tree = try source.ast();
    var checked: usize = 0;
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[index]);
        const expected: TypeInfo.TypeKind = if (std.mem.eql(u8, name, "sure"))
            .uint
        else if (std.mem.eql(u8, name, "possible"))
            .optional
        else
            continue;
        const info = ctx.getExpressionTypeStrict(@intCast(index)) orelse return error.MissingType;
        try std.testing.expectEqual(expected, info.kind);
        checked += 1;
    }
    try std.testing.expectEqual(@as(usize, 2), checked);
}

test "bare method calls use the enclosing container contract" {
    const code: [:0]const u8 =
        \\fn make() u8 { return 1; }
        \\const Factory = struct {
        \\    fn make() ?u8 { return null; }
        \\    fn use() void {
        \\        const possible = make();
        \\        _ = possible;
        \\    }
        \\};
    ;
    var source = Source.init(std.testing.allocator, "scope.zig", code);
    defer source.deinit();
    var ctx = TypeContext.init(std.testing.allocator, &source);
    defer ctx.deinit();
    const tree = try source.ast();
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(tree.nodes.items(.main_token)[index]), "possible")) continue;
        const info = ctx.getExpressionTypeStrict(@intCast(index)) orelse return error.MissingType;
        try std.testing.expectEqual(TypeInfo.TypeKind.optional, info.kind);
        return;
    }
    return error.MissingUse;
}

test "strict expression queries remain independent of heuristic results" {
    const code: [:0]const u8 =
        \\fn inspect(receiver: anytype) void {
        \\    _ = receiver.openFile();
        \\}
    ;
    var source = Source.init(std.testing.allocator, "strict-query.zig", code);
    defer source.deinit();
    var context = TypeContext.init(std.testing.allocator, &source);
    defer context.deinit();
    const tree = try source.ast();
    for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (!call_resolver.isCallNode(tag)) continue;
        const node: u32 = @intCast(index);
        try std.testing.expect(context.getExpressionTypeStrict(node) == null);
        const heuristic = context.getExpressionType(node) orelse return error.MissingType;
        try std.testing.expectEqual(TypeInfo.TypeKind.error_union, heuristic.kind);
        try std.testing.expect(context.getExpressionTypeStrict(node) == null);
        return;
    }
    return error.MissingCall;
}
