const std = @import("std");
const TypeContext = @import("../type_context.zig").TypeContext;
const import_resolver = @import("../analysis/import_resolver.zig");
const call_resolver = @import("../analysis/call_resolver.zig");
const Rule = @import("../rule.zig").Rule;
const RuleError = @import("../rule.zig").RuleError;
const Diagnostic = @import("../rule.zig").Diagnostic;
const Source = @import("../source.zig").Source;
const ast_walk = @import("../ast_walk.zig");

/// Rule that detects unused const/var declarations and functions.
///
/// This rule scans declarations (const, var, fn) at both file-level and inside
/// nested containers (structs, enums, unions) that are not exported (not marked
/// as `pub`, `export`, or `extern`) and checks if they are used elsewhere in
/// their scope. Declarations that are never referenced are reported as warnings.
///
/// Usage detection is AST-based with basic scope awareness to avoid counting
/// references shadowed by locals or payload bindings.
pub const UnusedDeclRule = struct {
    pub const rule: Rule = Rule{
        .name = "unused-decl",
        .default_severity = .warning,
        .checkFn = check,
    };

    const DeclInfo = struct {
        name: []const u8,
        normalized_name: []const u8,
        token_index: u32,
        byte_offset: usize,
        allow_field_access: bool,
        owner_container: ?u32,
        owner_container_name: ?[]const u8,
        receiver_type_node: ?u32,
        is_function: bool,
    };

    /// Kind of declaration for more descriptive diagnostic messages.
    const DeclKind = enum {
        function,
        type_decl, // struct, enum, union
        constant,
        variable,
        declaration, // fallback when kind cannot be determined
    };

    /// Classify a declaration using ZIR-based type information for better diagnostics.
    fn classifyDecl(src: *Source, decl: DeclInfo) DeclKind {
        if (decl.is_function) return .function;
        if (decl.owner_container != null) return .declaration;

        // Try to get type info from ZIR
        const zir_decl = src.findDecl(decl.name) orelse {
            // No ZIR info available, use basic classification
            return .declaration;
        };

        // Check if it's a type
        switch (zir_decl.type_info.kind) {
            .@"struct", .@"enum", .@"union", .type_type, .function => return .type_decl,
            else => {},
        }

        // It's a value
        if (zir_decl.is_const) return .constant;
        return .variable;
    }

    /// Get a human-readable description for a declaration kind.
    fn declKindDescription(kind: DeclKind) []const u8 {
        return switch (kind) {
            .function => "Function",
            .type_decl => "Type",
            .constant => "Constant",
            .variable => "Variable",
            .declaration => "Declaration",
        };
    }

    fn check(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
    ) RuleError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);
        const token_starts = tree.tokens.items(.start);

        var decls: std.ArrayList(DeclInfo) = .empty;
        defer decls.deinit(allocator);

        var container_names: std.AutoHashMap(u32, []const u8) = .init(allocator);
        defer container_names.deinit();
        try collectContainerNames(tree, allocator, &container_names);

        try collectRootDecls(tree, allocator, &decls, token_starts);
        try collectContainerDecls(tree, allocator, &decls, tags, token_starts, &container_names);

        const parent_map = try allocator.alloc(u32, tags.len);
        defer allocator.free(parent_map);
        @memset(parent_map, 0);
        for (tree.rootDecls()) |root| {
            ast_walk.fillParentMap(tree, @intFromEnum(root), parent_map);
        }

        var type_ctx = TypeContext.init(allocator, src);
        defer type_ctx.deinit();
        var reference_paths = try ReferencePaths.init(allocator, tree, parent_map);
        defer reference_paths.deinit();

        for (decls.items) |decl| {
            if (!try isDeclUsed(tree, allocator, decl, parent_map, &type_ctx, &reference_paths)) {
                const range = try src.byteRangeToSourceRange(decl.byte_offset, decl.byte_offset + decl.name.len);

                // Use ZIR-based type info for more descriptive messages
                const decl_kind = classifyDecl(src, decl);
                const kind_desc = declKindDescription(decl_kind);

                const message = try std.fmt.allocPrint(
                    allocator,
                    "{s} '{s}' is never used",
                    .{ kind_desc, decl.name },
                );
                defer allocator.free(message);

                const diag = try Diagnostic.init(
                    allocator,
                    src.getFilePath(),
                    "unused-decl",
                    .warning,
                    message,
                    range,
                );
                try diagnostics.append(allocator, diag);
            }
        }
    }

    fn collectRootDecls(
        tree: *const std.zig.Ast,
        allocator: std.mem.Allocator,
        decls: *std.ArrayList(DeclInfo),
        token_starts: []const u32,
    ) RuleError!void {
        const tags = tree.nodes.items(.tag);
        const root_decls = tree.rootDecls();

        for (root_decls) |decl_idx| {
            const idx = @intFromEnum(decl_idx);
            const tag = tags[idx];

            const decl_info = switch (tag) {
                .simple_var_decl,
                .aligned_var_decl,
                .global_var_decl,
                => extractVarDecl(tree, @intCast(idx), token_starts, false, null, null),
                .fn_decl,
                .fn_proto,
                .fn_proto_simple,
                .fn_proto_one,
                .fn_proto_multi,
                => extractFnDecl(tree, @intCast(idx), token_starts, false, null, null),
                else => null,
            };

            if (decl_info) |info| {
                if (!isSpecialName(info.name)) {
                    try decls.append(allocator, info);
                }
            }
        }
    }

    fn collectContainerDecls(
        tree: *const std.zig.Ast,
        allocator: std.mem.Allocator,
        decls: *std.ArrayList(DeclInfo),
        tags: []const std.zig.Ast.Node.Tag,
        token_starts: []const u32,
        container_names: *const std.AutoHashMap(u32, []const u8),
    ) RuleError!void {
        for (tags, 0..) |tag, i| {
            switch (tag) {
                .container_decl,
                .container_decl_trailing,
                .container_decl_two,
                .container_decl_two_trailing,
                .container_decl_arg,
                .container_decl_arg_trailing,
                .tagged_union,
                .tagged_union_trailing,
                .tagged_union_enum_tag,
                .tagged_union_enum_tag_trailing,
                .tagged_union_two,
                .tagged_union_two_trailing,
                => {
                    var member_buf: [2]std.zig.Ast.Node.Index = undefined;
                    const members = getContainerMembers(tree, @intCast(i), &member_buf);
                    if (members.len == 0) continue;

                    for (members) |member_idx| {
                        const member = @intFromEnum(member_idx);
                        const member_tag = tags[member];
                        const container_name = container_names.get(@as(u32, @intCast(i)));

                        const decl_info = switch (member_tag) {
                            .simple_var_decl,
                            .aligned_var_decl,
                            .global_var_decl,
                            => extractVarDecl(
                                tree,
                                @intCast(member),
                                token_starts,
                                true,
                                @as(u32, @intCast(i)),
                                container_name,
                            ),
                            .fn_decl,
                            .fn_proto,
                            .fn_proto_simple,
                            .fn_proto_one,
                            .fn_proto_multi,
                            => extractFnDecl(
                                tree,
                                @intCast(member),
                                token_starts,
                                true,
                                @as(u32, @intCast(i)),
                                container_name,
                            ),
                            else => null,
                        };

                        if (decl_info) |info| {
                            if (!isSpecialName(info.name)) {
                                try decls.append(allocator, info);
                            }
                        }
                    }
                },
                else => {},
            }
        }
    }

    fn getContainerMembers(
        tree: *const std.zig.Ast,
        node: u32,
        buf: *[2]std.zig.Ast.Node.Index,
    ) []const std.zig.Ast.Node.Index {
        const tags = tree.nodes.items(.tag);
        const tag = tags[node];

        return switch (tag) {
            .container_decl, .container_decl_trailing => tree.containerDecl(@enumFromInt(node)).ast.members,
            .container_decl_two, .container_decl_two_trailing => tree.containerDeclTwo(buf, @enumFromInt(node)).ast.members,
            .container_decl_arg, .container_decl_arg_trailing => tree.containerDeclArg(@enumFromInt(node)).ast.members,
            .tagged_union, .tagged_union_trailing => tree.taggedUnion(@enumFromInt(node)).ast.members,
            .tagged_union_enum_tag, .tagged_union_enum_tag_trailing => tree.taggedUnionEnumTag(@enumFromInt(node)).ast.members,
            .tagged_union_two, .tagged_union_two_trailing => tree.taggedUnionTwo(buf, @enumFromInt(node)).ast.members,
            else => &.{},
        };
    }

    fn extractVarDecl(
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_starts: []const u32,
        allow_field_access: bool,
        owner_container: ?u32,
        owner_container_name: ?[]const u8,
    ) ?DeclInfo {
        const full = tree.fullVarDecl(@enumFromInt(node_idx)) orelse return null;
        if (full.visib_token != null) return null;
        if (full.extern_export_token != null) return null;

        const token_tags = tree.tokens.items(.tag);
        const name_token = full.ast.mut_token + 1;
        if (name_token >= token_tags.len) return null;
        if (token_tags[name_token] != .identifier) return null;

        const name = tree.tokenSlice(name_token);
        const name_start = token_starts[name_token];

        return DeclInfo{
            .name = name,
            .normalized_name = normalizeIdentifier(name),
            .token_index = name_token,
            .byte_offset = name_start,
            .allow_field_access = allow_field_access,
            .owner_container = owner_container,
            .owner_container_name = owner_container_name,
            .receiver_type_node = null,
            .is_function = false,
        };
    }

    fn extractFnDecl(
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_starts: []const u32,
        allow_field_access: bool,
        owner_container: ?u32,
        owner_container_name: ?[]const u8,
    ) ?DeclInfo {
        const tags = tree.nodes.items(.tag);
        const tag = tags[node_idx];

        var buffer: [1]std.zig.Ast.Node.Index = undefined;

        return switch (tag) {
            .fn_decl => blk: {
                const data = tree.nodes.items(.data)[node_idx];
                const proto_node = @intFromEnum(data.node_and_node[0]);
                break :blk extractFnDecl(
                    tree,
                    proto_node,
                    token_starts,
                    allow_field_access,
                    owner_container,
                    owner_container_name,
                );
            },
            .fn_proto => extractFnDeclFromProto(
                tree,
                tree.fnProto(@enumFromInt(node_idx)),
                token_starts,
                allow_field_access,
                owner_container,
                owner_container_name,
            ),
            .fn_proto_simple => extractFnDeclFromProto(
                tree,
                tree.fnProtoSimple(&buffer, @enumFromInt(node_idx)),
                token_starts,
                allow_field_access,
                owner_container,
                owner_container_name,
            ),
            .fn_proto_one => extractFnDeclFromProto(
                tree,
                tree.fnProtoOne(&buffer, @enumFromInt(node_idx)),
                token_starts,
                allow_field_access,
                owner_container,
                owner_container_name,
            ),
            .fn_proto_multi => extractFnDeclFromProto(
                tree,
                tree.fnProtoMulti(@enumFromInt(node_idx)),
                token_starts,
                allow_field_access,
                owner_container,
                owner_container_name,
            ),
            else => null,
        };
    }

    fn extractFnDeclFromProto(
        tree: *const std.zig.Ast,
        proto: std.zig.Ast.full.FnProto,
        token_starts: []const u32,
        allow_field_access: bool,
        owner_container: ?u32,
        owner_container_name: ?[]const u8,
    ) ?DeclInfo {
        if (proto.visib_token != null) return null;
        if (proto.extern_export_inline_token) |tok| {
            const tag = tree.tokenTag(tok);
            if (tag == .keyword_extern or tag == .keyword_export) return null;
        }

        const name_token = proto.name_token orelse return null;
        if (tree.tokenTag(name_token) != .identifier) return null;

        const name = tree.tokenSlice(name_token);
        const name_start = token_starts[name_token];

        return DeclInfo{
            .name = name,
            .normalized_name = normalizeIdentifier(name),
            .token_index = name_token,
            .byte_offset = name_start,
            .allow_field_access = allow_field_access,
            .owner_container = owner_container,
            .owner_container_name = owner_container_name,
            .receiver_type_node = if (owner_container == null) receiverTypeNode(tree, proto) else null,
            .is_function = true,
        };
    }

    fn receiverTypeNode(tree: *const std.zig.Ast, proto: std.zig.Ast.full.FnProto) ?u32 {
        var params = proto.iterate(tree);
        const first = params.next() orelse return null;
        const type_expr = first.type_expr orelse return null;
        return @intFromEnum(type_expr);
    }

    fn normalizeIdentifier(ident: []const u8) []const u8 {
        if (ident.len >= 3 and std.mem.startsWith(u8, ident, "@\"") and ident[ident.len - 1] == '"') {
            return ident[2 .. ident.len - 1];
        }
        return ident;
    }

    fn isSpecialName(name: []const u8) bool {
        if (name.len > 0 and name[0] == '_') return true;
        if (std.mem.eql(u8, name, "main")) return true;
        if (std.mem.eql(u8, name, "panic")) return true;
        return false;
    }

    /// Names select paths to inspect; the scanner still decides scope and receiver identity.
    const ReferencePaths = struct {
        arena: std.heap.ArenaAllocator,
        parents: []u32 = &.{},
        active: []usize = &.{},
        generation: usize = 0,
        names: std.StringHashMapUnmanaged(std.ArrayList(u32)) = .empty,
        roots: std.AutoHashMapUnmanaged(u32, void) = .empty,
        reflection_calls: std.ArrayList(u32) = .empty,
        active_roots: std.ArrayList(u32) = .empty,

        fn init(allocator: std.mem.Allocator, tree: *const std.zig.Ast, parents: []const u32) !ReferencePaths {
            var self = ReferencePaths{ .arena = std.heap.ArenaAllocator.init(allocator) };
            errdefer self.deinit();
            const arena = self.arena.allocator();
            self.parents = try arena.dupe(u32, parents);
            self.active = try arena.alloc(usize, parents.len);
            @memset(self.active, 0);
            for (tree.rootDecls()) |root| try self.roots.put(arena, @intFromEnum(root), {});
            for (tree.nodes.items(.tag), 0..) |tag, node_index| {
                if (node_index == 0) continue;
                const node: u32 = @intCast(node_index);
                var links = ParentLinks{ .parents = self.parents, .parent = node };
                var container_buffer: [2]std.zig.Ast.Node.Index = undefined;
                if (tree.fullContainerDecl(&container_buffer, @enumFromInt(node))) |container| {
                    links.optional(container.ast.arg);
                    for (container.ast.members) |member| links.link(@intFromEnum(member));
                } else {
                    ast_walk.walkChildren(ParentLinks, tree, node, &links, ParentLinks.visit) catch unreachable;
                }
                // Runtime walks omit declaration metadata, but liveness scans it.
                if (tag == .fn_decl) links.link(@intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]));
                if (tree.fullVarDecl(@enumFromInt(node))) |full| {
                    links.optional(full.ast.type_node);
                    links.optional(full.ast.align_node);
                    links.optional(full.ast.addrspace_node);
                    links.optional(full.ast.section_node);
                }
                const name = switch (tag) {
                    .identifier, .enum_literal => normalizeIdentifier(tree.tokenSlice(tree.nodes.items(.main_token)[node])),
                    .field_access => import_resolver.fieldAccessName(tree, node),
                    else => null,
                };
                if (name) |normalized| {
                    const result = try self.names.getOrPut(arena, normalized);
                    if (!result.found_existing) result.value_ptr.* = .empty;
                    try result.value_ptr.append(arena, node);
                }
                if (call_resolver.isCallNode(tag)) {
                    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
                    const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse continue;
                    const method = import_resolver.fieldAccessName(tree, @intFromEnum(call.ast.fn_expr)) orelse continue;
                    if (std.mem.eql(u8, method, "refAllDecls") or std.mem.eql(u8, method, "refAllDeclsRecursive")) {
                        try self.reflection_calls.append(arena, node);
                    }
                }
            }
            return self;
        }

        fn deinit(self: *ReferencePaths) void {
            self.arena.deinit();
        }

        fn select(self: *ReferencePaths, name: []const u8, include_reflection: bool) !void {
            self.generation += 1;
            self.active_roots.clearRetainingCapacity();
            if (self.names.get(name)) |nodes| {
                for (nodes.items) |node| try self.markPath(node);
            }
            if (include_reflection) {
                for (self.reflection_calls.items) |node| try self.markPath(node);
            }
        }

        fn markPath(self: *ReferencePaths, initial: u32) !void {
            var node = initial;
            while (node != 0 and node < self.parents.len and self.active[node] != self.generation) {
                self.active[node] = self.generation;
                const parent = self.parents[node];
                if (parent == 0 and self.roots.contains(node)) {
                    try self.active_roots.append(self.arena.allocator(), node);
                }
                node = parent;
            }
        }

        const ParentLinks = struct {
            parents: []u32,
            parent: u32,

            fn link(self: *ParentLinks, child: u32) void {
                if (child != 0 and child < self.parents.len and self.parents[child] == 0) {
                    self.parents[child] = self.parent;
                }
            }

            fn optional(self: *ParentLinks, child: std.zig.Ast.Node.OptionalIndex) void {
                if (child.unwrap()) |node| self.link(@intFromEnum(node));
            }

            fn visit(_: *const std.zig.Ast, child: u32, self: *ParentLinks) error{}!void {
                self.link(child);
            }
        };
    };

    fn isDeclUsed(
        tree: *const std.zig.Ast,
        allocator: std.mem.Allocator,
        decl: DeclInfo,
        parent_map: []const u32,
        type_ctx: *TypeContext,
        reference_paths: *ReferencePaths,
    ) RuleError!bool {
        try reference_paths.select(decl.normalized_name, decl.owner_container != null);
        var scanner = UsageScanner.init(allocator, tree, decl, parent_map, type_ctx, reference_paths);
        defer scanner.deinit();
        return scanner.scanRoot();
    }

    const UsageScanner = struct {
        allocator: std.mem.Allocator,
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        normalized_name: []const u8,
        allow_field_access: bool,
        owner_container: ?u32,
        owner_container_name: ?[]const u8,
        is_function: bool,
        receiver_type_node: ?u32,
        parent_map: []const u32,
        type_ctx: *TypeContext,
        reference_paths: *const ReferencePaths,
        inside_owner_container: bool = false,
        shadowed: bool = false,
        shadow_stack: std.ArrayListUnmanaged(bool) = .empty,
        container_stack: std.ArrayListUnmanaged(bool) = .empty,

        fn init(
            allocator: std.mem.Allocator,
            tree: *const std.zig.Ast,
            decl: DeclInfo,
            parent_map: []const u32,
            type_ctx: *TypeContext,
            reference_paths: *const ReferencePaths,
        ) UsageScanner {
            return .{
                .allocator = allocator,
                .tree = tree,
                .tags = tree.nodes.items(.tag),
                .datas = tree.nodes.items(.data),
                .main_tokens = tree.nodes.items(.main_token),
                .token_tags = tree.tokens.items(.tag),
                .normalized_name = decl.normalized_name,
                .allow_field_access = decl.allow_field_access,
                .owner_container = decl.owner_container,
                .owner_container_name = decl.owner_container_name,
                .is_function = decl.is_function,
                .receiver_type_node = decl.receiver_type_node,
                .parent_map = parent_map,
                .type_ctx = type_ctx,
                .reference_paths = reference_paths,
            };
        }

        fn deinit(self: *UsageScanner) void {
            self.shadow_stack.deinit(self.allocator);
            self.container_stack.deinit(self.allocator);
        }

        fn scanRoot(self: *UsageScanner) RuleError!bool {
            for (self.reference_paths.active_roots.items) |node| {
                if (try self.scanNode(node)) return true;
            }
            return false;
        }

        fn pushScope(self: *UsageScanner) RuleError!void {
            try self.shadow_stack.append(self.allocator, self.shadowed);
        }

        fn popScope(self: *UsageScanner) void {
            self.shadowed = self.shadow_stack.pop() orelse false;
        }

        fn pushContainerScope(self: *UsageScanner, container_node: u32) RuleError!void {
            try self.container_stack.append(self.allocator, self.inside_owner_container);
            if (!self.inside_owner_container) {
                if (self.owner_container) |owner| {
                    if (owner == container_node) {
                        self.inside_owner_container = true;
                    }
                }
            }
        }

        fn popContainerScope(self: *UsageScanner) void {
            self.inside_owner_container = self.container_stack.pop() orelse false;
        }

        fn scanNode(self: *UsageScanner, node: u32) RuleError!bool {
            if (node == 0) return false;
            if (node >= self.datas.len) return false;
            if (self.reference_paths.active[node] != self.reference_paths.generation) return false;

            const tag = self.tags[node];
            const data = self.datas[node];

            switch (tag) {
                .identifier => return self.isIdentifierUsed(node),
                .enum_literal => return !self.is_function and
                    self.isTokenName(self.main_tokens[node]) and self.resultLocationTargetsOwner(node),
                .field_access => return self.scanFieldAccess(@intCast(node), data),
                .fn_decl => return self.scanFnDecl(node),
                .fn_proto,
                .fn_proto_simple,
                .fn_proto_one,
                .fn_proto_multi,
                => return self.scanFnProto(node),
                .call, .call_comma, .call_one, .call_one_comma => return self.scanCall(node),
                .simple_var_decl,
                .aligned_var_decl,
                .local_var_decl,
                .global_var_decl,
                => return self.scanVarDecl(node),
                .block,
                .block_semicolon,
                .block_two,
                .block_two_semicolon,
                => return self.scanBlock(node),
                .assign_destructure => return self.scanAssignDestructure(node),
                .@"if" => return self.scanIfFull(node),
                .if_simple => return self.scanIfSimple(node),
                .while_simple,
                .while_cont,
                .@"while",
                => return self.scanWhile(node),
                .@"for",
                .for_simple,
                => return self.scanFor(node),
                .@"switch",
                .switch_comma,
                => return self.scanSwitch(node),
                .@"catch" => return self.scanCatch(node),
                .@"errdefer" => return self.scanErrdefer(node),
                .container_decl,
                .container_decl_trailing,
                .container_decl_two,
                .container_decl_two_trailing,
                .container_decl_arg,
                .container_decl_arg_trailing,
                .tagged_union,
                .tagged_union_trailing,
                .tagged_union_enum_tag,
                .tagged_union_enum_tag_trailing,
                .tagged_union_two,
                .tagged_union_two_trailing,
                => return self.scanContainerDecl(node),
                else => {},
            }

            return switch (tag) {
                .container_field,
                .container_field_init,
                .container_field_align,
                => blk: {
                    const field = self.tree.fullContainerField(@enumFromInt(node)) orelse return false;
                    break :blk self.scanAstValuesForName(
                        @TypeOf(field),
                        field,
                        &.{ .type_expr, .value_expr, .align_expr },
                    );
                },

                // zig fmt: off
                .switch_case_one, .switch_case_inline_one => self.scanSwitchCase(node),
                .switch_case, .switch_case_inline =>        self.scanAstParentOpForName(@TypeOf(self.tree.switchCase(@enumFromInt(node))), self.tree.switchCase(@enumFromInt(node)), .target_expr, .values),
                .@"asm" =>                                  self.scanAstParentOpForName(@TypeOf(self.tree.asmFull(@enumFromInt(node))), self.tree.asmFull(@enumFromInt(node)), .template, .items),
                // zig fmt: on

                else => self.scanChildren(node),
            };
        }

        fn scanCall(self: *UsageScanner, node: u32) RuleError!bool {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = self.tree.fullCall(&buffer, @enumFromInt(node)) orelse return false;
            const callee = @intFromEnum(call.ast.fn_expr);
            if (callee < self.tags.len and self.tags[callee] == .enum_literal and
                self.is_function and self.owner_container != null and
                self.resultLocationTargetsOwner(node))
            {
                const token = self.main_tokens[callee];
                if (self.isTokenName(token)) return true;
            }
            if (self.callReflectsOwner(node)) return true;
            return self.scanChildren(node);
        }

        fn resultLocationTargetsOwner(self: *UsageScanner, node: u32) bool {
            const local_files = [_]import_resolver.File{.{ .path = "", .tree = self.tree }};
            const resolver = self.type_ctx.project_resolver orelse call_resolver.ProjectTypeResolver{
                .files = &local_files,
                .file_index = 0,
            };
            const expected = resolver.resolveResultLocationTypeNode(node) orelse return false;
            const owner_resolver = call_resolver.ProjectTypeResolver{
                .files = resolver.files,
                .file_index = expected.file_index,
            };
            const owner = owner_resolver.resolveTypeNode(expected.node_index) orelse return false;
            return resolver.files[owner.file_index].tree == self.tree and owner.container_node == self.owner_container;
        }

        fn callReflectsOwner(self: *UsageScanner, node: u32) bool {
            if (!self.inside_owner_container) return false;
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = self.tree.fullCall(&buffer, @enumFromInt(node)) orelse return false;
            const callee = @intFromEnum(call.ast.fn_expr);
            if (callee >= self.tags.len or self.tags[callee] != .field_access) return false;
            const access = self.datas[callee].node_and_token;
            const field_token = access[1];
            if (!self.tokenMatchesSlice(field_token, "refAllDecls") and
                !self.tokenMatchesSlice(field_token, "refAllDeclsRecursive")) return false;
            if (call.ast.params.len != 1) return false;
            const target = @intFromEnum(call.ast.params[0]);
            if (target >= self.tags.len) return false;
            if (self.tags[target] == .builtin_call or
                self.tags[target] == .builtin_call_comma or
                self.tags[target] == .builtin_call_two or
                self.tags[target] == .builtin_call_two_comma)
            {
                const token = self.main_tokens[target];
                if (token < self.token_tags.len and std.mem.eql(u8, self.tree.tokenSlice(token), "@This")) {
                    return true;
                }
            }
            if (self.tags[target] == .identifier) {
                if (self.owner_container_name) |owner_name| {
                    return self.tokenMatchesSlice(self.main_tokens[target], owner_name);
                }
            }
            return false;
        }

        fn scanChildren(self: *UsageScanner, node: u32) RuleError!bool {
            const ChildScanner = struct {
                scanner: *UsageScanner,
                used: *bool,
                stop: bool = false,

                fn visitChild(_: *const std.zig.Ast, child_node: u32, ctx: *@This()) RuleError!void {
                    if (ctx.stop) return;
                    if (try ctx.scanner.scanNode(child_node)) {
                        ctx.used.* = true;
                        ctx.stop = true;
                    }
                }
            };

            var used = false;
            var ctx = ChildScanner{
                .scanner = self,
                .used = &used,
            };

            try ast_walk.walkChildren(ChildScanner, self.tree, node, &ctx, ChildScanner.visitChild);
            return used;
        }

        fn scanNodes(self: *UsageScanner, nodes: []const std.zig.Ast.Node.Index) RuleError!bool {
            for (nodes) |item| {
                if (try self.scanNode(@intFromEnum(item))) return true;
            }
            return false;
        }

        fn scanFieldAccess(self: *UsageScanner, node: u32, data: std.zig.Ast.Node.Data) RuleError!bool {
            const receiver_node = @intFromEnum(data.node_and_token[0]);
            const field_token = data.node_and_token[1];

            if (self.isTokenName(field_token)) {
                if (self.isTypedReceiver(receiver_node)) return true;
                if (self.allow_field_access) {
                    if (self.inside_owner_container) return true;
                    if (self.is_function) {
                        // A bare field read can never invoke a method. Only a
                        // call through the field, or a namespace access naming
                        // the owner, counts as a use. A same-named field read
                        // on another type must not mask an unused method.
                        if (self.fieldAccessIsCallee(node)) return true;
                        if (self.owner_container) |owner| {
                            // `Owner.name`, or `struct {...}.name` whose receiver
                            // is the owner container itself, unambiguously names
                            // this member.
                            if (receiver_node == owner) return true;
                            if (self.owner_container_name) |owner_name| {
                                if (self.accessHasOwnerName(receiver_node, owner_name)) return true;
                            }
                        } else {
                            return true;
                        }
                    } else if (self.owner_container_name) |owner_name| {
                        if (self.accessHasOwnerName(receiver_node, owner_name)) {
                            return true;
                        }
                    } else {
                        return true;
                    }
                }
            }
            return self.scanNode(receiver_node);
        }

        fn fieldAccessIsCallee(self: *UsageScanner, node: u32) bool {
            if (node == 0 or node >= self.parent_map.len) return false;
            const parent = self.parent_map[node];
            if (parent == 0 or parent >= self.tags.len) return false;
            switch (self.tags[parent]) {
                .call, .call_comma, .call_one, .call_one_comma => {},
                else => return false,
            }
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const full_call = self.tree.fullCall(&call_buf, @enumFromInt(parent)) orelse return false;
            return @intFromEnum(full_call.ast.fn_expr) == node;
        }

        fn isTypedReceiver(self: *UsageScanner, receiver_node: u32) bool {
            const expected_type_node = self.receiver_type_node orelse return false;
            const files = [_]import_resolver.File{
                .{ .path = "", .tree = self.tree },
            };
            const resolver = call_resolver.ProjectTypeResolver{
                .files = &files,
                .file_index = 0,
            };
            const expected_type = resolver.resolveTypeNode(expected_type_node) orelse return false;
            if (expected_type.container_node != null) return false;
            const actual_type = resolver.resolveExprType(receiver_node) orelse return false;
            return call_resolver.resolvedTypesEqual(actual_type, expected_type);
        }

        fn scanVarDecl(self: *UsageScanner, node: u32) RuleError!bool {
            const full = self.tree.fullVarDecl(@enumFromInt(node)) orelse return false;
            if (try self.scanOptionalNode(full.ast.type_node)) return true;
            if (try self.scanOptionalNode(full.ast.align_node)) return true;
            if (try self.scanOptionalNode(full.ast.addrspace_node)) return true;
            if (try self.scanOptionalNode(full.ast.section_node)) return true;
            return self.scanOptionalNode(full.ast.init_node);
        }

        fn scanOptionalNode(self: *UsageScanner, node_opt: std.zig.Ast.Node.OptionalIndex) RuleError!bool {
            if (node_opt.unwrap()) |node| {
                return self.scanNode(@intFromEnum(node));
            }
            return false;
        }

        fn scanFnDecl(self: *UsageScanner, node: u32) RuleError!bool {
            const data = self.datas[node];
            const proto_node = @intFromEnum(data.node_and_node[0]);
            const body_node = @intFromEnum(data.node_and_node[1]);

            if (try self.scanFnProto(proto_node)) return true;
            if (body_node == 0) return false;

            try self.pushScope();
            defer self.popScope();
            self.shadowFnParams(proto_node);
            return self.scanNode(body_node);
        }

        fn scanFnProto(self: *UsageScanner, node: u32) RuleError!bool {
            const tag = self.tags[node];
            var buffer: [1]std.zig.Ast.Node.Index = undefined;

            return switch (tag) {
                .fn_proto => self.scanFnProtoComponents(self.tree.fnProto(@enumFromInt(node))),
                .fn_proto_simple => self.scanFnProtoComponents(self.tree.fnProtoSimple(&buffer, @enumFromInt(node))),
                .fn_proto_one => self.scanFnProtoComponents(self.tree.fnProtoOne(&buffer, @enumFromInt(node))),
                .fn_proto_multi => self.scanFnProtoComponents(self.tree.fnProtoMulti(@enumFromInt(node))),
                else => false,
            };
        }

        fn scanFnProtoComponents(self: *UsageScanner, proto: std.zig.Ast.full.FnProto) RuleError!bool {
            if (try self.scanNodes(proto.ast.params)) return true;
            if (try self.scanOptionalNode(proto.ast.return_type)) return true;
            if (try self.scanOptionalNode(proto.ast.align_expr)) return true;
            if (try self.scanOptionalNode(proto.ast.addrspace_expr)) return true;
            if (try self.scanOptionalNode(proto.ast.section_expr)) return true;
            return self.scanOptionalNode(proto.ast.callconv_expr);
        }

        fn shadowFnParams(self: *UsageScanner, node: u32) void {
            const tag = self.tags[node];
            var buffer: [1]std.zig.Ast.Node.Index = undefined;

            switch (tag) {
                .fn_proto => self.shadowFnProtoParams(self.tree.fnProto(@enumFromInt(node))),
                .fn_proto_simple => self.shadowFnProtoParams(self.tree.fnProtoSimple(&buffer, @enumFromInt(node))),
                .fn_proto_one => self.shadowFnProtoParams(self.tree.fnProtoOne(&buffer, @enumFromInt(node))),
                .fn_proto_multi => self.shadowFnProtoParams(self.tree.fnProtoMulti(@enumFromInt(node))),
                else => {},
            }
        }

        fn shadowFnProtoParams(self: *UsageScanner, proto: std.zig.Ast.full.FnProto) void {
            var it = proto.iterate(self.tree);
            while (it.next()) |param| {
                if (param.name_token) |tok| {
                    self.shadowIfToken(tok);
                }
            }
        }

        fn scanBlock(self: *UsageScanner, node: u32) RuleError!bool {
            var statements: []const u32 = &.{};
            var scratch_buf: [2]u32 = undefined;

            switch (self.tags[node]) {
                .block, .block_semicolon => {
                    const extra_range = self.datas[node].extra_range;
                    const start = @intFromEnum(extra_range.start);
                    const end = @intFromEnum(extra_range.end);
                    statements = self.tree.extra_data[start..end];
                },
                .block_two, .block_two_semicolon => {
                    const opt_nodes = self.datas[node].opt_node_and_opt_node;
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
                else => return false,
            }

            try self.pushScope();
            defer self.popScope();

            for (statements) |stmt| {
                if (try self.scanNode(stmt)) return true;
                if (self.nodeDeclaresName(stmt)) {
                    self.shadowed = true;
                }
            }
            return false;
        }

        fn scanAssignDestructure(self: *UsageScanner, node: u32) RuleError!bool {
            const destruct = self.tree.assignDestructure(@enumFromInt(node));
            if (try self.scanNode(@intFromEnum(destruct.ast.value_expr))) return true;
            return self.scanNodes(destruct.ast.variables);
        }

        fn scanIfFull(self: *UsageScanner, node: u32) RuleError!bool {
            const full_if = self.tree.fullIf(@enumFromInt(node)) orelse return false;
            if (try self.scanNode(@intFromEnum(full_if.ast.cond_expr))) return true;

            try self.pushScope();
            if (full_if.payload_token) |tok| self.shadowIfToken(tok);
            const then_used = try self.scanNode(@intFromEnum(full_if.ast.then_expr));
            self.popScope();
            if (then_used) return true;

            if (full_if.ast.else_expr.unwrap()) |else_node| {
                try self.pushScope();
                if (full_if.error_token) |tok| self.shadowIfToken(tok);
                const else_used = try self.scanNode(@intFromEnum(else_node));
                self.popScope();
                if (else_used) return true;
            }
            return false;
        }

        fn scanIfSimple(self: *UsageScanner, node: u32) RuleError!bool {
            const full_if = self.tree.ifSimple(@enumFromInt(node));
            if (try self.scanNode(@intFromEnum(full_if.ast.cond_expr))) return true;
            try self.pushScope();
            if (full_if.payload_token) |tok| self.shadowIfToken(tok);
            const then_used = try self.scanNode(@intFromEnum(full_if.ast.then_expr));
            self.popScope();
            return then_used;
        }

        fn scanWhile(self: *UsageScanner, node: u32) RuleError!bool {
            const tag = self.tags[node];
            const full_while = switch (tag) {
                .while_simple => self.tree.whileSimple(@enumFromInt(node)),
                .while_cont => self.tree.whileCont(@enumFromInt(node)),
                .@"while" => self.tree.whileFull(@enumFromInt(node)),
                else => return false,
            };

            if (try self.scanNode(@intFromEnum(full_while.ast.cond_expr))) return true;

            try self.pushScope();
            if (full_while.payload_token) |tok| self.shadowIfToken(tok);
            const body_used = try self.scanNode(@intFromEnum(full_while.ast.then_expr));
            self.popScope();
            if (body_used) return true;

            if (full_while.ast.else_expr.unwrap()) |else_node| {
                try self.pushScope();
                if (full_while.error_token) |tok| self.shadowIfToken(tok);
                const else_used = try self.scanNode(@intFromEnum(else_node));
                self.popScope();
                if (else_used) return true;
            }
            return false;
        }

        fn scanFor(self: *UsageScanner, node: u32) RuleError!bool {
            const tag = self.tags[node];
            const full_for = switch (tag) {
                .@"for" => self.tree.forFull(@enumFromInt(node)),
                .for_simple => self.tree.forSimple(@enumFromInt(node)),
                else => return false,
            };
            if (try self.scanNodes(full_for.ast.inputs)) return true;

            try self.pushScope();
            self.shadowForPayload(full_for.payload_token);
            const then_used = try self.scanNode(@intFromEnum(full_for.ast.then_expr));
            self.popScope();
            if (then_used) return true;

            if (full_for.ast.else_expr.unwrap()) |else_node| {
                if (try self.scanNode(@intFromEnum(else_node))) return true;
            }
            return false;
        }

        fn scanSwitch(self: *UsageScanner, node: u32) RuleError!bool {
            const full_switch = self.tree.switchFull(@enumFromInt(node));
            if (try self.scanNode(@intFromEnum(full_switch.ast.condition))) return true;
            for (full_switch.ast.cases) |case_node| {
                if (try self.scanSwitchCase(@intFromEnum(case_node))) return true;
            }
            return false;
        }

        fn scanSwitchCase(self: *UsageScanner, node: u32) RuleError!bool {
            const full_case = self.tree.fullSwitchCase(@enumFromInt(node)) orelse return false;
            if (try self.scanNodes(full_case.ast.values)) return true;

            try self.pushScope();
            if (full_case.payload_token) |tok| self.shadowIfToken(tok);
            const target_used = try self.scanNode(@intFromEnum(full_case.ast.target_expr));
            self.popScope();
            return target_used;
        }

        fn scanCatch(self: *UsageScanner, node: u32) RuleError!bool {
            const data = self.datas[node].node_and_node;
            if (try self.scanNode(@intFromEnum(data[0]))) return true;

            var payload_token: ?u32 = null;
            const catch_token = self.main_tokens[node];
            if (catch_token + 2 < self.token_tags.len and self.token_tags[catch_token + 1] == .pipe) {
                payload_token = catch_token + 2;
            }

            try self.pushScope();
            if (payload_token) |tok| self.shadowIfToken(tok);
            const rhs_used = try self.scanNode(@intFromEnum(data[1]));
            self.popScope();
            return rhs_used;
        }

        fn scanErrdefer(self: *UsageScanner, node: u32) RuleError!bool {
            const data = self.datas[node].opt_token_and_node;
            const payload_token = data[0].unwrap();
            const expr_node = data[1];

            try self.pushScope();
            if (payload_token) |tok| self.shadowIfToken(tok);
            const used = try self.scanNode(@intFromEnum(expr_node));
            self.popScope();
            return used;
        }

        fn scanContainerDecl(self: *UsageScanner, node: u32) RuleError!bool {
            const tag = self.tags[node];
            switch (tag) {
                .container_decl, .container_decl_trailing => {
                    const container = self.tree.containerDecl(@enumFromInt(node));
                    return self.scanContainerDeclComponents(node, container);
                },
                .container_decl_two, .container_decl_two_trailing => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const container = self.tree.containerDeclTwo(&buf, @enumFromInt(node));
                    return self.scanContainerDeclComponents(node, container);
                },
                .container_decl_arg, .container_decl_arg_trailing => {
                    const container = self.tree.containerDeclArg(@enumFromInt(node));
                    return self.scanContainerDeclComponents(node, container);
                },
                .tagged_union, .tagged_union_trailing => {
                    const container = self.tree.taggedUnion(@enumFromInt(node));
                    return self.scanContainerDeclComponents(node, container);
                },
                .tagged_union_enum_tag, .tagged_union_enum_tag_trailing => {
                    const container = self.tree.taggedUnionEnumTag(@enumFromInt(node));
                    return self.scanContainerDeclComponents(node, container);
                },
                .tagged_union_two, .tagged_union_two_trailing => {
                    var buf: [2]std.zig.Ast.Node.Index = undefined;
                    const container = self.tree.taggedUnionTwo(&buf, @enumFromInt(node));
                    return self.scanContainerDeclComponents(node, container);
                },
                else => return false,
            }
        }

        fn scanContainerDeclComponents(
            self: *UsageScanner,
            node: u32,
            container: std.zig.Ast.full.ContainerDecl,
        ) RuleError!bool {
            if (container.ast.arg.unwrap()) |arg_node| {
                if (try self.scanNode(@intFromEnum(arg_node))) return true;
            }
            return self.scanContainerMembers(node, container.ast.members);
        }

        fn scanContainerMembers(
            self: *UsageScanner,
            container_node: u32,
            members: []const std.zig.Ast.Node.Index,
        ) RuleError!bool {
            try self.pushContainerScope(container_node);
            defer self.popContainerScope();

            try self.pushScope();
            defer self.popScope();

            if (self.owner_container == null or self.owner_container.? != container_node) {
                if (self.containerDeclaresName(members)) {
                    self.shadowed = true;
                }
            }
            return self.scanNodes(members);
        }

        fn containerDeclaresName(self: *UsageScanner, members: []const std.zig.Ast.Node.Index) bool {
            for (members) |member| {
                if (self.nodeDeclaresName(@intFromEnum(member))) return true;
            }
            return false;
        }

        fn nodeDeclaresName(self: *UsageScanner, node: u32) bool {
            const tag = self.tags[node];
            return switch (tag) {
                .simple_var_decl,
                .aligned_var_decl,
                .local_var_decl,
                .global_var_decl,
                => self.varDeclNameMatches(node),
                .fn_decl => blk: {
                    const data = self.datas[node];
                    const proto_node = @intFromEnum(data.node_and_node[0]);
                    break :blk self.fnProtoNameMatches(proto_node);
                },
                .fn_proto,
                .fn_proto_simple,
                .fn_proto_one,
                .fn_proto_multi,
                => self.fnProtoNameMatches(node),
                .assign_destructure => self.assignDestructureDeclaresName(node),
                else => false,
            };
        }

        fn assignDestructureDeclaresName(self: *UsageScanner, node: u32) bool {
            const destruct = self.tree.assignDestructure(@enumFromInt(node));
            for (destruct.ast.variables) |var_node| {
                if (self.varDeclNameMatches(@intFromEnum(var_node))) return true;
            }
            return false;
        }

        fn varDeclNameMatches(self: *UsageScanner, node: u32) bool {
            const full = self.tree.fullVarDecl(@enumFromInt(node)) orelse return false;
            const name_token = full.ast.mut_token + 1;
            if (name_token >= self.token_tags.len) return false;
            if (self.token_tags[name_token] != .identifier) return false;
            return self.isTokenName(name_token);
        }

        fn fnProtoNameMatches(self: *UsageScanner, node: u32) bool {
            const tag = self.tags[node];
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            return switch (tag) {
                .fn_proto => self.fnProtoNameMatchesImpl(self.tree.fnProto(@enumFromInt(node))),
                .fn_proto_simple => self.fnProtoNameMatchesImpl(self.tree.fnProtoSimple(&buffer, @enumFromInt(node))),
                .fn_proto_one => self.fnProtoNameMatchesImpl(self.tree.fnProtoOne(&buffer, @enumFromInt(node))),
                .fn_proto_multi => self.fnProtoNameMatchesImpl(self.tree.fnProtoMulti(@enumFromInt(node))),
                else => false,
            };
        }

        fn fnProtoNameMatchesImpl(self: *UsageScanner, proto: std.zig.Ast.full.FnProto) bool {
            const name_token = proto.name_token orelse return false;
            return self.isTokenName(name_token);
        }

        fn shadowIfToken(self: *UsageScanner, token: u32) void {
            if (token >= self.token_tags.len) return;
            switch (self.token_tags[token]) {
                .asterisk => {
                    const next = token + 1;
                    if (next < self.token_tags.len and self.token_tags[next] == .identifier) {
                        if (self.isTokenName(next)) {
                            self.shadowed = true;
                        }
                    }
                },
                .identifier => {
                    if (self.isTokenName(token)) {
                        self.shadowed = true;
                    }
                },
                else => {},
            }
        }

        fn shadowForPayload(self: *UsageScanner, token: u32) void {
            var idx = token;
            if (idx < self.token_tags.len and self.token_tags[idx] == .pipe) {
                idx += 1;
            }
            while (idx < self.token_tags.len) : (idx += 1) {
                const tag = self.token_tags[idx];
                if (tag == .pipe) break;
                if (tag == .identifier and self.isTokenName(idx)) {
                    self.shadowed = true;
                    return;
                }
                if (tag == .asterisk) {
                    const next = idx + 1;
                    if (next < self.token_tags.len and self.token_tags[next] == .identifier and self.isTokenName(next)) {
                        self.shadowed = true;
                        return;
                    }
                }
            }
        }

        fn isIdentifierUsed(self: *UsageScanner, node: u32) bool {
            if (self.owner_container != null and !self.inside_owner_container) return false;
            if (self.shadowed) return false;
            const token = self.main_tokens[node];
            return self.isTokenName(token);
        }

        fn isTokenName(self: *UsageScanner, token: u32) bool {
            if (token >= self.token_tags.len) return false;
            const slice = normalizeIdentifier(self.tree.tokenSlice(token));
            return std.mem.eql(u8, slice, self.normalized_name);
        }

        fn tokenMatchesSlice(self: *UsageScanner, token: u32, name: []const u8) bool {
            if (token >= self.token_tags.len) return false;
            const slice = normalizeIdentifier(self.tree.tokenSlice(token));
            return std.mem.eql(u8, slice, name);
        }

        fn accessHasOwnerName(self: *UsageScanner, node: u32, owner_name: []const u8) bool {
            if (node == 0 or node >= self.datas.len) return false;
            return switch (self.tags[node]) {
                .identifier => self.tokenMatchesSlice(self.main_tokens[node], owner_name),
                .field_access => blk: {
                    const data = self.datas[node];
                    const field_token = data.node_and_token[1];
                    if (self.tokenMatchesSlice(field_token, owner_name)) break :blk true;
                    break :blk self.accessHasOwnerName(@intFromEnum(data.node_and_token[0]), owner_name);
                },
                else => false,
            };
        }

        fn scanAstValuesForName(
            self: *UsageScanner,
            comptime T: type,
            inner: T,
            comptime fields: []const std.meta.FieldEnum(@TypeOf(inner.ast)),
        ) RuleError!bool {
            inline for (fields) |item| {
                const field_value = @field(inner.ast, @tagName(item));
                if (try self.scanNodeFromField(@TypeOf(field_value), field_value)) return true;
            }
            return false;
        }

        fn scanAstParentOpForName(
            self: *UsageScanner,
            comptime T: type,
            inner: T,
            comptime parent: std.meta.FieldEnum(@TypeOf(inner.ast)),
            comptime childs: @TypeOf(parent),
        ) RuleError!bool {
            const parent_value = @field(inner.ast, @tagName(parent));
            if (try self.scanNodeFromField(@TypeOf(parent_value), parent_value)) return true;
            const child_nodes = @field(inner.ast, @tagName(childs));
            return self.scanNodes(child_nodes);
        }

        fn scanNodeFromField(
            self: *UsageScanner,
            comptime FieldType: type,
            field_value: FieldType,
        ) RuleError!bool {
            if (FieldType == std.zig.Ast.Node.Index) {
                return self.scanNode(@intFromEnum(field_value));
            }
            if (FieldType == std.zig.Ast.Node.OptionalIndex) {
                if (field_value.unwrap()) |node| {
                    return self.scanNode(@intFromEnum(node));
                }
                return false;
            }
            return false;
        }
    };

    fn collectContainerNames(
        tree: *const std.zig.Ast,
        allocator: std.mem.Allocator,
        container_names: *std.AutoHashMap(u32, []const u8),
    ) RuleError!void {
        _ = allocator;
        const tags = tree.nodes.items(.tag);
        const token_tags = tree.tokens.items(.tag);
        for (tags, 0..) |tag, i| {
            switch (tag) {
                .simple_var_decl,
                .aligned_var_decl,
                .local_var_decl,
                .global_var_decl,
                => {
                    const node_idx: std.zig.Ast.Node.Index = @enumFromInt(i);
                    const full = tree.fullVarDecl(node_idx) orelse continue;
                    const name_token = full.ast.mut_token + 1;
                    if (name_token >= token_tags.len) continue;
                    if (token_tags[name_token] != .identifier) continue;
                    const name = normalizeIdentifier(tree.tokenSlice(name_token));

                    if (full.ast.init_node.unwrap()) |init_node| {
                        const init_tag = tags[@intFromEnum(init_node)];
                        if (isContainerTag(init_tag)) {
                            try container_names.put(@intFromEnum(init_node), name);
                        }
                    }
                },
                else => {},
            }
        }
    }

    fn isContainerTag(tag: std.zig.Ast.Node.Tag) bool {
        return switch (tag) {
            .container_decl,
            .container_decl_trailing,
            .container_decl_two,
            .container_decl_two_trailing,
            .container_decl_arg,
            .container_decl_arg_trailing,
            .tagged_union,
            .tagged_union_trailing,
            .tagged_union_enum_tag,
            .tagged_union_enum_tag_trailing,
            .tagged_union_two,
            .tagged_union_two_trailing,
            => true,
            else => false,
        };
    }
};

fn expectSingleUnusedDecl(code: [:0]const u8, expected_name: []const u8) !void {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "skript-regression.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try UnusedDeclRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, expected_name) != null);
}

test "skript regression: result-location method calls use private declarations" {
    const code: [:0]const u8 =
        \\pub const Query = struct {
        \\    value: u32,
        \\    fn submit(value: u32) Query {
        \\        return .{ .value = value };
        \\    }
        \\    fn genuinelyUnused() Query {
        \\        return .{ .value = 0 };
        \\    }
        \\};
        \\pub fn makeQuery() Query {
        \\    return .submit(1);
        \\}
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "contextual constants match the file container without promoting nested homonyms" {
    const code: [:0]const u8 =
        "const Self = @This();\n" ++
        "const empty: Self = .{};\n" ++
        "pub const Other = struct {\n" ++
        "    const empty: @This() = .{};\n" ++
        "};\n" ++
        "pub fn make() Self { return .empty; }\n";
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "contextual-constant.zig", code);
    defer source.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try UnusedDeclRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqual(@as(usize, 4), diagnostics.items[0].range.start.line);
}

test "skript regression: refAllDecls reaches private container declarations" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\pub const Reflected = struct {
        \\    fn reachedOnlyByReflection() void {}
        \\    test {
        \\        comptime {
        \\            std.testing.refAllDecls(@This());
        \\        }
        \\    }
        \\};
        \\pub const Ordinary = struct {
        \\    fn genuinelyUnused() void {}
        \\};
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "skript residual: typed file receiver reaches private method" {
    const code: [:0]const u8 =
        \\const Reader = @This();
        \\fn finalizeSlocTable(self: *Reader) !void {
        \\    _ = self;
        \\}
        \\fn genuinelyUnused() void {}
        \\pub fn readUnit() !void {
        \\    var reader: Reader = .{};
        \\    try reader.finalizeSlocTable();
        \\}
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "skript residual: call argument result location reaches private method" {
    const code: [:0]const u8 =
        \\pub const Query = struct {
        \\    value: u32,
        \\    fn submit(value: u32) Query {
        \\        return .{ .value = value };
        \\    }
        \\    fn genuinelyUnused() Query {
        \\        return .{ .value = 0 };
        \\    }
        \\};
        \\const History = struct {
        \\    fn add(self: *History, query: Query) void {
        \\        _ = self;
        \\        _ = query;
        \\    }
        \\};
        \\pub fn record(history: *History) void {
        \\    history.add(.submit(1));
        \\}
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "skript residual: typed receiver rejects homonymous root method" {
    const code: [:0]const u8 =
        \\const Reader = @This();
        \\const Other = struct {
        \\    fn finalizeSlocTable(self: *Other) !void {
        \\        _ = self;
        \\    }
        \\};
        \\fn finalizeSlocTable(self: *Reader) !void {
        \\    _ = self;
        \\}
        \\pub fn readUnit(other: *Other) !void {
        \\    try other.finalizeSlocTable();
        \\}
    ;

    try expectSingleUnusedDecl(code, "finalizeSlocTable");
}

test "skript control: shadowed local type rejects root receiver method" {
    const code: [:0]const u8 =
        \\const Reader = @This();
        \\const Other = struct {};
        \\fn finalizeSlocTable(self: *Reader) !void {
        \\    _ = self;
        \\}
        \\pub fn readUnit() !void {
        \\    const Reader = Other;
        \\    var reader: Reader = .{};
        \\    try reader.finalizeSlocTable();
        \\}
    ;

    try expectSingleUnusedDecl(code, "finalizeSlocTable");
}

test "skript regression: Ast root receiver calls use consume and parseFile" {
    const code: [:0]const u8 =
        \\const Ast = @This();
        \\fn consume(_: *Ast, pos: *usize, n: usize) void {
        \\    pos.* += n;
        \\}
        \\fn parseFile(self: *Ast, pos: *usize) void {
        \\    _ = self;
        \\    _ = pos;
        \\}
        \\fn eatExpected(self: *Ast, pos: *usize) void {
        \\    self.consume(pos, 1);
        \\}
        \\pub fn create(self: *Ast, pos: *usize) void {
        \\    self.parseFile(pos);
        \\    self.eatExpected(pos);
        \\}
        \\fn genuinelyUnused() void {}
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "skript regression: EvalHeap alias receiver call uses checkOwner" {
    const code: [:0]const u8 =
        \\const Self = @This();
        \\pub const Heap = Self;
        \\fn checkOwner(self: *Heap) void {
        \\    _ = self;
        \\}
        \\pub fn importValue(self: *Heap) void {
        \\    self.checkOwner();
        \\}
        \\fn genuinelyUnused() void {}
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "skript regression: allocator-created Store uses rawAllocator and retainRaw" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const MemAllocator = std.mem.Allocator;
        \\const Store = @This();
        \\pub fn init(base_alloc: MemAllocator) !*Store {
        \\    const self = try base_alloc.create(Store);
        \\    _ = self.rawAllocator();
        \\    try self.retainRaw(1);
        \\    return self;
        \\}
        \\fn rawAllocator(self: *Store) void {
        \\    _ = self;
        \\}
        \\fn retainRaw(self: *Store, bytes: usize) !void {
        \\    _ = self;
        \\    _ = bytes;
        \\}
        \\fn genuinelyUnused() void {}
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "skript regression: receiver field gives shorthand submit its Query result type" {
    const code: [:0]const u8 =
        \\pub const Query = struct {
        \\    value: u32,
        \\    fn submit(value: u32) Query {
        \\        return .{ .value = value };
        \\    }
        \\    fn genuinelyUnused() Query {
        \\        return .{ .value = 0 };
        \\    }
        \\};
        \\const History = struct {
        \\    pub fn add(_: *History, _: Query, _: u32) void {}
        \\};
        \\const Model = struct {
        \\    history: History,
        \\    pub fn doEvaluate(self: *Model) void {
        \\        self.history.add(.submit(1), 0);
        \\    }
        \\};
        \\pub fn run(model: *Model) void {
        \\    model.doEvaluate();
        \\}
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "skript control: homonymous factory create keeps its declared return type" {
    const code: [:0]const u8 =
        \\const Store = @This();
        \\const Other = struct {
        \\    fn rawAllocator(_: *Other) void {}
        \\};
        \\const Factory = struct {
        \\    fn create(_: Factory, comptime T: type) *Other {
        \\        _ = T;
        \\        return undefined;
        \\    }
        \\};
        \\fn rawAllocator(self: *Store) void {
        \\    _ = self;
        \\}
        \\pub fn init(factory: Factory) void {
        \\    const self = factory.create(Store);
        \\    self.rawAllocator();
        \\}
    ;

    try expectSingleUnusedDecl(code, "rawAllocator");
}

test "skript control: nonmatching result location rejects homonymous submit" {
    const code: [:0]const u8 =
        \\pub const Query = struct {
        \\    fn submit() Query {
        \\        return .{};
        \\    }
        \\};
        \\pub const OtherQuery = struct {
        \\    pub fn submit() OtherQuery {
        \\        return .{};
        \\    }
        \\};
        \\const History = struct {
        \\    pub fn add(_: *History, _: OtherQuery) void {}
        \\};
        \\const Model = struct {
        \\    history: History,
        \\    pub fn doEvaluate(self: *Model) void {
        \\        self.history.add(.submit());
        \\    }
        \\};
        \\pub fn run(model: *Model) void {
        \\    model.doEvaluate();
        \\}
    ;

    try expectSingleUnusedDecl(code, "submit");
}

test "skript control: unknown receiver type is not method identity proof" {
    const code: [:0]const u8 =
        \\const Heap = @This();
        \\fn checkOwner(self: *Heap) void {
        \\    _ = self;
        \\}
        \\pub fn importValue(receiver: anytype) void {
        \\    receiver.checkOwner();
        \\}
    ;

    try expectSingleUnusedDecl(code, "checkOwner");
}

test "skript regression: array receiver reaches root method" {
    const code: [:0]const u8 =
        \\const Site = @This();
        \\fn captures(self: *Site) void {
        \\    _ = self;
        \\}
        \\pub fn run(sites: []Site) void {
        \\    sites[0].captures();
        \\}
        \\fn genuinelyUnused() void {}
    ;

    try expectSingleUnusedDecl(code, "genuinelyUnused");
}

test "skript control: array receiver type mismatch rejects root method" {
    const code: [:0]const u8 =
        \\const Site = @This();
        \\const Other = struct {};
        \\fn captures(self: *Site) void {
        \\    _ = self;
        \\}
        \\pub fn run(sites: []Other) void {
        \\    sites[0].captures();
        \\}
    ;

    try expectSingleUnusedDecl(code, "captures");
}

test "contextual shorthand distinguishes same-named nested containers" {
    const code: [:0]const u8 =
        \\pub const Left = struct {
        \\    pub const Item = struct {
        \\        fn submit() Item { return .{}; }
        \\    };
        \\};
        \\pub const Right = struct {
        \\    pub const Item = struct {
        \\        fn submit() Item { return .{}; }
        \\    };
        \\};
        \\const Sink = struct {
        \\    fn add(_: Sink, _: Left.Item) void {}
        \\};
        \\pub fn run(sink: Sink) void {
        \\    sink.add(.submit());
        \\    _ = @sizeOf(Right.Item);
        \\}
    ;
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "contextual-method.zig", code);
    defer source.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try UnusedDeclRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqual(@as(usize, 8), diagnostics.items[0].range.start.line);
}

test "self-called private method counts as used" {
    const code: [:0]const u8 =
        \\const Adapter = @This();
        \\value: usize,
        \\fn bump(self: *Adapter) usize {
        \\    return self.value + 1;
        \\}
        \\pub fn run(self: *Adapter) usize {
        \\    return self.bump();
        \\}
    ;
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "self-called-method.zig", code);
    defer source.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try UnusedDeclRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "same-named field read does not mark method used" {
    const code: [:0]const u8 =
        \\const A = struct {
        \\    bump: u32,
        \\    pub fn get(self: *A) u32 {
        \\        return self.bump;
        \\    }
        \\};
        \\const B = struct {
        \\    fn bump(self: *B) u32 {
        \\        _ = self;
        \\        return 1;
        \\    }
        \\    pub fn go(self: *B) u32 {
        \\        _ = self;
        \\        return 0;
        \\    }
        \\};
        \\pub fn main() void {
        \\    var a: A = .{ .bump = 3 };
        \\    var b: B = .{};
        \\    const x: u32 = a.get() + b.go();
        \\    _ = x;
        \\}
    ;
    try expectSingleUnusedDecl(code, "bump");
}

test "indexed declaration references retain parameter and local shadowing" {
    try expectSingleUnusedDecl(
        \\const hidden = 1;
        \\const Visible = u32;
        \\pub fn run(hidden: Visible) Visible {
        \\    _ = hidden;
        \\    { const hidden = 2; _ = hidden; }
        \\    return 0;
        \\}
    , "hidden");
}

test "indexed declaration references retain nested signatures and initializers" {
    try expectSingleUnusedDecl(
        \\const Parameter = u32;
        \\const Return = u64;
        \\const Value = u8;
        \\const unused = 1;
        \\pub const Namespace = struct {
        \\    pub fn run(_: Parameter) Return {
        \\        const value: Value = 0;
        \\        return value;
        \\    }
        \\};
    , "unused");
}

test "anonymous struct namespace reference counts as used" {
    const code: [:0]const u8 =
        \\const Handler = struct {
        \\    dispatch: *const fn (state: *Handler, event: u32) bool,
        \\    state: u32,
        \\    pub fn init() Handler {
        \\        return .{
        \\            .dispatch = struct {
        \\                fn call(ptr: *Handler, event: u32) bool {
        \\                    ptr.state += event;
        \\                    return true;
        \\                }
        \\            }.call,
        \\            .state = 0,
        \\        };
        \\    }
        \\};
        \\pub fn main() void {
        \\    var handler = Handler.init();
        \\    _ = handler.dispatch(&handler, 1);
        \\}
    ;
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "anonymous-namespace.zig", code);
    defer source.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try UnusedDeclRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}
