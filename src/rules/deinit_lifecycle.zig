const std = @import("std");
const Rule = @import("../rule.zig").Rule;
const Source = @import("../source.zig").Source;
const Diagnostic = @import("../diagnostic.zig").Diagnostic;
const RuleError = @import("../rule.zig").RuleError;
const ast_walk = @import("../ast_walk.zig");
const call_utils = @import("../analysis/call_utils.zig");

const Ast = std.zig.Ast;

pub const DeinitLifecycleRule = struct {
    pub const rule: Rule = .{
        .name = "deinit-lifecycle",
        .default_severity = .warning,
        .checkFn = check,
    };

    const DeferredCleanup = struct {
        call: MethodCall,
        has_defer: bool = false,
        has_errdefer: bool = false,
        defer_stmt: ?u32 = null,
        errdefer_stmt: ?u32 = null,
    };

    const MethodCall = struct {
        receiver: []const u8,
        method: []const u8,
        resource: ?[]const u8 = null,

        fn eql(a: MethodCall, b: MethodCall) bool {
            if (!std.mem.eql(u8, a.receiver, b.receiver)) return false;
            if (!std.mem.eql(u8, a.method, b.method)) return false;

            if (a.resource) |resource| {
                const other_resource = b.resource orelse return false;
                return std.mem.eql(u8, resource, other_resource);
            }
            return b.resource == null;
        }

        fn cleanedResource(call: MethodCall) []const u8 {
            return call.resource orelse call.receiver;
        }
    };

    const cleanup_methods = [_][]const u8{
        "deinit",
        "close",
        "destroy",
        "release",
        "free",
        "reset",
        "clear",
        "clearAndFree",
        "cancel",
        "stop",
        "join",
    };

    fn check(src: *Source, allocator: std.mem.Allocator, diagnostics: *std.ArrayList(Diagnostic)) RuleError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);

        var identity_arena = std.heap.ArenaAllocator.init(allocator);
        defer identity_arena.deinit();

        var scanner = Scanner{
            .src = src,
            .tree = tree,
            .tags = tags,
            .datas = datas,
            .allocator = allocator,
            .identity_allocator = identity_arena.allocator(),
            .diagnostics = diagnostics,
            .active_cleanups = .empty,
        };
        defer scanner.active_cleanups.deinit(allocator);

        for (tags, 0..) |tag, i| {
            switch (tag) {
                .fn_decl => {
                    const body = @intFromEnum(datas[i].node_and_node[1]);
                    if (body != 0) {
                        try scanner.scanNode(@intCast(body));
                    }
                },
                .test_decl => {
                    const body = @intFromEnum(datas[i].opt_token_and_node[1]);
                    if (body != 0) {
                        try scanner.scanNode(@intCast(body));
                    }
                },
                else => {},
            }
        }
    }

    const Scanner = struct {
        src: *Source,
        tree: *const Ast,
        tags: []const Ast.Node.Tag,
        datas: []const Ast.Node.Data,
        allocator: std.mem.Allocator,
        identity_allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        active_cleanups: std.ArrayList(MethodCall),

        fn scanNode(self: *Scanner, node: u32) RuleError!void {
            if (node == 0 or node >= self.tags.len) return;

            switch (self.tags[node]) {
                .fn_decl, .test_decl => return,
                .block, .block_semicolon, .block_two, .block_two_semicolon => try self.scanBlock(node),
                else => {
                    const child = struct {
                        fn visit(_: *const Ast, child_node: u32, scanner: *Scanner) RuleError!void {
                            try scanner.scanNode(child_node);
                        }
                    };
                    try ast_walk.walkChildren(Scanner, self.tree, node, self, child.visit);
                },
            }
        }

        fn scanBlock(self: *Scanner, block_node: u32) RuleError!void {
            var scratch: [2]u32 = undefined;
            const statements = self.blockStatements(block_node, &scratch);
            if (statements.len == 0) return;

            var deferred_cleanups: std.ArrayList(DeferredCleanup) = .empty;
            defer deferred_cleanups.deinit(self.allocator);

            for (statements) |stmt| {
                const is_defer = switch (self.tags[stmt]) {
                    .@"defer" => true,
                    .@"errdefer" => false,
                    else => continue,
                };

                if (try self.extractDeferredMethodCall(stmt)) |call| {
                    if (!isCleanupMethod(call.method)) continue;
                    try self.recordDeferredCleanup(
                        &deferred_cleanups,
                        call,
                        stmt,
                        is_defer,
                    );
                }
            }

            try self.reportDuplicateDeferredCleanup(deferred_cleanups.items);

            const active_base = self.active_cleanups.items.len;
            defer self.active_cleanups.shrinkRetainingCapacity(active_base);

            for (statements, 0..) |stmt, idx| {
                switch (self.tags[stmt]) {
                    .@"defer", .@"errdefer" => {
                        if (try self.extractDeferredMethodCall(stmt)) |call| {
                            if (isCleanupMethod(call.method) and !self.hasActiveCleanup(call)) {
                                try self.active_cleanups.append(self.allocator, call);
                            }
                        }
                    },
                    else => {},
                }

                if (try self.extractDirectCleanupCall(stmt)) |call| {
                    if (self.hasActiveCleanup(call) and
                        (try self.findTryReinit(
                            statements[idx + 1 ..],
                            call.cleanedResource(),
                        )) != null)
                    {
                        try self.emitCleanupBeforeTryReinit(stmt, call);
                    }
                }

                try self.scanNode(stmt);
            }
        }

        fn blockStatements(self: *const Scanner, block_node: u32, scratch: *[2]u32) []const u32 {
            switch (self.tags[block_node]) {
                .block, .block_semicolon => {
                    const range = self.datas[block_node].extra_range;
                    const start = @intFromEnum(range.start);
                    const end = @intFromEnum(range.end);
                    return self.tree.extra_data[start..end];
                },
                .block_two, .block_two_semicolon => {
                    const nodes = self.datas[block_node].opt_node_and_opt_node;
                    var count: usize = 0;
                    if (nodes[0].unwrap()) |n| {
                        scratch[count] = @intFromEnum(n);
                        count += 1;
                    }
                    if (nodes[1].unwrap()) |n| {
                        scratch[count] = @intFromEnum(n);
                        count += 1;
                    }
                    return scratch[0..count];
                },
                else => return &.{},
            }
        }

        fn extractDeferredMethodCall(self: *const Scanner, stmt: u32) RuleError!?MethodCall {
            const body: u32 = switch (self.tags[stmt]) {
                .@"defer" => @intFromEnum(self.datas[stmt].node),
                .@"errdefer" => @intFromEnum(self.datas[stmt].opt_token_and_node[1]),
                else => return null,
            };
            if (body == 0 or body >= self.tags.len) return null;

            if (try self.extractMethodCall(body)) |call| return call;

            if (self.tags[body] == .block or self.tags[body] == .block_semicolon or
                self.tags[body] == .block_two or self.tags[body] == .block_two_semicolon)
            {
                var scratch: [2]u32 = undefined;
                const statements = self.blockStatements(body, &scratch);
                if (statements.len == 1) {
                    return try self.extractMethodCall(statements[0]);
                }
            }

            return null;
        }

        fn extractDirectCleanupCall(self: *const Scanner, stmt: u32) RuleError!?MethodCall {
            const call = (try self.extractMethodCall(stmt)) orelse return null;
            if (!isCleanupMethod(call.method)) return null;
            return call;
        }

        fn extractMethodCall(self: *const Scanner, expr_node: u32) RuleError!?MethodCall {
            if (expr_node >= self.tags.len) return null;
            if (!call_utils.isCallNode(self.tags[expr_node])) return null;

            var call_buf: [1]Ast.Node.Index = undefined;
            const full_call = self.tree.fullCall(&call_buf, @enumFromInt(expr_node)) orelse return null;
            const callee = @intFromEnum(full_call.ast.fn_expr);
            if (callee == 0 or callee >= self.tags.len or self.tags[callee] != .field_access) return null;

            const token_tags = self.tree.tokens.items(.tag);
            const field_access = self.datas[callee].node_and_token;
            const receiver_node = @intFromEnum(field_access[0]);
            const method_token = field_access[1];

            if (method_token >= token_tags.len or token_tags[method_token] != .identifier) return null;
            if (receiver_node == 0 or receiver_node >= self.tags.len) return null;
            const receiver = (try self.canonicalReceiver(receiver_node)) orelse return null;
            const method = self.tree.tokenSlice(method_token);
            const resource = if (cleanupMethodUsesResourceArgument(method) and
                full_call.ast.params.len > 0)
                (try self.canonicalResource(
                    @intFromEnum(full_call.ast.params[0]),
                )) orelse return null
            else
                null;

            return .{
                .receiver = receiver,
                .method = method,
                .resource = resource,
            };
        }

        fn canonicalReceiver(self: *const Scanner, receiver_node: u32) RuleError!?[]const u8 {
            const token_tags = self.tree.tokens.items(.tag);
            const main_tokens = self.tree.nodes.items(.main_token);

            var parts: [32][]const u8 = undefined;
            var part_count: usize = 0;
            var node = receiver_node;

            while (true) {
                if (node == 0 or node >= self.tags.len) return null;
                switch (self.tags[node]) {
                    .identifier => {
                        const token = main_tokens[node];
                        if (token >= token_tags.len or token_tags[token] != .identifier) return null;
                        if (part_count >= parts.len) return null;
                        parts[part_count] = self.tree.tokenSlice(token);
                        part_count += 1;
                        break;
                    },
                    .field_access => {
                        const field_access = self.datas[node].node_and_token;
                        const field_token = field_access[1];
                        if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return null;
                        if (part_count >= parts.len) return null;
                        parts[part_count] = self.tree.tokenSlice(field_token);
                        part_count += 1;
                        node = @intFromEnum(field_access[0]);
                    },
                    else => return null,
                }
            }

            var canonical: std.ArrayList(u8) = .empty;
            errdefer canonical.deinit(self.identity_allocator);

            var idx = part_count;
            while (idx > 0) : (idx -= 1) {
                if (canonical.items.len > 0) try canonical.append(self.identity_allocator, '.');
                try canonical.appendSlice(self.identity_allocator, parts[idx - 1]);
            }

            return try canonical.toOwnedSlice(self.identity_allocator);
        }

        fn canonicalResource(self: *const Scanner, resource_node: u32) RuleError!?[]const u8 {
            if (try self.canonicalReceiver(resource_node)) |resource| return resource;
            if (resource_node == 0 or resource_node >= self.tags.len) return null;

            const token_tags = self.tree.tokens.items(.tag);
            const first_token = self.tree.firstToken(@enumFromInt(resource_node));
            const last_token = self.tree.lastToken(@enumFromInt(resource_node));
            if (first_token > last_token or last_token >= token_tags.len) return null;

            var canonical: std.ArrayList(u8) = .empty;
            errdefer canonical.deinit(self.identity_allocator);

            var token = first_token;
            while (token <= last_token) : (token += 1) {
                try canonical.appendSlice(self.identity_allocator, self.tree.tokenSlice(token));
            }
            return try canonical.toOwnedSlice(self.identity_allocator);
        }

        fn recordDeferredCleanup(
            self: *Scanner,
            cleanups: *std.ArrayList(DeferredCleanup),
            call: MethodCall,
            stmt: u32,
            is_defer: bool,
        ) RuleError!void {
            for (cleanups.items) |*cleanup| {
                if (cleanup.call.eql(call)) {
                    if (is_defer) {
                        cleanup.has_defer = true;
                        if (cleanup.defer_stmt == null) cleanup.defer_stmt = stmt;
                    } else {
                        cleanup.has_errdefer = true;
                        if (cleanup.errdefer_stmt == null) cleanup.errdefer_stmt = stmt;
                    }
                    return;
                }
            }

            var cleanup = DeferredCleanup{ .call = call };
            if (is_defer) {
                cleanup.has_defer = true;
                cleanup.defer_stmt = stmt;
            } else {
                cleanup.has_errdefer = true;
                cleanup.errdefer_stmt = stmt;
            }
            try cleanups.append(self.allocator, cleanup);
        }

        fn reportDuplicateDeferredCleanup(
            self: *Scanner,
            cleanups: []const DeferredCleanup,
        ) RuleError!void {
            for (cleanups) |cleanup| {
                if (!(cleanup.has_defer and cleanup.has_errdefer)) continue;
                const report_stmt = cleanup.errdefer_stmt orelse cleanup.defer_stmt orelse continue;
                try self.emitDuplicateDeferredCleanup(report_stmt, cleanup.call);
            }
        }

        fn hasActiveCleanup(self: *const Scanner, call: MethodCall) bool {
            for (self.active_cleanups.items) |active| {
                if (active.eql(call)) return true;
            }
            return false;
        }

        fn findTryReinit(
            self: *const Scanner,
            statements: []const u32,
            resource: []const u8,
        ) RuleError!?u32 {
            for (statements) |stmt| {
                if (try self.assignmentToResourceIsTry(stmt, resource)) |is_try| {
                    return if (is_try) stmt else null;
                }
            }
            return null;
        }

        fn assignmentToResourceIsTry(
            self: *const Scanner,
            stmt: u32,
            resource: []const u8,
        ) RuleError!?bool {
            if (stmt >= self.tags.len or !isAssignTag(self.tags[stmt])) return null;

            const pair = self.datas[stmt].node_and_node;
            const lhs = @intFromEnum(pair[0]);
            const rhs = @intFromEnum(pair[1]);
            if (lhs == 0 or lhs >= self.tags.len) return null;

            const lhs_resource = (try self.canonicalResource(lhs)) orelse return null;
            if (!std.mem.eql(u8, lhs_resource, resource)) return null;

            if (rhs == 0 or rhs >= self.tags.len) return false;
            return self.tags[rhs] == .@"try";
        }

        fn emitDuplicateDeferredCleanup(
            self: *Scanner,
            stmt: u32,
            call: MethodCall,
        ) RuleError!void {
            const loc = try self.src.tokenLocation(self.tree.nodes.items(.main_token)[stmt]);
            const message = if (call.resource) |resource|
                try std.fmt.allocPrint(
                    self.allocator,
                    "'{s}.{s}({s})' is registered in both defer and errdefer within the same scope; this can run cleanup twice on error unwind",
                    .{ call.receiver, call.method, resource },
                )
            else
                try std.fmt.allocPrint(
                    self.allocator,
                    "'{s}.{s}' is registered in both defer and errdefer within the same scope; this can run cleanup twice on error unwind",
                    .{ call.receiver, call.method },
                );
            defer self.allocator.free(message);

            const diag = try Diagnostic.initAtLocation(
                self.allocator,
                self.src.getFilePath(),
                rule.name,
                .warning,
                message,
                loc.line,
                loc.column,
            );
            try self.diagnostics.append(self.allocator, diag);
        }

        fn emitCleanupBeforeTryReinit(
            self: *Scanner,
            stmt: u32,
            call: MethodCall,
        ) RuleError!void {
            const loc = try self.src.tokenLocation(self.tree.nodes.items(.main_token)[stmt]);
            const message = if (call.resource) |resource|
                try std.fmt.allocPrint(
                    self.allocator,
                    "'{s}.{s}({s})' appears before a fallible reinitialization while deferred cleanup is active; error unwind may call '{s}.{s}({s})' twice",
                    .{
                        call.receiver,
                        call.method,
                        resource,
                        call.receiver,
                        call.method,
                        resource,
                    },
                )
            else
                try std.fmt.allocPrint(
                    self.allocator,
                    "'{s}.{s}()' appears before a fallible reinitialization while deferred cleanup is active; error unwind may call '{s}.{s}()' twice",
                    .{ call.receiver, call.method, call.receiver, call.method },
                );
            defer self.allocator.free(message);

            const diag = try Diagnostic.initAtLocation(
                self.allocator,
                self.src.getFilePath(),
                rule.name,
                .hint,
                message,
                loc.line,
                loc.column,
            );
            try self.diagnostics.append(self.allocator, diag);
        }
    };

    fn isCleanupMethod(method: []const u8) bool {
        for (cleanup_methods) |known_method| {
            if (std.mem.eql(u8, method, known_method)) return true;
        }
        return false;
    }

    fn cleanupMethodUsesResourceArgument(method: []const u8) bool {
        return std.mem.eql(u8, method, "free") or std.mem.eql(u8, method, "destroy");
    }

    fn isAssignTag(tag: Ast.Node.Tag) bool {
        return switch (tag) {
            .assign,
            .assign_mul,
            .assign_div,
            .assign_mod,
            .assign_add,
            .assign_sub,
            .assign_shl,
            .assign_shl_sat,
            .assign_shr,
            .assign_bit_and,
            .assign_bit_xor,
            .assign_bit_or,
            .assign_mul_wrap,
            .assign_add_wrap,
            .assign_sub_wrap,
            .assign_mul_sat,
            .assign_add_sat,
            .assign_sub_sat,
            => true,
            else => false,
        };
    }
};
