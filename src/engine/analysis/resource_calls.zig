const std = @import("std");
const call_utils = @import("../../analysis/call_utils.zig");
const allocator_utils = @import("../../analysis/allocator_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
const ast_walk = @import("../../ast_walk.zig");
const ids = @import("../../ids.zig");
const Source = @import("../../source.zig").Source;
const LexicalIndex = @import("../../analysis/lexical_index.zig").LexicalIndex;
const QueryContext = @import("../../checkers/optional_unwrap/bindings.zig").QueryContext;

pub fn Mixin(comptime _Engine: type) type {
    return struct {
        const ResourceCallKind = enum {
            alloc,
            realloc,
            free,
            free_owned,
            open,
            close,
        };

        /// Which arm of a `catch` expression produced a value.
        ///
        /// A guarded call that fails does not leave the binding empty: its
        /// handler runs instead and the binding takes the handler's fallback,
        /// which may be an open, an allocation, or a handle this frame
        /// already holds. So the expression a `catch` fills a binding with
        /// depends on which arm ran, and each arm has its own expression.
        const CatchArm = enum {
            /// Not a `catch` expression, or an arm nothing is known about.
            none,
            /// The primary: the guarded call succeeded.
            success,
            /// The handler: the guarded call failed and the fallback ran.
            failure,
        };

        pub const ResourceCall = struct {
            kind: ResourceCallKind,
            target_expr: ?u32,
            call_node: u32,
        };

        /// The expression a `catch` expression filled its binding with on
        /// `arm`, or null when that arm handed over nothing to resolve.
        ///
        /// `.success` yields the primary - the guarded call ran and produced
        /// the value. `.failure` yields the handler's fallback, following a
        /// labeled block down to the operand its `break :label` carries out:
        /// a handler written `catch blk: { ...; break :blk fallback; }`
        /// acquired that value inside the block, so the block is only a
        /// wrapper around it. `.none` yields the expression unchanged, which
        /// is what every binding outside a `catch` wants.
        pub fn catchArmValueExpr(
            self: *_Engine,
            tree: *const std.zig.Ast,
            expr_node: u32,
            arm: CatchArm,
        ) ?u32 {
            _ = self;
            const tags = tree.nodes.items(.tag);
            if (expr_node >= tags.len or tags[expr_node] != .@"catch") return expr_node;
            const pair = tree.nodes.items(.data)[expr_node].node_and_node;
            return switch (arm) {
                .success => @intFromEnum(pair[0]),
                .failure => failureValueExpr(tree, @intFromEnum(pair[1]), catch_failure_value_frames),
                .none => expr_node,
            };
        }

        /// Bound on the labeled-block walk: deep enough for the nesting a
        /// handler is written with, and no deeper. A chain past it answers
        /// null rather than naming a value it never reached.
        const catch_failure_value_frames: u8 = 32;

        /// The value a `catch` handler's fallback expression carries, or the
        /// expression itself when it is already one.
        fn failureValueExpr(tree: *const std.zig.Ast, node: u32, depth: u8) ?u32 {
            if (depth == 0 or node >= tree.nodes.len) return null;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            return switch (tags[node]) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => blk: {
                    var scratch: [2]u32 = undefined;
                    const statements = blockStatements(tree, tags, datas, node, &scratch) orelse break :blk null;
                    if (statements.len == 0) break :blk null;
                    break :blk failureValueExpr(tree, statements[statements.len - 1], depth - 1);
                },
                .@"break" => blk: {
                    const pair = datas[node].opt_token_and_opt_node;
                    // An unlabeled break leaves a loop or switch, which this
                    // fallback is not written in; only a labeled one names
                    // the value the block hands out.
                    if (pair[0] == .none) break :blk null;
                    const operand = pair[1].unwrap() orelse break :blk null;
                    break :blk @intFromEnum(operand);
                },
                else => node,
            };
        }

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
                    // `realloc` reuses the allocation behind its first
                    // argument, so the call is an allocation and the previous
                    // pointer is what it releases. Without an argument there
                    // is nothing to reuse, so this is not one.
                    if (std.mem.eql(u8, call_info.method_name, "realloc")) {
                        if (first_arg) |arg_node| {
                            return .{ .kind = .realloc, .target_expr = arg_node, .call_node = call_ast_node };
                        }
                    }
                }
            }

            // An arena owns everything allocated through its allocator and
            // `deinit` releases the arena itself. Classified from the proven
            // arena type, so a `deinit` on any other value is untouched. Sits
            // after the configured models and the allocator methods above, and
            // before type-based open detection.
            //
            // The proof is about a binding, and a binding the frame writes
            // over holds something else by the time this call runs, so the
            // release stands only while the binding is still the one the
            // declared type or the constructor described.
            if (call_info.base_node) |base_node| {
                if (std.mem.eql(u8, call_info.method_name, "deinit")) {
                    if (allocator_utils.isArenaAllocatorExpr(tree, self.type_context, base_node) and
                        arenaReceiverIsStable(self, tree, base_node))
                    {
                        return .{ .kind = .free_owned, .target_expr = base_node, .call_node = call_ast_node };
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
                if (call_info.base_node) |base_node| {
                    // Pre-0.16 `std.fs` handles close the receiver directly;
                    // Zig 0.16 `std.Io` handles close it through `io`.
                    const closes_bare_receiver = first_arg == null and
                        isKnownResourceType(call_info.receiver_type);
                    const closes_through_io = call_info.param_count == 1 and
                        ioCloseReceiver(self, tree, base_node) != null;
                    if (closes_bare_receiver or closes_through_io) {
                        // A guard's payload capture names the value its
                        // condition carried, and the open is recorded against
                        // that condition's own binding. Releasing the capture
                        // instead closes a region the acquisition was never
                        // tracked on, so the release is named after the
                        // condition - found by the same capture climb that
                        // proved the receiver carries a handle at all. A
                        // receiver that is no capture this file can attribute,
                        // and a pre-0.16 receiver proven by its own
                        // annotation, are left spelled as they were written.
                        const target: u32 = if (closes_through_io)
                            (payloadCaptureCondition(self, tree, base_node) orelse base_node)
                        else
                            base_node;
                        return .{ .kind = .close, .target_expr = target, .call_node = call_ast_node };
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

            // A wrapper that closes the resource it is handed releases the
            // caller's argument just as `<arg>.close()` does. The callee is
            // proven from its body, never from its spelling, so this runs last.
            if (call_info.param_count > 0) {
                if (releasedByCalleeBody(self, tree, call_ast_node)) |arg_node| {
                    return .{ .kind = .close, .target_expr = arg_node, .call_node = call_ast_node };
                }
            }
            return null;
        }

        /// True when nothing in the frame `receiver_node` sits in writes the
        /// binding it names again.
        ///
        /// Both arena proofs read the value a binding holds where an
        /// allocation happens: the charge decides whether a block belongs to
        /// the arena, this release decides whether the arena settles what it
        /// holds. A binding the frame writes over holds something else by then,
        /// so neither the type it was declared with nor the constructor it ran
        /// with speaks for the value the call runs on, and a `deinit` queued
        /// against the name settles nothing.
        ///
        /// The frame is the boundary: a same-named binding of another function
        /// and a write to a field of a same-named value are both someone
        /// else's. A receiver that is not a plain binding names no variable to
        /// write over, and is left as it was classified.
        fn arenaReceiverIsStable(self: *_Engine, tree: *const std.zig.Ast, receiver_node: u32) bool {
            const tags = tree.nodes.items(.tag);
            if (receiver_node >= tags.len or tags[receiver_node] != .identifier) return true;
            const parent_map = self.getParentMap(tree) catch return false;
            const frame = enclosingCallable(tags, parent_map, receiver_node) orelse return false;
            const resolver = (_Engine.VarResolution.getOrBuildVarResolver(self, ids.astId(frame)) catch
                return false) orelse return false;
            const receiver = resolver.resolve(receiver_node) orelse return false;

            const datas = tree.nodes.items(.data);
            for (tags, 0..) |tag, index| {
                if (!writesItsLeftSide(tag)) continue;
                const node: u32 = @intCast(index);
                if (!ast_walk.isAncestor(frame, node, parent_map)) continue;
                const lhs: u32 = @intFromEnum(datas[node].node_and_node[0]);
                if (lhs >= tags.len or tags[lhs] != .identifier) continue;
                // Both sides are named by the frame's own resolver, so a
                // shadowing local of the same spelling is someone else's write
                // and a same-named binding of another frame is never read here
                // at all.
                if (resolver.resolve(lhs)) |written| {
                    if (written == receiver) return false;
                }
            }
            return true;
        }

        /// Nearest enclosing callable of `node`: a function or a test
        /// declaration. Both hold statements that call out, and a test's frame
        /// disposes an arena exactly like a function's does.
        fn enclosingCallable(
            tags: []const std.zig.Ast.Node.Tag,
            parent_map: []const u32,
            node: u32,
        ) ?u32 {
            var current = node;
            var steps: u32 = 0;
            while (steps < 128 and current < parent_map.len) : (steps += 1) {
                if (current >= tags.len) return null;
                if (tags[current] == .fn_decl or tags[current] == .test_decl) return current;
                const parent = parent_map[current];
                if (parent == 0) return null;
                current = parent;
            }
            return null;
        }

        /// Every tag that writes its left side. A compound assignment reads the
        /// value it overwrites, so it rebinds just as plainly as a plain one
        /// does. The same set the arena's ownership charge walks, so both sides
        /// answer what the frame writes over the same way.
        fn writesItsLeftSide(tag: std.zig.Ast.Node.Tag) bool {
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

        /// Resource type a Zig 0.16 handle carries.
        const IoHandle = enum {
            file,
            dir,
        };

        /// Walk budget for the receiver proofs below. It bounds stack use, not
        /// evidence: a chain longer than this answers "unknown", which leaves
        /// the handle held and still reported instead of guessing. The chain
        /// between a `close(io)` and the annotation that names its handle is
        /// longer than it looks: a guard's payload, the optional the guard
        /// unwrapped, the binding that optional was written into, the open it
        /// was built from and the receiver that open was called on all sit
        /// between the two ends of it.
        const io_handle_walk_frames: u8 = 16;

        /// Handle that `close(io)` releases at `expr_node`, or null when the
        /// proof fails.
        ///
        /// Zig 0.16 hands out `std.Io.File` and `std.Io.Dir`, and both close
        /// through the `io` runtime argument rather than through the bare
        /// receiver the pre-0.16 `std.fs` types took. The handle is proven
        /// from a verified `std` import - a `std.Io.File`/`std.Io.Dir`
        /// annotation, or the result of one of the four modeled opens
        /// (`createFile`, `openFile`, `openDir`, `openIterableDir`) on a
        /// `std.Io.Dir` - and never from the name `close`. A method that
        /// merely takes an `io`, or one called `close` on an unrelated type,
        /// releases nothing here, so its handle stays held and keeps being
        /// reported.
        fn ioCloseReceiver(self: *_Engine, tree: *const std.zig.Ast, expr_node: u32) ?IoHandle {
            return ioHandleOfExpr(self, tree, expr_node, io_handle_walk_frames);
        }

        /// Handle an expression carries. Only a verified `std.Io` resource
        /// answers, and a verified borrowed std factory answers with the
        /// type it hands back: `std.Io.Dir.cwd()` carries a directory and
        /// `std.Io.File.stdout()` a file. What it does not answer is whether
        /// anything was acquired - the caller owns nothing there, and that is
        /// the open classifier's separate question, asked through
        /// `isBorrowedIoFactory`.
        fn ioHandleOfExpr(
            self: *_Engine,
            tree: *const std.zig.Ast,
            expr_node: u32,
            depth: u8,
        ) ?IoHandle {
            if (depth == 0) return null;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (expr_node >= tags.len) return null;
            return switch (tags[expr_node]) {
                .grouped_expression, .unwrap_optional => ioHandleOfExpr(self, tree, @intFromEnum(datas[expr_node].node_and_token[0]), depth - 1),
                .@"try" => ioHandleOfExpr(self, tree, @intFromEnum(datas[expr_node].node), depth - 1),
                // What type a catch-initialized binding holds is the success
                // arm's question: its annotation or its success init names
                // the type, and a handler that coerces to that same type
                // names it too. Which arm produced the value is a separate
                // question, answered per arm by `catchArmValueExpr`.
                .@"catch" => ioHandleOfExpr(self, tree, @intFromEnum(datas[expr_node].node_and_node[0]), depth - 1),
                .identifier => ioHandleOfBinding(self, tree, expr_node, depth - 1),
                // A field is proven by the type it is declared with.
                .field_access => ioHandleOfTypeInfo(self, tree, expr_node),
                .call, .call_comma, .call_one, .call_one_comma => ioHandleOfCall(self, tree, expr_node, depth - 1),
                else => null,
            };
        }

        /// Handle a binding holds: its annotation when it has one, otherwise
        /// the initializer it was given.
        fn ioHandleOfBinding(
            self: *_Engine,
            tree: *const std.zig.Ast,
            identifier_node: u32,
            depth: u8,
        ) ?IoHandle {
            if (depth == 0) return null;
            if (ioHandleOfTypeInfo(self, tree, identifier_node)) |handle| return handle;

            var storage: [1]import_resolver.File = undefined;
            const resolver = projectResolverFor(self, tree, &storage) orelse return null;
            // A guard's payload capture is a binding no declaration
            // describes, so the resolver finds nothing to resolve it from and
            // the name is answered from the guard that wrote it instead.
            const declaration = resolver.resolveDeclarationNode(identifier_node) orelse
                return ioHandleOfPayloadCapture(self, tree, identifier_node, depth);
            // A parameter is declared by its annotation, not by an
            // initializer: `fn open(dir: Io.Dir, io: Io)` receives a
            // directory the same way a caller passes one, and that
            // annotation is the only thing that says what it is.
            if (isFnProtoTag(tree.nodes.items(.tag), declaration)) {
                return ioHandleOfFnParam(self, tree, declaration, identifier_node, depth - 1);
            }
            const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return null;
            const init = full.ast.init_node.unwrap() orelse return null;
            return ioHandleOfExpr(self, tree, @intFromEnum(init), depth - 1);
        }

        /// Handle a guard's payload capture carries, or null when the
        /// identifier is not a capture this file can attribute.
        ///
        /// `if (maybe) |file| file.close(io);` releases through a binding that
        /// nothing declares: the capture is introduced by the guard it is
        /// written next to, so the only thing that could name its type is an
        /// annotation on the optional - and an inferred optional has none.
        /// What the capture holds is the value the condition carried, so that
        /// condition is the proof: the modeled open the optional was built
        /// from, never the name `close` and never the name `file`.
        /// The capture itself is matched to its guard by
        /// `payloadCaptureCondition` below.
        fn ioHandleOfPayloadCapture(
            self: *_Engine,
            tree: *const std.zig.Ast,
            identifier_node: u32,
            depth: u8,
        ) ?IoHandle {
            if (depth == 0) return null;
            const condition = payloadCaptureCondition(self, tree, identifier_node) orelse return null;
            return ioHandleOfExpr(self, tree, condition, depth - 1);
        }

        /// The condition of the guard that wrote the binding the identifier at
        /// `identifier_node` reads, or null when the identifier is not a
        /// capture this file can attribute.
        ///
        /// This is both what the capture carries and what it releases: the
        /// acquisition is tracked against the condition's own binding, so a
        /// release naming the capture instead would name a region the open was
        /// never recorded on. A capture is written at one token and read at
        /// another, so the read and the declaration are never the same token
        /// and comparing the two proves nothing. What pairs them is the
        /// binding the read resolves to, and a guard is credited only when
        /// that binding is the capture it wrote: a name a nearer guard, a
        /// `for` element or a failure rebinds resolves to that binding
        /// instead, so a capture enclosing the same name is shadowed by it
        /// rather than answered for.
        ///
        /// Only an optional's own payload is read this way. A `for` payload is
        /// an element of its input rather than the input itself, and a
        /// `catch`, `orelse` or `errdefer` payload is an error, so none of
        /// those is the value its guard carried and each answers null.
        fn payloadCaptureCondition(self: *_Engine, tree: *const std.zig.Ast, identifier_node: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (identifier_node >= tags.len or tags[identifier_node] != .identifier) return null;
            const source = self.source orelse return null;
            const index = lexicalIndexFor(source, tree) orelse return null;
            const declaration = captureDeclaration(tree, index, identifier_node) orelse return null;

            // Parent links are a forest over the tree's nodes, so a chain ends
            // at a root declaration and the node count bounds it exactly. That
            // bound is structural rather than a budget: it counts the tree the
            // walk is climbing, so a guard behind any number of nested blocks
            // is still reached. The climb also stops at the function or
            // container the read sits in, because a capture binds nothing
            // outside the scope that wrote it.
            var node: u32 = identifier_node;
            var remaining: usize = index.ranges.len;
            while (remaining != 0 and node < index.ranges.len) : (remaining -= 1) {
                const parent = index.parent(node) orelse return null;
                if (parent >= tags.len) return null;
                if (closesCaptureScope(tags[parent])) return null;
                node = parent;
                const condition: u32 = switch (tags[node]) {
                    .@"if", .if_simple => blk: {
                        const full = tree.fullIf(@enumFromInt(node)) orelse continue;
                        if (!captureDeclares(full.payload_token, declaration)) continue;
                        break :blk @intFromEnum(full.ast.cond_expr);
                    },
                    .@"while", .while_simple, .while_cont => blk: {
                        const full = tree.fullWhile(@enumFromInt(node)) orelse continue;
                        if (!captureDeclares(full.payload_token, declaration)) continue;
                        break :blk @intFromEnum(full.ast.cond_expr);
                    },
                    else => continue,
                };
                if (condition >= tags.len) return null;
                return condition;
            }
            return null;
        }

        /// The declaration the identifier at `identifier_node` resolves to.
        ///
        /// The lexical index names variables and parameters but not the
        /// bindings a guard's capture introduces, so the query the optional
        /// unwrap checkers already use answers this one: it reads every
        /// capture scope the identifier can appear in and takes the innermost
        /// declaration of the name, which is what makes a shadowed capture
        /// resolve to itself rather than to the capture enclosing it.
        fn captureDeclaration(
            tree: *const std.zig.Ast,
            index: *const LexicalIndex,
            identifier_node: u32,
        ) ?u32 {
            const query = QueryContext{ .tree = tree, .lexical = index };
            return query.resolveIdentifierBinding(identifier_node);
        }

        /// Does this guard's capture declare exactly the binding at
        /// `declaration`?
        ///
        /// A `|*payload|` capture declares the identifier written past its
        /// `*`, so the `*` the capture points at is never that declaration
        /// and a pointer capture is never taken for the value its guard
        /// carried.
        fn captureDeclares(payload: ?std.zig.Ast.TokenIndex, declaration: u32) bool {
            const captured = payload orelse return false;
            return captured == declaration;
        }

        /// Is `tag` a scope a guard's payload capture cannot reach out of?
        ///
        /// A capture binds inside the function that wrote it, and a container
        /// declares its own members outside that function's scope, so the
        /// climb to a capture stops at either boundary rather than walking on
        /// to a guard that could never have held this declaration.
        fn closesCaptureScope(tag: std.zig.Ast.Node.Tag) bool {
            return switch (tag) {
                .fn_decl, .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi => true,
                else => call_resolver.isContainerTag(tag),
            };
        }

        /// Handle the annotated function parameter `identifier_node` names.
        /// An unannotated parameter proves nothing here and answers unknown.
        fn ioHandleOfFnParam(
            self: *_Engine,
            tree: *const std.zig.Ast,
            proto_node: u32,
            identifier_node: u32,
            depth: u8,
        ) ?IoHandle {
            if (depth == 0) return null;
            const tags = tree.nodes.items(.tag);
            if (identifier_node >= tags.len or tags[identifier_node] != .identifier) return null;
            const main_tokens = tree.nodes.items(.main_token);
            if (identifier_node >= main_tokens.len) return null;
            const token: u32 = main_tokens[identifier_node];

            // An unnamed parameter (`_: *Context`) still occupies its
            // position, so the scan steps over it instead of ending; only a
            // position past the last parameter ends it.
            var index: usize = 0;
            while (index < 64) : (index += 1) {
                const name_token = fnProtoParamNameToken(tree, proto_node, index) orelse {
                    if (fnProtoParamTypeNode(tree, proto_node, index) == null) break;
                    continue;
                };
                if (name_token != token) continue;
                const type_node = fnProtoParamTypeNode(tree, proto_node, index) orelse return null;
                return ioHandleOfTypeNode(self, tree, type_node, depth);
            }
            return null;
        }

        /// Handle a `std.Io.Dir` open method produces, or null for any other
        /// method name. This is the std model for the calls that hand back an
        /// owned handle; a same-named method on an unrelated type is settled
        /// by the receiver proof, not by the name.
        fn ioOpenMethodHandle(method: []const u8) ?IoHandle {
            if (std.mem.eql(u8, method, "createFile")) return .file;
            if (std.mem.eql(u8, method, "openFile")) return .file;
            if (std.mem.eql(u8, method, "openDir")) return .dir;
            if (std.mem.eql(u8, method, "openIterableDir")) return .dir;
            return null;
        }

        /// Handle a call hands back: one of the four modeled opens, or a
        /// verified borrowed std factory. A borrowed factory yields a handle
        /// of that type, so a value read out of one carries the type - what it
        /// is not is an acquisition, and the open classifier decides that
        /// separately.
        fn ioHandleOfCall(
            self: *_Engine,
            tree: *const std.zig.Ast,
            call_node: u32,
            depth: u8,
        ) ?IoHandle {
            if (ioHandleOfOpen(self, tree, call_node, depth)) |handle| return handle;
            return borrowedIoFactoryHandle(self, tree, call_node);
        }

        /// Handle a verified Zig 0.16 open produces: `createFile`/`openFile`
        /// yield a file, `openDir`/`openIterableDir` a directory. The call has
        /// to name its handle through a `std.Io.Dir` receiver, so a same-named
        /// method on an unrelated type opens nothing here.
        fn ioHandleOfOpen(
            self: *_Engine,
            tree: *const std.zig.Ast,
            call_node: u32,
            depth: u8,
        ) ?IoHandle {
            if (depth == 0) return null;
            if (call_node >= tree.nodes.len) return null;
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return null;
            const callee_node: u32 = @intFromEnum(call.ast.fn_expr);
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (callee_node >= tags.len or tags[callee_node] != .field_access) return null;
            const access = datas[callee_node].node_and_token;
            const method = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
            const handle = ioOpenMethodHandle(method) orelse return null;
            if (!isIoDirReceiver(self, tree, @intFromEnum(access[0]), depth - 1)) return null;
            return handle;
        }

        /// A `std.Io.Dir` value: the type written out, `cwd()`, or a binding
        /// that proves to be one. `cwd()` borrows the process directory, but
        /// what it opens is owned by the caller - which is why the open is
        /// modeled and why the borrow proves a receiver without ever being an
        /// acquisition of its own.
        fn isIoDirReceiver(
            self: *_Engine,
            tree: *const std.zig.Ast,
            expr_node: u32,
            depth: u8,
        ) bool {
            if (depth == 0) return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (expr_node >= tags.len) return false;
            switch (tags[expr_node]) {
                .grouped_expression, .unwrap_optional => return isIoDirReceiver(self, tree, @intFromEnum(datas[expr_node].node_and_token[0]), depth - 1),
                .@"try" => return isIoDirReceiver(self, tree, @intFromEnum(datas[expr_node].node), depth - 1),
                .@"catch" => return isIoDirReceiver(self, tree, @intFromEnum(datas[expr_node].node_and_node[0]), depth - 1),
                .identifier => return ioHandleOfBinding(self, tree, expr_node, depth - 1) == .dir,
                .field_access => {
                    // A field is proven either by the `std.Io.Dir` type it is
                    // spelled with or by the type it is declared with.
                    if (spelledIoHandle(self, tree, expr_node) == .dir) return true;
                    return ioHandleOfTypeInfo(self, tree, expr_node) == .dir;
                },
                // Only `std.Io.Dir.cwd()` borrows a directory; every other
                // receiver has to prove the type some other way.
                .call, .call_comma, .call_one, .call_one_comma => return borrowedIoFactoryHandle(self, tree, expr_node) == .dir,
                else => return false,
            }
        }

        /// Handle a declared type names, when the annotation spells
        /// `std.Io.File` or `std.Io.Dir` through a verified `std` import.
        fn ioHandleOfTypeInfo(
            self: *_Engine,
            tree: *const std.zig.Ast,
            expr_node: u32,
        ) ?IoHandle {
            const type_ctx = self.type_context orelse return null;
            const info = type_ctx.getExpressionType(expr_node) orelse return null;
            // An inferred type has no annotation to check, and its spelling is
            // the loose name map's guess rather than the source's own.
            const type_node = info.type_node orelse return null;
            return ioHandleOfTypeNode(self, info.type_ast orelse tree, type_node, io_handle_walk_frames);
        }

        fn ioHandleOfTypeNode(
            self: *_Engine,
            tree: *const std.zig.Ast,
            type_node: u32,
            depth: u8,
        ) ?IoHandle {
            if (depth == 0) return null;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (type_node >= tags.len) return null;
            switch (tags[type_node]) {
                .optional_type => return ioHandleOfTypeNode(self, tree, @intFromEnum(datas[type_node].node), depth - 1),
                .error_union => return ioHandleOfTypeNode(self, tree, @intFromEnum(datas[type_node].node_and_node[1]), depth - 1),
                else => {},
            }
            return spelledIoHandle(self, tree, type_node);
        }

        /// Handle a `std.Io` type member names, or null for anything else.
        fn ioMemberHandle(member: []const u8) ?IoHandle {
            if (std.mem.eql(u8, member, "File")) return .file;
            if (std.mem.eql(u8, member, "Dir")) return .dir;
            return null;
        }

        /// Alias frames one namespace walk follows. A chain longer than this
        /// answers "unknown", which leaves the handle held and reported
        /// instead of guessing.
        const io_alias_walk_frames: u8 = 8;

        /// Handle a `std.Io` type member names, reached through whatever the
        /// source calls the standard library: `std.Io.File`, or `Io.File`
        /// behind `const Io = std.Io`. Only the binding is proven, never the
        /// path after it, so a user namespace cannot pass for the standard
        /// library.
        fn spelledIoHandle(self: *_Engine, tree: *const std.zig.Ast, node: u32) ?IoHandle {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (node >= tags.len or tags[node] != .field_access) return null;
            const access = datas[node].node_and_token;
            const member = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
            const handle = ioMemberHandle(member) orelse return null;

            var storage: [1]import_resolver.File = undefined;
            const resolver = projectResolverFor(self, tree, &storage) orelse return null;
            if (!isStdIoNamespaceExpr(resolver, @intFromEnum(access[0]), io_alias_walk_frames)) return null;
            return handle;
        }

        /// True when `expr_node` denotes the standard library's `Io`
        /// namespace. A `const` alias in front of it - `const Io = std.Io`,
        /// which issue #62's reducer uses - is followed with the project
        /// resolver to what it was given, so the identity comes from the
        /// alias rather than from the local spelling. A user type called `Io`
        /// is an alias to nothing proven and stays unknown.
        fn isStdIoNamespaceExpr(
            resolver: call_resolver.ProjectTypeResolver,
            expr_node: u32,
            depth: u8,
        ) bool {
            if (depth == 0) return false;
            if (resolver.file_index >= resolver.files.len) return false;
            const tree = resolver.files[resolver.file_index].tree;
            if (tree.errors.len != 0) return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (expr_node >= tags.len) return false;
            switch (tags[expr_node]) {
                .grouped_expression, .unwrap_optional => return isStdIoNamespaceExpr(
                    resolver,
                    @intFromEnum(datas[expr_node].node_and_token[0]),
                    depth - 1,
                ),
                .identifier => {
                    const alias = resolver.resolveTypeAliasNode(expr_node) orelse return false;
                    if (alias.file_index >= resolver.files.len) return false;
                    const aliased = call_resolver.ProjectTypeResolver{
                        .files = resolver.files,
                        .file_index = alias.file_index,
                    };
                    return isStdIoNamespaceExpr(aliased, alias.node_index, depth - 1);
                },
                .field_access => {
                    const access = datas[expr_node].node_and_token;
                    if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(access[1])), "Io")) return false;
                    return isVerifiedStdBinding(tree, resolver, @intFromEnum(access[0]));
                },
                else => return false,
            }
        }

        /// Resolver whose current file is `tree`, so an import proof taken in
        /// that file answers about that file.
        fn projectResolverFor(
            self: *_Engine,
            tree: *const std.zig.Ast,
            storage: *[1]import_resolver.File,
        ) ?call_resolver.ProjectTypeResolver {
            const files = projectFiles(self, tree, storage) orelse return null;
            for (files, 0..) |file, index| {
                if (file.tree == tree) {
                    return call_resolver.ProjectTypeResolver{ .files = files, .file_index = index };
                }
            }
            return null;
        }
        const ResourceReturnStatus = enum {
            unknown,
            resource,
            non_resource,
        };

        /// Handle type a verified borrowed std factory hands back, or null for
        /// any other call. `std.Io.Dir.cwd()` and
        /// `std.Io.File.{stdin,stdout,stderr}` return a handle of that type
        /// that the caller does not own, so the value carries the type even
        /// though it is not an acquisition - which is the open classifier's
        /// separate decision.
        ///
        /// The callee is proven, never its name: the receiver has to be spelled
        /// `std.Io.Dir` or `std.Io.File` through a verified `std` import, so a
        /// user type's own `cwd` keeps normal handling and a same-named
        /// function elsewhere is unaffected.
        fn borrowedIoFactoryHandle(
            self: *_Engine,
            tree: *const std.zig.Ast,
            call_node: u32,
        ) ?IoHandle {
            if (call_node >= tree.nodes.len) return null;
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return null;
            const callee_node: u32 = @intFromEnum(call.ast.fn_expr);
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (callee_node >= tags.len or tags[callee_node] != .field_access) return null;
            const access = datas[callee_node].node_and_token;
            const handle = spelledIoHandle(self, tree, @intFromEnum(access[0])) orelse return null;
            const member = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
            const borrowed = switch (handle) {
                .dir => std.mem.eql(u8, member, "cwd"),
                .file => std.mem.eql(u8, member, "stdin") or
                    std.mem.eql(u8, member, "stdout") or
                    std.mem.eql(u8, member, "stderr"),
            };
            if (!borrowed) return null;
            return handle;
        }

        /// True when `call_ast_node` is one of those verified borrowed
        /// factories, which acquire nothing and so are never the acquisition a
        /// leak is reported against.
        fn isBorrowedIoFactory(self: *_Engine, call_ast_node: u32) bool {
            const src = self.source orelse return false;
            const tree = src.ast() catch return false;
            return borrowedIoFactoryHandle(self, tree, call_ast_node) != null;
        }

        /// Types a call's result is an owned handle when it is spelled as one:
        /// the pre-0.16 `std.fs` handles, a raw descriptor, and the Zig 0.16
        /// `std.Io` file and directory handles.
        ///
        /// This is the open side of the same model the close side proves -
        /// `std.Io.File.close(io)` and `std.Io.Dir.close(io)` release exactly
        /// what a call returning one of these hands back.
        fn isResourceTypeName(type_name: []const u8) bool {
            return std.mem.eql(u8, type_name, "std.fs.File") or
                std.mem.eql(u8, type_name, "std.fs.Dir") or
                std.mem.eql(u8, type_name, "std.fs.IterableDir") or
                std.mem.eql(u8, type_name, "std.posix.fd_t") or
                std.mem.eql(u8, type_name, "std.Io.File") or
                std.mem.eql(u8, type_name, "std.Io.Dir");
        }

        /// Classify whether a call returns a known resource type.
        /// Uses strict type information and avoids name-only heuristics.
        pub fn classifyResourceReturningCall(self: *_Engine, call_ast_node: u32) ResourceReturnStatus {
            const type_ctx = self.type_context orelse return .unknown;
            if (type_ctx.getExpressionTypeStrict(call_ast_node)) |strict_info| {
                if (strict_info.type_str) |type_str| {
                    if (isResourceTypeName(type_str)) {
                        // A borrowed factory hands back a handle the caller
                        // does not own, so it acquires nothing here.
                        if (isBorrowedIoFactory(self, call_ast_node)) return .non_resource;
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
                    if (isResourceTypeName(type_str)) {
                        // The same borrowed-factory guard as the strict branch.
                        if (isBorrowedIoFactory(self, call_ast_node)) return .non_resource;
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
            var files = [_]import_resolver.File{.{ .path = source.getFilePath(), .tree = tree }};
            files[0].lexical_index = lexicalIndexFor(source, tree);
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

        /// One project file reachable by name from a binding chain.
        const AliasFiles = struct {
            indices: [4]usize = undefined,
            len: usize = 0,

            /// Returns false only when the chain names more files than the
            /// bound allows; naming a file twice is not a failure.
            fn add(self: *AliasFiles, file_index: usize) bool {
                for (self.indices[0..self.len]) |existing| {
                    if (existing == file_index) return true;
                }
                if (self.len == self.indices.len) return false;
                self.indices[self.len] = file_index;
                self.len += 1;
                return true;
            }

            fn single(file_index: usize) AliasFiles {
                return .{ .indices = .{ file_index, 0, 0, 0 }, .len = 1 };
            }
        };

        /// Function declarations one callee expression can denote. A module
        /// that re-exports the same name from more than one file (a frontend
        /// switch) contributes every candidate; the caller requires them all
        /// to agree before treating any of them as a release.
        const CalleeDecls = struct {
            decls: [4]struct { file_index: usize, node: u32 } = undefined,
            len: usize = 0,

            fn add(self: *CalleeDecls, file_index: usize, node: u32) bool {
                if (self.len == self.decls.len) return false;
                self.decls[self.len] = .{ .file_index = file_index, .node = node };
                self.len += 1;
                return true;
            }
        };

        /// Argument of `call_ast_node` that a proven wrapper releases, or null.
        ///
        /// `compat.closeDir(ctx, &directory)` hands the caller a release the
        /// same way `directory.close()` does, but the callee's spelling is
        /// `closeDir` and its body lives in another file. The proof is the
        /// body, and it takes all three of these to hold:
        ///
        /// * the callee resolves to one function declaration, across `const`
        ///   re-exports, with every candidate naming the same parameter;
        /// * that body is a single unconditional statement, so a wrapper that
        ///   closes behind a branch is not a release;
        /// * the closed value is a genuine resource type - `std.fs.File`,
        ///   `std.fs.Dir`, `std.fs.IterableDir`, `std.posix.fd_t`,
        ///   `std.Io.File` or `std.Io.Dir` - written through a verified `std`
        ///   import of the callee's own file, and reached from the parameter
        ///   the caller passes by address.
        ///
        /// Nothing here looks at the callee's name, so a sibling with the same
        /// signature that does not close - `compat.nextDir` also takes a
        /// `*Directory` - stays an unmodelled call. A look-alike `close` on
        /// some other field, or on a type this walk cannot resolve, is not a
        /// release either, so the resource stays held and still reported.
        fn releasedByCalleeBody(self: *_Engine, tree: *const std.zig.Ast, call_ast_node: u32) ?u32 {
            var storage: [1]import_resolver.File = undefined;
            const files: []const import_resolver.File = projectFiles(self, tree, &storage) orelse return null;

            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            if (call_ast_node >= tree.nodes.len) return null;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_ast_node)) orelse return null;

            // Only a qualified callee is walked: that is the wrapper shape
            // (`compat.closeDir`, `io.closeDir`). A plain local call is either
            // already modelled by name or inlined, so resolving it again here
            // would cost a project scan per call site for no new proof.
            const callee_node: u32 = @intFromEnum(call.ast.fn_expr);
            if (callee_node >= tree.nodes.len) return null;
            if (tree.nodeTag(@enumFromInt(callee_node)) != .field_access) return null;

            var start_files: AliasFiles = .{};
            if (!fileIndexOf(files, tree, &start_files)) return null;

            const resolver = call_resolver.ProjectTypeResolver{
                .files = files,
                .file_index = start_files.indices[0],
            };

            // The project resolver settles ordinary and member callees. It
            // does not follow a `const` re-export, so that case falls through
            // to the alias walk below, which returns the same shape.
            var implicit_self: usize = 0;
            var proven: ?usize = null;
            if (resolver.resolveCallableAtCall(call_ast_node)) |callable| {
                if (callable.file_index >= files.len) return null;
                const decl = fnDeclOfProto(files[callable.file_index].tree, callable.proto_node) orelse return null;
                proven = closedResourceParameterIndex(files, callable.file_index, decl);
                implicit_self = callable.implicit_self_count;
            } else {
                var decls: CalleeDecls = .{};
                if (!collectCalleeDecls(files, &start_files, callee_node, &decls, 0)) return null;
                if (decls.len == 0) return null;
                for (decls.decls[0..decls.len]) |decl| {
                    const index = closedResourceParameterIndex(files, decl.file_index, decl.node) orelse return null;
                    if (proven) |previous| {
                        if (previous != index) return null;
                    } else {
                        proven = index;
                    }
                }
            }

            const param_index = proven orelse return null;
            if (param_index < implicit_self) return null;
            const arg = call_utils.callParam(tree, call_ast_node, param_index - implicit_self) orelse return null;
            if (arg >= tree.nodes.len) return null;
            return switch (tree.nodeTag(@enumFromInt(arg))) {
                // Passed by address, so the callee reaches the caller's
                // resource rather than a copy of it.
                .address_of, .deref => arg,
                else => null,
            };
        }

        /// Project file list the callee walk may follow. Prefers the
        /// whole-project resolver so a re-export into another file is
        /// reachable; without one the walk is confined to the analyzed file
        /// and simply finds nothing to prove.
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

        fn fileIndexOf(
            files: []const import_resolver.File,
            tree: *const std.zig.Ast,
            out: *AliasFiles,
        ) bool {
            for (files, 0..) |file, index| {
                if (file.tree == tree) return out.add(index);
            }
            return false;
        }

        /// Expand a callee expression into the function declarations it can
        /// denote, following `const` re-exports and conditional imports.
        /// Returns false - meaning "unknown", which callers treat as "not a
        /// release" - as soon as any part of the chain cannot be resolved.
        fn collectCalleeDecls(
            files: []const import_resolver.File,
            namespace: *const AliasFiles,
            callee_node: u32,
            out: *CalleeDecls,
            depth: u8,
        ) bool {
            if (depth >= 8 or namespace.len == 0) return false;
            const first_file = namespace.indices[0];
            if (first_file >= files.len) return false;
            const tree = files[first_file].tree;
            if (tree.errors.len != 0) return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (callee_node >= tags.len) return false;

            switch (tags[callee_node]) {
                .grouped_expression => return collectCalleeDecls(
                    files,
                    namespace,
                    @intFromEnum(datas[callee_node].node_and_token[0]),
                    out,
                    depth + 1,
                ),
                .@"if", .if_simple => {
                    const full_if = tree.fullIf(@enumFromInt(callee_node)) orelse return false;
                    const else_expr = full_if.ast.else_expr.unwrap() orelse return false;
                    return collectCalleeDecls(
                        files,
                        namespace,
                        @intFromEnum(full_if.ast.then_expr),
                        out,
                        depth + 1,
                    ) and collectCalleeDecls(
                        files,
                        namespace,
                        @intFromEnum(else_expr),
                        out,
                        depth + 1,
                    );
                },
                .identifier => {
                    const name = import_resolver.identifierName(tree, callee_node) orelse return false;
                    return resolveCalleeBinding(files, namespace, name, out, depth);
                },
                .field_access => {
                    const access = datas[callee_node].node_and_token;
                    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                    var members: AliasFiles = .{};
                    if (!resolveNamespace(files, namespace, @intFromEnum(access[0]), &members, depth)) return false;
                    return resolveCalleeBinding(files, &members, name, out, depth);
                },
                else => return false,
            }
        }

        /// Look `name` up in each namespace file and record the declarations
        /// it reaches: a function directly, or the `const` it re-exports.
        fn resolveCalleeBinding(
            files: []const import_resolver.File,
            namespace: *const AliasFiles,
            name: []const u8,
            out: *CalleeDecls,
            depth: u8,
        ) bool {
            if (depth >= 8 or namespace.len == 0) return false;
            var resolved_any = false;
            for (namespace.indices[0..namespace.len]) |file_index| {
                if (file_index >= files.len) return false;
                const tree = files[file_index].tree;
                const decl = rootDeclByName(tree, name) orelse return false;
                const tags = tree.nodes.items(.tag);
                if (tags[decl] == .fn_decl) {
                    if (!out.add(file_index, decl)) return false;
                } else if (import_resolver.isVarDeclTag(tags[decl])) {
                    const full = tree.fullVarDecl(@enumFromInt(decl)) orelse return false;
                    if (tree.tokenTag(full.ast.mut_token) != .keyword_const) return false;
                    const init = full.ast.init_node.unwrap() orelse return false;
                    const alias = AliasFiles.single(file_index);
                    if (!collectCalleeDecls(files, &alias, @intFromEnum(init), out, depth + 1)) return false;
                } else return false;
                resolved_any = true;
            }
            return resolved_any;
        }

        /// Resolve a namespace expression - an import binding, possibly
        /// re-exported or switched per frontend - to the files it names.
        fn resolveNamespace(
            files: []const import_resolver.File,
            namespace: *const AliasFiles,
            expr_node: u32,
            out: *AliasFiles,
            depth: u8,
        ) bool {
            if (depth >= 8 or namespace.len == 0) return false;
            const first_file = namespace.indices[0];
            if (first_file >= files.len) return false;
            const tree = files[first_file].tree;
            if (tree.errors.len != 0) return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (expr_node >= tags.len) return false;

            switch (tags[expr_node]) {
                .grouped_expression => return resolveNamespace(
                    files,
                    namespace,
                    @intFromEnum(datas[expr_node].node_and_token[0]),
                    out,
                    depth + 1,
                ),
                .@"if", .if_simple => {
                    const full_if = tree.fullIf(@enumFromInt(expr_node)) orelse return false;
                    const else_expr = full_if.ast.else_expr.unwrap() orelse return false;
                    var then_files: AliasFiles = .{};
                    if (!resolveNamespace(files, namespace, @intFromEnum(full_if.ast.then_expr), &then_files, depth + 1)) return false;
                    var else_files: AliasFiles = .{};
                    if (!resolveNamespace(
                        files,
                        namespace,
                        @intFromEnum(else_expr),
                        &else_files,
                        depth + 1,
                    )) return false;
                    for (then_files.indices[0..then_files.len]) |file_index| {
                        if (!out.add(file_index)) return false;
                    }
                    for (else_files.indices[0..else_files.len]) |file_index| {
                        if (!out.add(file_index)) return false;
                    }
                    return true;
                },
                .identifier => {
                    const name = import_resolver.identifierName(tree, expr_node) orelse return false;
                    const decl = rootDeclByName(tree, name) orelse return false;
                    if (!import_resolver.isVarDeclTag(tags[decl])) return false;
                    const full = tree.fullVarDecl(@enumFromInt(decl)) orelse return false;
                    if (tree.tokenTag(full.ast.mut_token) != .keyword_const) return false;
                    const init = full.ast.init_node.unwrap() orelse return false;
                    const same_file = AliasFiles.single(first_file);
                    return resolveNamespace(files, &same_file, @intFromEnum(init), out, depth + 1);
                },
                .field_access => {
                    const access = datas[expr_node].node_and_token;
                    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                    var members: AliasFiles = .{};
                    if (!resolveNamespace(files, namespace, @intFromEnum(access[0]), &members, depth)) return false;
                    var resolved_any = false;
                    for (members.indices[0..members.len]) |member_file| {
                        if (member_file >= files.len) return false;
                        const member_tree = files[member_file].tree;
                        const member_decl = rootDeclByName(member_tree, name) orelse return false;
                        const member_tags = member_tree.nodes.items(.tag);
                        if (!import_resolver.isVarDeclTag(member_tags[member_decl])) return false;
                        const full = member_tree.fullVarDecl(@enumFromInt(member_decl)) orelse return false;
                        if (member_tree.tokenTag(full.ast.mut_token) != .keyword_const) return false;
                        const init = full.ast.init_node.unwrap() orelse return false;
                        const member_only = AliasFiles.single(member_file);
                        var branch: AliasFiles = .{};
                        if (!resolveNamespace(
                            files,
                            &member_only,
                            @intFromEnum(init),
                            &branch,
                            depth + 1,
                        )) return false;
                        for (branch.indices[0..branch.len]) |file_index| {
                            if (!out.add(file_index)) return false;
                        }
                        resolved_any = true;
                    }
                    return resolved_any;
                },
                else => {
                    // `@import("…")` and any other namespace expression.
                    const import_path = import_resolver.importPathFromBuiltinCall(tree, expr_node) orelse return false;
                    for (namespace.indices[0..namespace.len]) |file_index| {
                        if (file_index >= files.len) return false;
                        const target = import_resolver.resolveImportToFileIndex(
                            files,
                            files[file_index].path,
                            import_path,
                        ) orelse return false;
                        if (!out.add(target)) return false;
                    }
                    return true;
                },
            }
        }

        /// Root-scope declaration named `name`, or null. Only root declarations
        /// are visible here; a name that would need a local scope is reported
        /// as unknown instead of being guessed at.
        fn rootDeclByName(tree: *const std.zig.Ast, name: []const u8) ?u32 {
            const tags = tree.nodes.items(.tag);
            for (tree.rootDecls()) |decl_node| {
                const decl: u32 = @intFromEnum(decl_node);
                if (decl >= tags.len) continue;
                if (tags[decl] == .fn_decl) {
                    const proto: u32 = @intFromEnum(tree.nodes.items(.data)[decl].node_and_node[0]);
                    const name_token = fnProtoNameToken(tree, proto) orelse continue;
                    if (tokenIsName(tree, name_token, name)) return decl;
                    continue;
                }
                if (!import_resolver.isVarDeclTag(tags[decl])) continue;
                const full = tree.fullVarDecl(@enumFromInt(decl)) orelse continue;
                if (tokenIsName(tree, full.ast.mut_token + 1, name)) return decl;
            }
            return null;
        }

        fn tokenIsName(tree: *const std.zig.Ast, token: u32, name: []const u8) bool {
            if (token >= tree.tokens.len) return false;
            if (tree.tokenTag(token) != .identifier) return false;
            return std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(token)), name);
        }

        /// Prototype parameter index the function at `fn_decl` unconditionally
        /// closes, or null when its body closes anything else.
        ///
        /// The body must be a single statement, and the value it closes must
        /// be a genuine resource reached from one of the parameters: a
        /// same-named method on a different field, on a type this walk cannot
        /// resolve, or behind a branch is not a release of the argument the
        /// caller still holds.
        fn closedResourceParameterIndex(
            files: []const import_resolver.File,
            file_index: usize,
            fn_decl: u32,
        ) ?usize {
            if (file_index >= files.len) return null;
            const tree = files[file_index].tree;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (fn_decl >= tags.len or tags[fn_decl] != .fn_decl) return null;
            const proto = fnProtoOf(tree, fn_decl) orelse return null;
            const body: u32 = @intFromEnum(datas[fn_decl].node_and_node[1]);

            var scratch: [2]u32 = undefined;
            const statements = blockStatements(tree, tags, datas, body, &scratch) orelse return null;
            if (statements.len != 1) return null;

            const statement = statements[0];
            if (statement >= tags.len or !call_utils.isCallNode(tags[statement])) return null;
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(statement)) orelse return null;
            const callee: u32 = @intFromEnum(call.ast.fn_expr);
            if (callee >= tags.len or tags[callee] != .field_access) return null;
            const access = datas[callee].node_and_token;
            if (!tokenIsName(tree, access[1], "close")) return null;

            // `<parameter>(.field)*.close(...)`: record the field chain and the
            // parameter it hangs off.
            var fields: [8]u32 = undefined;
            var field_count: usize = 0;
            var node: u32 = @intFromEnum(access[0]);
            var depth: u8 = 0;
            while (depth < 8) : (depth += 1) {
                if (node >= tags.len) return null;
                switch (tags[node]) {
                    .identifier => break,
                    .field_access => {
                        if (field_count == fields.len) return null;
                        fields[field_count] = datas[node].node_and_token[1];
                        field_count += 1;
                        node = @intFromEnum(datas[node].node_and_token[0]);
                    },
                    .deref => node = @intFromEnum(datas[node].node),
                    .grouped_expression, .unwrap_optional => node = @intFromEnum(datas[node].node_and_token[0]),
                    else => return null,
                }
            }
            if (depth >= 8 or node >= tags.len or tags[node] != .identifier) return null;

            const token = tree.nodes.items(.main_token)[node];
            if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return null;
            const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));

            // An unnamed parameter (`_: *Context`) still occupies its
            // position - the caller passes the argument there and every
            // later parameter keeps its index - so the scan steps over it
            // instead of ending. Only a position past the last parameter
            // ends it.
            var param_index: ?usize = null;
            var index: usize = 0;
            while (index < 64) : (index += 1) {
                const name_token = fnProtoParamNameToken(tree, proto, index) orelse {
                    if (fnProtoParamTypeNode(tree, proto, index) == null) break;
                    continue;
                };
                if (tokenIsName(tree, name_token, name)) {
                    param_index = index;
                    break;
                }
            }

            const closed_param = param_index orelse return null;
            return closesGenuineResourceField(files, file_index, proto, closed_param, fields[0..field_count]);
        }

        /// True when `field_chain` off `param_index` names the wrapper's one
        /// real resource.
        ///
        /// The wrapper type must carry exactly one field of a genuine
        /// resource type and the body must close that field. With two such
        /// fields "the opened handle" is ambiguous - a body closing the other
        /// one is not a release of what the caller opened - so the proof fails
        /// and the leak stays reported. Nested paths are not proven either.
        fn closesGenuineResourceField(
            files: []const import_resolver.File,
            file_index: usize,
            proto: u32,
            param_index: usize,
            field_chain: []const u32,
        ) ?usize {
            if (field_chain.len != 1) return null;
            const resolver = call_resolver.ProjectTypeResolver{ .files = files, .file_index = file_index };
            const tree = files[file_index].tree;
            const param_type = fnProtoParamTypeNode(tree, proto, param_index) orelse return null;
            const owner = resolver.resolveTypeNode(param_type) orelse return null;
            if (owner.file_index != file_index) return null;
            const container_node = owner.container_node orelse return null;

            const container_tree = files[owner.file_index].tree;
            var buf: [2]std.zig.Ast.Node.Index = undefined;
            const container = container_tree.fullContainerDecl(&buf, @enumFromInt(container_node)) orelse return null;
            var genuine_fields: usize = 0;
            var closes_the_only_resource = false;
            for (container.ast.members) |member_node| {
                const member: u32 = @intFromEnum(member_node);
                if (member >= container_tree.nodes.items(.tag).len) continue;
                const field = containerField(container_tree, member) orelse continue;
                if (!isGenuineResourceType(container_tree, resolver, field.type_node, 0)) continue;
                genuine_fields += 1;
                if (std.mem.eql(u8, import_resolver.normalizeIdentifier(container_tree.tokenSlice(field.name_token)), import_resolver.normalizeIdentifier(tree.tokenSlice(field_chain[0])))) {
                    closes_the_only_resource = true;
                }
            }
            if (genuine_fields != 1 or !closes_the_only_resource) return null;
            return param_index;
        }

        const ContainerField = struct {
            name_token: std.zig.Ast.TokenIndex,
            type_node: u32,
        };

        fn containerField(tree: *const std.zig.Ast, member: u32) ?ContainerField {
            const tags = tree.nodes.items(.tag);
            if (member >= tags.len) return null;
            const tag = tags[member];
            if (tag != .container_field and tag != .container_field_init and tag != .container_field_align) return null;
            const full_field = tree.fullContainerField(@enumFromInt(member)) orelse return null;
            const type_node = full_field.ast.type_expr.unwrap() orelse return null;
            return .{
                .name_token = full_field.ast.main_token,
                .type_node = @intFromEnum(type_node),
            };
        }

        /// Resource type spelled through a verified `std` import of the same
        /// file: `std.fs.File`, `std.fs.Dir`, `std.fs.IterableDir`,
        /// `std.posix.fd_t`, `std.Io.File` or `std.Io.Dir`.
        fn isGenuineResourceType(
            tree: *const std.zig.Ast,
            resolver: call_resolver.ProjectTypeResolver,
            type_node: u32,
            depth: u8,
        ) bool {
            if (depth >= 8) return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            if (type_node >= tags.len) return false;
            switch (tags[type_node]) {
                .optional_type => return isGenuineResourceType(
                    tree,
                    resolver,
                    @intFromEnum(datas[type_node].node),
                    depth + 1,
                ),
                .error_union => return isGenuineResourceType(
                    tree,
                    resolver,
                    @intFromEnum(datas[type_node].node_and_node[1]),
                    depth + 1,
                ),
                .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                    const ptr = tree.fullPtrType(@enumFromInt(type_node)) orelse return false;
                    return isGenuineResourceType(tree, resolver, @intFromEnum(ptr.ast.child_type), depth + 1);
                },
                .field_access => {
                    const access = datas[type_node].node_and_token;
                    const member = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                    const base: u32 = @intFromEnum(access[0]);
                    if (base >= tags.len or tags[base] != .field_access) return false;
                    const base_access = datas[base].node_and_token;
                    const namespace = import_resolver.normalizeIdentifier(tree.tokenSlice(base_access[1]));
                    if (std.mem.eql(u8, member, "fd_t")) {
                        if (!std.mem.eql(u8, namespace, "posix")) return false;
                    } else if (std.mem.eql(u8, member, "File") or
                        std.mem.eql(u8, member, "Dir") or
                        std.mem.eql(u8, member, "IterableDir"))
                    {
                        if (!std.mem.eql(u8, namespace, "fs") and !std.mem.eql(u8, namespace, "Io")) return false;
                    } else return false;
                    return isVerifiedStdBinding(tree, resolver, @intFromEnum(base_access[0]));
                },
                else => return false,
            }
        }

        fn isVerifiedStdBinding(
            tree: *const std.zig.Ast,
            resolver: call_resolver.ProjectTypeResolver,
            node: u32,
        ) bool {
            if (import_resolver.importPathFromBuiltinCall(tree, node)) |path| {
                return std.mem.eql(u8, path, "std");
            }
            return resolver.isVerifiedImportBinding(node, "std");
        }

        fn isFnProtoTag(tags: []const std.zig.Ast.Node.Tag, node: u32) bool {
            if (node >= tags.len) return false;
            return switch (tags[node]) {
                .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi => true,
                else => false,
            };
        }

        /// Prototype node of a function declaration.
        fn fnProtoOf(tree: *const std.zig.Ast, fn_decl: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (fn_decl >= tags.len or tags[fn_decl] != .fn_decl) return null;
            const proto: u32 = @intFromEnum(tree.nodes.items(.data)[fn_decl].node_and_node[0]);
            if (!isFnProtoTag(tags, proto)) return null;
            return proto;
        }

        /// Declaration owning a prototype, for a callee the project resolver
        /// resolved to its prototype directly. A prototype node carries its
        /// parameters in `extra_data`, not in `node_and_node`, so the owner is
        /// found by matching the declaration that points at it.
        fn fnDeclOfProto(tree: *const std.zig.Ast, proto_node: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (!isFnProtoTag(tags, proto_node)) return null;
            const datas = tree.nodes.items(.data);
            for (tags, 0..) |tag, node| {
                if (tag != .fn_decl) continue;
                const decl_proto: u32 = @intFromEnum(datas[node].node_and_node[0]);
                if (decl_proto == proto_node) return @intCast(node);
            }
            return null;
        }

        /// Name token of prototype parameter `index`. The prototype is decoded
        /// inside this frame, so no borrowed parameter slice escapes.
        fn fnProtoParamNameToken(tree: *const std.zig.Ast, proto_node: u32, index: usize) ?u32 {
            const type_node = fnProtoParamTypeNode(tree, proto_node, index) orelse return null;
            const name_token = import_resolver.paramNameTokenBeforeType(tree, type_node) orelse return null;
            return @intCast(name_token);
        }

        fn fnProtoParamTypeNode(tree: *const std.zig.Ast, proto_node: u32, index: usize) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (!isFnProtoTag(tags, proto_node)) return null;
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const params = switch (tags[proto_node]) {
                .fn_proto => tree.fnProto(@enumFromInt(proto_node)).ast.params,
                .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)).ast.params,
                .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(proto_node)).ast.params,
                .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)).ast.params,
                else => return null,
            };
            if (index >= params.len) return null;
            return paramTypeNode(tree, @intFromEnum(params[index]));
        }

        fn fnProtoNameToken(tree: *const std.zig.Ast, proto_node: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (!isFnProtoTag(tags, proto_node)) return null;
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const name_token = switch (tags[proto_node]) {
                .fn_proto => tree.fnProto(@enumFromInt(proto_node)).name_token,
                .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)).name_token,
                .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(proto_node)).name_token,
                .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)).name_token,
                else => return null,
            } orelse return null;
            return name_token;
        }

        /// Type expression of a parameter node, which the AST stores either as
        /// the parameter itself or as a var-decl wrapping the name and type.
        fn paramTypeNode(tree: *const std.zig.Ast, param_node: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            if (param_node >= tags.len) return null;
            if (import_resolver.isVarDeclTag(tags[param_node])) {
                const full = tree.fullVarDecl(@enumFromInt(param_node)) orelse return null;
                return @intFromEnum(full.ast.type_node.unwrap() orelse return null);
            }
            return param_node;
        }

        /// Statements of a block-shaped body node.
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
                // A single-expression body is not a block; treat it as one
                // statement so `fn f() void { x.close(); }` still qualifies.
                else => {
                    scratch[0] = node;
                    return scratch[0..1];
                },
            }
        }

        pub fn isDefinitelyNonAllocExpr(self: *_Engine, tree: *const std.zig.Ast, expr_node: u32) bool {
            if (resolveResourceCallFromExpr(self, tree, expr_node)) |call_info| {
                return switch (call_info.kind) {
                    .alloc, .realloc, .open => false,
                    .free, .free_owned, .close => true,
                };
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

/// The source's own immutable syntax facts, borrowed only for the AST they
/// describe. A foreign tree, a source whose AST is not parsed yet, or an index
/// that cannot be built answers null, which leaves the caller on the unindexed
/// behavior instead of failing a query. The source stays the sole owner of that
/// storage.
fn lexicalIndexFor(source: *Source, tree: *const std.zig.Ast) ?*const LexicalIndex {
    const source_tree = source.ast() catch return null;
    if (tree != source_tree) return null;
    return source.lexicalIndex() catch null;
}
