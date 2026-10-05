//! Provenance of the allocator an allocation is charged to.
//!
//! Two facts are proved here, and only from this source file:
//!
//! * A local standard arena owns every allocation made through it, whether
//!   the allocator is used as `arena.allocator`, as the `allocator()` it
//!   returns, or through a local binding of either. The arena is the owner,
//!   so `arena.deinit()` releases what it holds, handing the arena back by
//!   value - written out or inside a local binding of the frame that holds it
//!   - transfers it, and handing back its address transfers nothing: the
//!   frame it pointed into is gone by the time anyone reads it.
//! * An allocator that reaches the analyzed function through a context field
//!   of one of its parameters belongs to the caller. It counts as released
//!   only when the frame leaves that context alone, and every call site of
//!   this function in this file hands the parameter a context that still
//!   holds an arena the caller disposes on every path out or hands back.
//!   Anything else - a plain allocator, an arena with no `deinit`, an
//!   `errdefer` on its own, a context the frame writes to or hands on -
//!   directly or through a binding of its own that holds the address of the
//!   context or of the field the allocator arrives through - a method the
//!   caller reaches the context through, a context the caller reaches again
//!   before the call, a function with no visible call site - proves nothing
//!   and the allocation keeps being reported.
//! * That field is read through the parameter itself or through a copy of it
//!   the frame declared of its own: `const alias = context;` holds that same
//!   pointer under another name, so a read through the copy reads the
//!   caller's context and a write through it writes there. A copy is therefore
//!   read as the parameter, and every field path is read from its base to
//!   its final member, however many fields deep the allocator sits.
//!
//! A hand-off is settled by the context it carries, not by the local that
//! carries it: a call made through a binding holding the address of the
//! context is settled on that context, and an arena that rides out of the
//! frame rides out of the binding the return names only while nothing has
//! written that binding over - not the arena itself, nor the field of it the
//! arena rides under.
//! A copy of an arena a frame declares is that arena by value, so the field
//! the arena rides under is that same field whether the owner was written out
//! around the arena itself or around a binding the frame copied it into first,
//! and a write to that field replaces what the hand-off carries either way.
//!
//! Arena-ness comes from the arena type or from `ArenaAllocator.init` reached
//! through a verified `std` import. The import is proved by the binding's own
//! initializer inside this file, so neither proof needs a project file list and
//! `var arena = verified_std.heap.ArenaAllocator.init(gpa);` needs no written
//! type. A variable named `arena` that holds a plain allocator proves nothing,
//! and neither does a user type or namespace spelled like the standard one.
//!
//! Both of those read the value a binding holds where an allocation happens,
//! so a binding the frame writes over is no arena to either of them: a
//! declared type outlives the write and a constructor ran before it.

const std = @import("std");
const ids = @import("../../ids.zig");
const ast_walk = @import("../../ast_walk.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
const allocator_utils = @import("../../analysis/allocator_utils.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const Source = @import("../../source.zig").Source;
const LexicalIndex = @import("../../analysis/lexical_index.zig").LexicalIndex;
const Cfg = @import("../../cfg.zig").Cfg;

/// Longest projection chain walked back from an allocator expression to the
/// parameter the allocator arrives through.
const max_field_depth = 8;

/// Most pointer bindings one context is tracked through. A chain of aliases
/// deeper than this is longer than anything the proofs below read.
const max_context_aliases = 8;

/// Deepest block nesting a statement path is compared through.
const max_block_nesting = 16;

/// Most disposals of one arena a caller is read through, deferred and bare
/// together. A caller that disposes the same arena more often than this proves
/// nothing.
const max_caller_deinits = 8;

/// Fields read off a binding, in the order they are reached from its base.
const FieldChain = struct {
    names: [max_field_depth][]const u8 = undefined,
    len: usize = 0,
};

/// Statements walked to reach a node, outermost block first: the path a frame
/// takes to get there. Two nodes are ordered by the path to them, so a
/// statement of a block written before the block the call sits in still comes
/// first.
const StatementPath = struct {
    levels: [max_block_nesting]usize = undefined,
    len: usize = 0,
};

/// Largest prototype scanned for a parameter name.
const max_params = 32;

/// Base of an allocator expression plus the names of the fields walked over to
/// reach it, in access order. Names, not token positions: the same field is
/// spelled by a different token in the callee and in the caller, so the two
/// have to be recognized as one name.
const RootPath = struct {
    root: u32,
    fields: [max_field_depth][]const u8 = undefined,
    depth: usize = 0,
};

/// Call a pointer reaches as a written argument, and the position it is
/// written at: the hand-off a callee's own frame settles. Null when the
/// pointer is handed on some other way - returned, stored, put into a
/// container - where no callee of its own decides anything.
const CallArgument = struct {
    call_node: u32,
    param_index: usize,
};

/// Prototype a call reaches and how many of its leading parameters the call
/// site does not write.
const CalleeTarget = struct {
    proto_node: u32,
    implicit_self_count: usize,
};

/// Parameter an allocator expression reaches the caller's context through, and
/// the binding that parameter is declared as.
const ParameterRoot = struct {
    index: usize,
    var_id: ids.VarId,
};

pub fn Mixin(comptime _Engine: type) type {
    return struct {
        /// Expression an allocation call allocates through: the allocator
        /// receiver, or the first argument of a free-standing allocator
        /// function such as `std.fmt.allocPrint`.
        pub fn allocatorExpr(self: *_Engine, tree: *const std.zig.Ast, call_node: u32) ?u32 {
            const info = call_utils.resolveCall(tree, self.type_context, call_node, &self.fqn_buffer) orelse {
                return null;
            };
            if (info.param_count > 0) {
                const first_arg = call_utils.callParam(tree, call_node, 0) orelse {
                    return null;
                };
                if (allocator_utils.isAllocatorExpr(tree, self.type_context, first_arg)) {
                    return first_arg;
                }
            }
            if (info.base_node) |base| {
                if (allocator_utils.isAllocatorExpr(tree, self.type_context, base)) {
                    return base;
                }
            }
            // Neither the spelling nor the frontend's type resolution named an
            // allocator here, and a context field is exactly that case: it is
            // spelled like any other field, and reading its type means
            // resolving the parameter, the struct behind it and the field
            // inside that struct. The projection is still recognizable here,
            // and it is all the two owners below read - `localArenaOwner`
            // needs an arena binding behind it, `releasedByCallerArena` a
            // parameter of this very function. Both refuse whatever they
            // cannot prove, so an expression that is no allocator at all
            // leaves the allocation reported exactly as before.
            return unrecognizedAllocatorCandidate(tree, info);
        }

        /// Argument or receiver an allocation call still offers to the
        /// ownership proofs: the one that reads a binding through a field,
        /// which is the projection both proofs walk. Nothing else is named,
        /// because neither proof could read it.
        fn unrecognizedAllocatorCandidate(tree: *const std.zig.Ast, info: call_utils.CallInfo) ?u32 {
            if (info.param_count > 0) {
                if (call_utils.callParam(tree, info.call_node, 0)) |arg| {
                    if (readsThroughField(tree, arg)) return arg;
                }
            }
            if (info.base_node) |base| {
                if (readsThroughField(tree, base)) return base;
            }
            return null;
        }

        /// True when the expression reads a binding through at least one
        /// field, with only pointers and groupings in front of it.
        fn readsThroughField(tree: *const std.zig.Ast, expr: u32) bool {
            const root = stripProjections(tree, expr) orelse return false;
            return root.depth != 0;
        }

        /// Arena binding of the analyzed function that owns an allocation made
        /// through `alloc_expr`, when that allocator is one of its arenas.
        pub fn localArenaOwner(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            alloc_expr: u32,
        ) ?ids.VarId {
            return arenaOwnerOf(self, tree, current_cfg, alloc_expr, 0);
        }

        /// True when the allocator arrives through a context field of a
        /// parameter and every call site of this function in this file hands
        /// that parameter an arena the caller settles on every path out.
        ///
        /// The frame also has to leave the context alone, and the caller has to
        /// keep it. Anything that writes through the context, stores it, hands
        /// it to another function or returns it lets the allocator outlive the
        /// arena the caller disposes, and so does a context the caller reaches
        /// again between handing it over and making the call. Then nothing the
        /// caller did proves anything here.
        pub fn releasedByCallerArena(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            alloc_expr: u32,
        ) bool {
            const fn_node = current_cfg.fn_ast_node orelse {
                return false;
            };
            // Every question below is answered by this frame's own bindings:
            // which parameter the allocator reads through, whether the frame
            // escapes that parameter or writes to it. Resolving an identifier
            // falls back to the token it happens to be written with when no
            // resolver is registered for the frame, and that fallback weighs a
            // use site against a parameter declaration and finds two different
            // bindings. Prepare the frame so the identity read here is the
            // resolver's answer and never a token coincidence.
            _Engine.VarResolution.prepare(self, current_cfg) catch {
                return false;
            };
            const fn_index = ids.astIndex(fn_node);
            const root = stripProjections(tree, alloc_expr) orelse {
                return false;
            };
            // A bare allocator parameter names no context, so nothing about the
            // caller's lifetime can be read off it here.
            if (root.depth == 0) {
                return false;
            }

            const parent_map = self.getParentMap(tree) catch {
                return false;
            };
            // The base has to be a parameter of this very function, read
            // through this frame's own bindings. The declaration names the
            // binding; the spelling in the body is a different token that only
            // the resolver can tie back to it, so a local shadowing the
            // parameter - or a same-named parameter of another function -
            // never stands in for it. The expression may also be spelled
            // through a copy of that pointer the frame declared of its own,
            // and the context both questions below are asked about is the
            // parameter that copy was taken from.
            const parameter = parameterOfRoot(self, tree, parent_map, current_cfg, fn_index, root.root) orelse {
                return false;
            };
            const param_index = parameter.index;
            const root_var = parameter.var_id;
            // A binding of this frame that holds the address of the context, or
            // of the field the allocator arrives through, is the context for
            // both questions below: writing through it and handing it on both
            // reach where the context itself reaches.
            var aliases: [max_context_aliases]ids.VarId = undefined;
            var alias_count: usize = 0;
            collectContextAliases(
                self,
                tree,
                parent_map,
                fn_index,
                current_cfg,
                root_var,
                root.fields[0..root.depth],
                true,
                parameterIsPointer(tree, fn_index, param_index),
                &aliases,
                &alias_count,
            );
            if (parameterEscapes(self, tree, current_cfg, fn_index, parent_map, root_var, aliases[0..alias_count], true)) {
                return false;
            }
            if (parameterIsWrittenTo(self, tree, current_cfg, parent_map, fn_index, root_var, aliases[0..alias_count], root.fields[0..root.depth])) {
                return false;
            }

            const own_proto = functionProtoNode(tree, fn_index) orelse {
                return false;
            };
            const tags = tree.nodes.items(.tag);
            var call_sites: usize = 0;
            for (tags, 0..) |tag, node_index| {
                const node: u32 = @intCast(node_index);
                if (!call_utils.isCallNode(tag)) continue;
                // The call has to reach this function. Its name alone would
                // also accept a same-named function of another scope, or one a
                // local binding has taken over.
                const callee_proto = calleeTarget(self, tree, node) orelse continue;
                if (callee_proto.proto_node != own_proto) {
                    continue;
                }
                var call_buf: [1]std.zig.Ast.Node.Index = undefined;
                const call = tree.fullCall(&call_buf, @enumFromInt(node)) orelse continue;
                // A recursive self-call adds no caller fact.
                const caller_fn = enclosingBody(tags, parent_map, node) orelse continue;
                if (caller_fn == fn_index) {
                    continue;
                }

                // A caller this file cannot read proves nothing, so it settles
                // the release against the claim instead of for it. Counting a
                // site whose frame is missing would let the one caller that
                // cannot be examined stand in for a disposing one.
                const caller_cfg = (self.getOrBuildFunctionCfg(ids.astId(caller_fn)) catch {
                    return false;
                }) orelse {
                    return false;
                };
                // The caller's own bindings have to be resolvable before the
                // arena it passes can be recognized, and a frame that was
                // never analyzed in its own right has no resolver yet. That
                // resolver is built for the caller's own frame, so reading it
                // leaves this frame's bindings untouched.
                _Engine.VarResolution.prepare(self, caller_cfg) catch {
                    return false;
                };
                if (!callSiteReleasesArena(
                    self,
                    tree,
                    parent_map,
                    caller_fn,
                    caller_cfg,
                    call,
                    node,
                    param_index,
                    root,
                )) {
                    return false;
                }
                call_sites += 1;
            }
            // No visible caller: the release is not in this file, so nothing is
            // proved and the allocation keeps being reported.
            if (call_sites == 0) {
                return false;
            }
            return true;
        }

        /// Walk an allocator expression looking for the arena binding it draws
        /// from. Bounded so a malformed chain cannot spin.
        ///
        /// `allocator` is the only member read as an allocator hand-out, and
        /// the base it is read from still has to resolve to an arena binding,
        /// so `arena.allocator()`, `arena.allocator` and a local alias of
        /// either all lead back to the same arena. A method of any other name,
        /// or one whose receiver is not a proven arena, proves nothing.
        fn arenaOwnerOf(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            expr: u32,
            depth: u8,
        ) ?ids.VarId {
            if (depth >= 8) return null;
            const tags = tree.nodes.items(.tag);
            if (expr >= tags.len) return null;

            switch (tags[expr]) {
                .identifier => {
                    if (arenaVarId(self, tree, current_cfg, expr)) |arena| return arena;
                    // A local binding initialized from an arena's allocator.
                    const decl_info = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, expr, current_cfg) orelse return null;
                    if (decl_info.is_top_level) return null;
                    const full = tree.fullVarDecl(@enumFromInt(decl_info.decl_node)) orelse return null;
                    const init = full.ast.init_node.unwrap() orelse return null;
                    return arenaOwnerOf(self, tree, current_cfg, @intFromEnum(init), depth + 1);
                },
                .field_access => {
                    const access = tree.nodes.items(.data)[expr].node_and_token;
                    if (!fieldNameIs(tree, access[1], "allocator")) return null;
                    return arenaOwnerOf(self, tree, current_cfg, @intFromEnum(access[0]), depth + 1);
                },
                .call, .call_comma, .call_one, .call_one_comma => {
                    // `arena.allocator()` is how an arena hands out its
                    // allocator; the arena behind it still owns the result.
                    var call_buf: [1]std.zig.Ast.Node.Index = undefined;
                    const call = tree.fullCall(&call_buf, @enumFromInt(expr)) orelse return null;
                    const callee: u32 = @intFromEnum(call.ast.fn_expr);
                    if (callee >= tags.len or tags[callee] != .field_access) return null;
                    const access = tree.nodes.items(.data)[callee].node_and_token;
                    if (!fieldNameIs(tree, access[1], "allocator")) return null;
                    return arenaOwnerOf(self, tree, current_cfg, @intFromEnum(access[0]), depth + 1);
                },
                .deref, .address_of, .grouped_expression, .unwrap_optional => {
                    return arenaOwnerOf(self, tree, current_cfg, nodeChild(tree, expr) orelse return null, depth + 1);
                },
                else => return null,
            }
        }

        /// Var id of the arena an identifier denotes, when that identifier is
        /// an arena binding of the analyzed function.
        fn arenaVarId(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            ident_node: u32,
        ) ?ids.VarId {
            if (!isArenaBinding(self, tree, current_cfg, ident_node)) return null;
            return _Engine.VarResolution.resolveVarIdFromIdentifier(self, ident_node, current_cfg);
        }

        /// True when `ident_node` names a local binding of the analyzed
        /// function that holds a standard arena.
        ///
        /// Two proofs, both read out of this file. Either the declared type
        /// spells `std.heap.ArenaAllocator`, or the binding's own initializer
        /// is the `ArenaAllocator.init` constructor reached through a binding
        /// this file declares by importing `std`. The second route needs no
        /// written type and no project file list, so `var arena =
        /// verified_std.heap.ArenaAllocator.init(gpa);` is recognized in a
        /// single file on its own. Neither route is satisfied by a name: a
        /// value called `arena` proves nothing, and a type or namespace of the
        /// user's own that is spelled like the standard one is not the
        /// standard one.
        ///
        /// Neither route speaks for a binding the frame writes over. The type
        /// is what the binding was declared with and the constructor is what
        /// it was initialized with; both are settled by the write, and the
        /// value an allocation runs through is neither of them.
        fn isArenaBinding(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            ident_node: u32,
        ) bool {
            if (!bindingIsStableInFrame(self, tree, current_cfg, ident_node)) return false;
            if (allocator_utils.isArenaAllocatorExpr(tree, self.type_context, ident_node)) return true;
            return isArenaInitializerBinding(self, tree, current_cfg, ident_node);
        }

        /// The binding's own initializer is the standard arena constructor.
        fn isArenaInitializerBinding(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            ident_node: u32,
        ) bool {
            const tags = tree.nodes.items(.tag);
            if (ident_node >= tags.len or tags[ident_node] != .identifier) return false;
            const decl_info = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, ident_node, current_cfg) orelse return false;
            if (decl_info.is_top_level) return false;
            const full = tree.fullVarDecl(@enumFromInt(decl_info.decl_node)) orelse return false;
            const init = full.ast.init_node.unwrap() orelse return false;
            return isStdArenaInitializer(self, tree, @intFromEnum(init));
        }

        /// True when nothing inside the analyzed function writes the binding
        /// `ident_node` names again.
        ///
        /// Both proofs of arena-ness read the value the binding holds where an
        /// allocation happens, and a binding that is written over may hold
        /// something else by then. A declared type outlives the write and a
        /// constructor ran before it, so neither survives it: the arena the
        /// type names and the `deinit` queued against the binding are not
        /// evidence about the value the allocation runs through. The frame is
        /// the boundary - a same-named binding of another function, and a
        /// write to a field of a same-named value, are both someone else's.
        fn bindingIsStableInFrame(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            ident_node: u32,
        ) bool {
            const tags = tree.nodes.items(.tag);
            if (ident_node >= tags.len or tags[ident_node] != .identifier) return false;
            const fn_node = current_cfg.fn_ast_node orelse return false;
            const parent_map = self.getParentMap(tree) catch return false;
            return bindingIsStable(tree, parent_map, ids.astIndex(fn_node), tree.nodes.items(.main_token)[ident_node]);
        }

        /// The standard arena constructor: `<std>.heap.ArenaAllocator.init(...)`
        /// where `<std>` is `std` because this file imports it. Only the
        /// constructor counts; a same-named method anywhere else proves
        /// nothing.
        fn isStdArenaInitializer(self: *_Engine, tree: *const std.zig.Ast, expr: u32) bool {
            const tags = tree.nodes.items(.tag);
            if (expr >= tags.len or !call_utils.isCallNode(tags[expr])) return false;
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(expr)) orelse return false;
            const callee: u32 = @intFromEnum(call.ast.fn_expr);
            if (callee >= tags.len or tags[callee] != .field_access) return false;
            const datas = tree.nodes.items(.data);
            const access = datas[callee].node_and_token;
            if (!fieldNameIs(tree, access[1], "init")) return false;
            const namespace: u32 = @intFromEnum(access[0]);
            if (namespace >= tags.len or tags[namespace] != .field_access) return false;
            const namespace_access = datas[namespace].node_and_token;
            if (!fieldNameIs(tree, namespace_access[1], "ArenaAllocator")) return false;
            const heap: u32 = @intFromEnum(namespace_access[0]);
            if (heap >= tags.len or tags[heap] != .field_access) return false;
            const heap_access = datas[heap].node_and_token;
            if (!fieldNameIs(tree, heap_access[1], "heap")) return false;
            return importsStdInFile(self, tree, @intFromEnum(heap_access[0]));
        }

        /// True when the root of a namespace expression is `std` because this
        /// file imports it, either written inline or through a binding the
        /// file declares. The binding's own initializer decides, so a local
        /// namespace that happens to be spelled `std`, or a declaration of the
        /// same name bound to another module, fails.
        fn importsStdInFile(self: *_Engine, tree: *const std.zig.Ast, root: u32) bool {
            if (import_resolver.importPathFromBuiltinCall(tree, root)) |path| {
                return std.mem.eql(u8, path, "std");
            }
            return verifiedStdBinding(self, tree, root);
        }

        /// `isVerifiedImportBinding` against this file alone, so the proof
        /// does not depend on a project file list being attached to the run.
        /// A file with parse errors, a foreign tree, or no source behind it
        /// proves nothing.
        fn verifiedStdBinding(self: *_Engine, tree: *const std.zig.Ast, node: u32) bool {
            const tags = tree.nodes.items(.tag);
            if (node >= tags.len or tags[node] != .identifier) return false;
            var files: [1]import_resolver.File = undefined;
            const resolver = localFileResolver(self, tree, &files) orelse return false;
            return resolver.isVerifiedImportBinding(node, "std");
        }

        /// A resolver over this source's own AST and nothing else. `files`
        /// stays owned by the caller, which is what the resolver borrows.
        fn localFileResolver(
            self: *_Engine,
            tree: *const std.zig.Ast,
            files: *[1]import_resolver.File,
        ) ?call_resolver.ProjectTypeResolver {
            const src = self.source orelse return null;
            files.* = .{.{ .path = src.getFilePath(), .tree = tree }};
            files[0].lexical_index = lexicalIndexFor(src, tree);
            return .{ .files = files, .file_index = 0 };
        }

        /// Prototype a call reaches, and how many leading parameters of it the
        /// call site does not write: written argument `i` is prototype
        /// parameter `i + implicit_self_count`. An instance call reaches its
        /// prototype through a receiver it writes no argument for, a namespace
        /// call writes every parameter the prototype names, and the resolver
        /// that settles it is the one that knows which of the two it is.
        ///
        /// That resolver reads this file through a project view it can also
        /// refuse: parse errors, an exhausted resolution budget, a binding it
        /// cannot place. A caller-arena release cannot rest on that, so a
        /// resolver that stays silent is answered from this file alone - and
        /// that fallback reaches the bare-name root function only, which takes
        /// no receiver. A method this file cannot resolve answers nothing at
        /// all rather than being read as the bare function it is spelled like.
        fn calleeTarget(self: *_Engine, tree: *const std.zig.Ast, call_node: u32) ?CalleeTarget {
            var files: [1]import_resolver.File = undefined;
            if (localFileResolver(self, tree, &files)) |resolver| {
                if (resolver.resolveCallableAtCall(call_node)) |info| {
                    if (info.file_index == 0) {
                        return .{
                            .proto_node = info.proto_node,
                            .implicit_self_count = info.implicit_self_count,
                        };
                    }
                }
            }
            const proto = rootFunctionProtoAt(self, tree, call_node) orelse return null;
            return .{ .proto_node = proto, .implicit_self_count = 0 };
        }

        /// Prototype of the one function this file declares at root scope that
        /// a call names, read without the project resolver.
        ///
        /// A bare identifier naming a root-level function provably reaches it:
        /// a function of a container is written `Container.name`, so only the
        /// root scope can answer to the bare name. Two declarations of that
        /// name leave the call ambiguous and answer nothing, and a binding of
        /// that name reaching the call - a local, a parameter - has taken the
        /// callee over, which the lexical index settles.
        fn rootFunctionProtoAt(self: *_Engine, tree: *const std.zig.Ast, call_node: u32) ?u32 {
            const tags = tree.nodes.items(.tag);
            const token_tags = tree.tokens.items(.tag);
            if (call_node >= tags.len or !call_utils.isCallNode(tags[call_node])) return null;
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return null;
            const callee: u32 = @intFromEnum(call.ast.fn_expr);
            if (callee >= tags.len or tags[callee] != .identifier) return null;
            const callee_token = tree.nodes.items(.main_token)[callee];
            if (callee_token >= token_tags.len or token_tags[callee_token] != .identifier) return null;
            const name = import_resolver.normalizeIdentifier(tree.tokenSlice(callee_token));

            var found: ?u32 = null;
            for (tree.rootDecls()) |root| {
                const decl: u32 = @intFromEnum(root);
                if (decl >= tags.len or tags[decl] != .fn_decl) continue;
                const proto = functionProtoNode(tree, decl) orelse continue;
                const name_token = prototypeNameToken(tree, proto) orelse continue;
                if (name_token >= token_tags.len or token_tags[name_token] != .identifier) continue;
                if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(name_token)), name)) continue;
                if (found != null) return null;
                found = proto;
            }
            const proto = found orelse return null;

            const src = self.source orelse return null;
            const index = lexicalIndexFor(src, tree) orelse return null;
            if (index.findBinding(name, callee_token) != null) return null;
            return proto;
        }

        fn callSiteReleasesArena(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            caller_cfg: *const Cfg,
            call: std.zig.Ast.full.Call,
            call_node: u32,
            param_index: usize,
            root: RootPath,
        ) bool {
            if (param_index >= call.ast.params.len) {
                return false;
            }
            const arg: u32 = @intFromEnum(call.ast.params[param_index]);
            // The initializer the call is credited from describes the context
            // as it was declared. The call only proves the caller releases the
            // arena while that is still what the context holds.
            if (!callerContextStableAtCall(
                self,
                tree,
                parent_map,
                caller_fn,
                caller_cfg,
                call_node,
                arg,
                root.fields[0..root.depth],
            )) {
                return false;
            }
            const value = argumentValue(self, tree, caller_cfg, arg, 0) orelse {
                return false;
            };
            const field_value = selectFieldPath(self, tree, parent_map, caller_fn, caller_cfg, value, root.fields[0..root.depth], 0, 0) orelse {
                return false;
            };
            const arena = arenaOwnerOf(self, tree, caller_cfg, field_value, 0) orelse {
                return false;
            };
            if (!arenaDisposedInCaller(self, tree, parent_map, caller_fn, caller_cfg, call_node, arena)) {
                return false;
            }
            return true;
        }

        /// True when the context the argument reads through still holds what it
        /// was declared with where the call sits.
        ///
        /// The initializer a call site is credited from describes the context
        /// as it was declared. A write between that declaration and the call -
        /// straight onto the binding, onto a field along the path to the
        /// allocator, through a pointer taken of either, or through a hand-off
        /// whose own frame writes to what it receives - leaves the call holding
        /// something the arena the caller disposes never owned. What the caller
        /// does after the call is none of this acquisition's business: the
        /// blocks are charged by then.
        ///
        /// A method reaches its callee through the receiver the call is written
        /// with, and writes no argument for it at the call site, so a call on
        /// the context itself is read as a hand-off of that context.
        ///
        /// Bindings are read by identity, not by their spelling, so a same-named
        /// binding of an inner scope and a call that takes a plain number leave a
        /// verified hand-off alone.
        fn callerContextStableAtCall(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            caller_cfg: *const Cfg,
            call_node: u32,
            arg: u32,
            fields: []const []const u8,
        ) bool {
            // `scratch` collects the fields the argument reads to reach its
            // binding; the caller only asks which binding that is.
            var scratch = FieldChain{};
            // A value built for this call - a struct literal, a field read - is
            // written where it is used and cannot have been written over since.
            var base = fieldChainOf(tree, arg, &scratch) orelse {
                return true;
            };
            // A call handed a pointer is handed the binding that pointer points
            // into: `formatInside(slot)` where `slot` holds the address of the
            // context settles on that context, and the arena the caller proves
            // it disposes is the one inside it. Reading the binding the local
            // itself names instead would follow the lifetime of the local rather
            // than the one of the context the arena rides in. A value written
            // out for the call keeps the binding its own field chain names.
            if (scratch.len == 0) {
                if (pointerArgumentSource(self, tree, caller_cfg, arg)) |source| base = source;
            }
            // A target that does not resolve is not shown to be another binding.
            const target = _Engine.VarResolution.resolveVarIdFromIdentifier(self, base, caller_cfg) orelse {
                return false;
            };

            var aliases: [max_context_aliases]ids.VarId = undefined;
            var alias_count: usize = 0;
            collectContextAliases(
                self,
                tree,
                parent_map,
                caller_fn,
                caller_cfg,
                target,
                fields,
                false,
                // The answer here is about the binding the argument names, so
                // whether that binding is a pointer decides nothing.
                false,
                &aliases,
                &alias_count,
            );

            const call_path = statementPath(tree, parent_map, caller_fn, call_node) orelse {
                return false;
            };

            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            for (tags, 0..) |tag, index| {
                const node: u32 = @intCast(index);
                if (node == call_node) continue;
                if (!isAssignTag(tag) and !call_utils.isCallNode(tag)) continue;
                // A frame of its own is not this frame's story.
                if (enclosingBody(tags, parent_map, node) != caller_fn) continue;
                // A statement that cannot be placed against the call is taken
                // to run before it: an unplaced write settles nothing.
                const path = statementPath(tree, parent_map, caller_fn, node) orelse {
                    return false;
                };
                if (!nodeRunsBefore(&path, node, &call_path, call_node)) continue;

                if (isAssignTag(tag)) {
                    if (contextWrittenOver(
                        self,
                        tree,
                        caller_cfg,
                        @intFromEnum(datas[node].node_and_node[0]),
                        target,
                        aliases[0..alias_count],
                        fields,
                    )) {
                        return false;
                    }
                    continue;
                }
                if (callHandsOutContext(
                    self,
                    tree,
                    parent_map,
                    node,
                    caller_cfg,
                    target,
                    aliases[0..alias_count],
                    fields,
                )) {
                    return false;
                }
                if (callHandsOutReceiver(
                    self,
                    tree,
                    parent_map,
                    node,
                    caller_cfg,
                    target,
                    aliases[0..alias_count],
                    fields,
                )) {
                    return false;
                }
            }
            return true;
        }

        /// True when an assignment lands on the context the call reads, on a
        /// field the allocator path runs through, or on a binding that holds a
        /// pointer to either. A field beside that path names something else
        /// entirely and says nothing about the allocator being handed over.
        fn contextWrittenOver(
            self: *_Engine,
            tree: *const std.zig.Ast,
            caller_cfg: *const Cfg,
            lhs: u32,
            target: ids.VarId,
            aliases: []const ids.VarId,
            fields: []const []const u8,
        ) bool {
            var chain = FieldChain{};
            const base = fieldChainOf(tree, lhs, &chain) orelse return false;
            const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, base, caller_cfg) orelse return true;
            if (!reachesContext(bound, target, aliases)) return false;
            return chain.len == 0 or chainReachesPath(&chain, fields);
        }

        /// True when an earlier call receives the context, or a field of it, by
        /// address: written out as `&ctx`, reached through a binding that holds
        /// such a pointer, or wrapped in whatever the argument puts around it.
        /// The receiver a call is reached through is read separately, by
        /// `callHandsOutReceiver`.
        ///
        /// What the callee does with it decides. A frame that only reads a
        /// field off its parameter leaves the caller's binding alone, which is
        /// what makes a second hand-off of the same context sound; one that
        /// writes to it does not, and neither does a callee this file cannot
        /// read.
        fn callHandsOutContext(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            call_node: u32,
            caller_cfg: *const Cfg,
            target: ids.VarId,
            aliases: []const ids.VarId,
            fields: []const []const u8,
        ) bool {
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return false;
            for (call.ast.params, 0..) |param, param_index| {
                var finder = ContextAddressFinder{
                    .engine = self,
                    .parent_map = parent_map,
                    .frame_cfg = caller_cfg,
                    .target = target,
                    .aliases = aliases,
                    .fields = fields,
                };
                ast_walk.walk(ContextAddressFinder, tree, @intFromEnum(param), &finder) catch return true;
                if (!finder.found) continue;
                if (calleeMutatesArgument(self, tree, parent_map, call_node, param_index, true)) return true;
            }
            return false;
        }

        /// True when a call reaches its callee through a receiver that is the
        /// context, or a binding holding its address. `ctx.rebind(gpa)` hands
        /// the whole context over without an argument written for it at the call
        /// site, so the receiver is the one parameter of the callee the caller
        /// never spells out. A call written in `.call` form reaches its callee
        /// this way whichever shape the call itself is written in.
        ///
        /// The name the call is written with is the method rather than a field
        /// of the receiver's value, so it is walked off and only the fields read
        /// in front of it answer the path question. A field beside the path the
        /// allocator arrives through is a value of its own, and the name of a
        /// namespace call is a type of the program's rather than a value of the
        /// caller's, so neither settles anything here.
        fn callHandsOutReceiver(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            call_node: u32,
            caller_cfg: *const Cfg,
            target: ids.VarId,
            aliases: []const ids.VarId,
            fields: []const []const u8,
        ) bool {
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return false;
            const tags = tree.nodes.items(.tag);
            var expr: u32 = @intFromEnum(call.ast.fn_expr);
            if (expr < tags.len and tags[expr] == .field_access) {
                expr = @intFromEnum(tree.nodes.items(.data)[expr].node_and_token[0]);
            }
            var chain = FieldChain{};
            const base = fieldChainOf(tree, expr, &chain) orelse return false;
            const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, base, caller_cfg) orelse return false;
            if (!reachesContext(bound, target, aliases)) return false;
            if (chain.len != 0 and !chainReachesPath(&chain, fields)) return false;
            // The offset the callable resolves to is what tells a receiver that
            // arrives as a parameter from a namespace name that does not, and
            // nothing about the spelling of the call decides it.
            const callee = calleeTarget(self, tree, call_node) orelse return true;
            if (callee.implicit_self_count == 0) return false;
            const callee_fn = declarationOfProto(tree, callee.proto_node) orelse return true;
            return calleeFrameMutatesParameter(self, tree, parent_map, callee_fn, 0, true);
        }

        /// Bindings of `frame_fn` that hold the address of the context, of a
        /// field on the path to its allocator, or of another such binding. A
        /// write through one of them lands where a write through the context
        /// itself does.
        ///
        /// `pointer_only` keeps the plain reads out: a caller reads the context
        /// to know what it declared it with, while a frame that only reads its
        /// context leaves it alone and has to keep doing so. `fields` is null
        /// when the question is about the context as a whole and not about the
        /// one field the allocator arrives through.
        ///
        /// `root_is_pointer` says the target itself holds a pointer, which
        /// `pointer_only` cannot read off an initializer: a copy of it is that
        /// same pointer under another name, while a copy of a context handed
        /// over by value is a value of its own.
        fn collectContextAliases(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            frame_fn: u32,
            frame_cfg: *const Cfg,
            target: ids.VarId,
            fields: ?[]const []const u8,
            pointer_only: bool,
            root_is_pointer: bool,
            aliases: *[max_context_aliases]ids.VarId,
            count: *usize,
        ) void {
            const tags = tree.nodes.items(.tag);
            // One round per level of aliasing: a pointer taken of a pointer
            // taken of the context is found by the round after the first.
            var rounds: usize = 0;
            while (rounds < 4) : (rounds += 1) {
                var added = false;
                for (tags, 0..) |tag, index| {
                    if (!isVarDeclTag(tag)) continue;
                    const node: u32 = @intCast(index);
                    if (!ast_walk.isAncestor(frame_fn, node, parent_map)) continue;
                    if (count.* >= aliases.len) return;
                    const alias = _Engine.VarResolution.resolveVarIdFromVarDecl(self, node) orelse continue;
                    if (alias == target) continue;
                    if (reachesContext(alias, target, aliases[0..count.*])) continue;
                    const full = tree.fullVarDecl(@enumFromInt(node)) orelse continue;
                    const init = full.ast.init_node.unwrap() orelse continue;
                    if (!initializerTakesContextAddress(
                        self,
                        tree,
                        parent_map,
                        frame_cfg,
                        @intFromEnum(init),
                        target,
                        aliases[0..count.*],
                        fields,
                        pointer_only,
                        root_is_pointer,
                    )) continue;
                    aliases[count.*] = alias;
                    count.* += 1;
                    added = true;
                }
                if (!added) return;
            }
        }

        /// True when an initializer takes the address of the context, or of a
        /// field on the path to its allocator, or of a binding that already
        /// holds such an address.
        ///
        /// A context reached through a pointer parameter can be copied out of
        /// one as it stands: `const alias = context;` is that same pointer
        /// under another name, and a write through it lands in the caller's
        /// context exactly where one through the parameter itself does.
        fn initializerTakesContextAddress(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            frame_cfg: *const Cfg,
            init: u32,
            target: ids.VarId,
            aliases: []const ids.VarId,
            fields: ?[]const []const u8,
            pointer_only: bool,
            root_is_pointer: bool,
        ) bool {
            var finder = ContextAddressFinder{
                .engine = self,
                .parent_map = parent_map,
                .frame_cfg = frame_cfg,
                .target = target,
                .aliases = aliases,
                .fields = fields,
                .pointer_only = pointer_only,
                .root_is_pointer = root_is_pointer,
                .init_expr = init,
            };
            ast_walk.walk(ContextAddressFinder, tree, init, &finder) catch return true;
            return finder.found;
        }

        /// True when the frame of `callee_fn` writes to the parameter at
        /// `param_index`, which is what an earlier hand-off of the context to it
        /// settles. Every way of not answering proves a write rather than
        /// clearing one, so a frame this file cannot read never lets a
        /// hand-off through. `may_descend` bounds the answer to this frame's
        /// own bindings: a hand-off it makes itself is settled without reading
        /// the frame that hand-off would reach.
        fn calleeFrameMutatesParameter(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            callee_fn: u32,
            param_index: usize,
            may_descend: bool,
        ) bool {
            var params: [max_params]std.zig.Ast.TokenIndex = undefined;
            const param_count = prototypeParamNames(tree, callee_fn, &params) orelse return true;
            if (param_index >= param_count) return true;
            // A parameter this file cannot name cannot be read: nothing proves
            // that the frame leaves it alone.
            if (params[param_index] == no_param_name) return true;
            const param_var = ids.varId(params[param_index]);
            const callee_cfg = (self.getOrBuildFunctionCfg(ids.astId(callee_fn)) catch return true) orelse return true;
            _Engine.VarResolution.prepare(self, callee_cfg) catch return true;
            // A binding of this frame that holds the address of the parameter
            // reaches as far as the parameter does, so the frame's own
            // bindings answer here as well. Which field of the context the
            // allocator arrives through is the caller's question: every field
            // of the parameter counts.
            var aliases: [max_context_aliases]ids.VarId = undefined;
            var alias_count: usize = 0;
            collectContextAliases(
                self,
                tree,
                parent_map,
                callee_fn,
                callee_cfg,
                param_var,
                null,
                true,
                parameterIsPointer(tree, callee_fn, param_index),
                &aliases,
                &alias_count,
            );
            if (parameterEscapes(self, tree, callee_cfg, callee_fn, parent_map, param_var, aliases[0..alias_count], may_descend)) return true;
            return parameterIsWrittenTo(self, tree, callee_cfg, parent_map, callee_fn, param_var, aliases[0..alias_count], null);
        }

        /// True when the frame of the function this call reaches writes to the
        /// argument at `param_index`, or cannot be read to answer that. The one
        /// oracle every hand-off of a pointer is settled by, whichever frame
        /// makes it.
        fn calleeMutatesArgument(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            call_node: u32,
            param_index: usize,
            may_descend: bool,
        ) bool {
            const callee = calleeTarget(self, tree, call_node) orelse return true;
            const callee_fn = declarationOfProto(tree, callee.proto_node) orelse return true;
            // An instance call writes no argument for the receiver it is
            // reached through, and a namespace call writes every parameter the
            // prototype names. The offset the callable resolves to is what
            // tells the two apart; nothing about the spelling of the call
            // decides it.
            return calleeFrameMutatesParameter(self, tree, parent_map, callee_fn, param_index + callee.implicit_self_count, may_descend);
        }

        /// Looks for the address of a context, or of a binding that holds one,
        /// anywhere inside an expression. The shape of the expression around it
        /// is not read, so `&ctx`, `@constCast(&ctx)` and a context buried in a
        /// call of its own all answer the same.
        ///
        /// `pointer_only` narrows the answer to the initializers that take the
        /// address of the context: reading a field off it is not taking its
        /// address, and a binding initialized from such a read holds a value
        /// rather than a pointer into the caller's context.
        /// `root_is_pointer` reads the target itself rather than its
        /// initializer: a context reached through a pointer parameter is copied
        /// out of it by name alone. That copy settles nothing unless the bare
        /// name is the whole initializer - `const alias = context;` is that
        /// pointer under another name, while `const label =
        /// allocPrint(context.pool, ...);` reads one field of it inside an
        /// expression of its own and builds a value of that expression rather
        /// than a pointer into the context. `init_expr` names the expression
        /// the search started from, which is what tells the two apart.
        /// `fields` names the path the allocator arrives through, and null
        /// leaves the field question to the caller of the search.
        const ContextAddressFinder = struct {
            engine: *_Engine,
            parent_map: []const u32,
            frame_cfg: *const Cfg,
            target: ids.VarId,
            aliases: []const ids.VarId,
            fields: ?[]const []const u8,
            pointer_only: bool = false,
            root_is_pointer: bool = false,
            init_expr: u32 = 0,
            stop: bool = false,
            found: bool = false,

            pub fn visit(self: *@This(), tree: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) anyerror!void {
                if (self.stop) return;
                var chain = FieldChain{};
                var binding: ?u32 = null;
                var address_taken = false;
                // A path this file cannot place leaves the field question open
                // rather than answered by a prefix of a longer chain.
                var fields = self.fields;
                switch (tag) {
                    // A binding that holds the address is the address itself,
                    // however the expression hands it on.
                    .identifier => {
                        binding = node;
                        // A value read off a field of the context is a value of
                        // its own: `var length = ctx.name.len;` writes into the
                        // binding that holds it and nowhere near the allocator,
                        // so the fields read off the identifier are read here.
                        if (!fieldChainAbove(tree, self.parent_map, node, &chain)) fields = null;
                    },
                    .address_of => {
                        const operand = nodeChild(tree, node) orelse return;
                        binding = fieldChainOf(tree, operand, &chain);
                        address_taken = true;
                    },
                    else => return,
                }
                const base = binding orelse return;
                const whole = isWholeExpression(tree, self.parent_map, node, self.init_expr);
                if (!self.reaches(base, address_taken, whole)) return;
                if (fields) |path| {
                    // A field beside the allocator path is a value of its own:
                    // the callee is handed something the arena never owned.
                    if (chain.len != 0 and !chainReachesPath(&chain, path)) return;
                }
                self.found = true;
                self.stop = true;
            }

            /// True when the base names the context itself, or a binding that
            /// already holds a pointer to it.
            ///
            /// A search that only wants pointers is answered by an address
            /// taken of the base, or by the base standing there as the whole
            /// expression - a copy of the pointer the target holds is that same
            /// pointer under another name, whatever wraps the name. The target
            /// itself is read the same way unless it is a value rather than a
            /// pointer, in which case any reference to it reaches it.
            fn reaches(self: *@This(), base: u32, address_taken: bool, whole: bool) bool {
                const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self.engine, base, self.frame_cfg) orelse return true;
                if (bound == self.target) {
                    if (!self.pointer_only) return true;
                    return address_taken or (self.root_is_pointer and whole);
                }
                if (!reachesContext(bound, self.target, self.aliases)) return false;
                // An alias already tracked hands that pointer on the same way
                // the target does, and no further: reading a field off it
                // inside an expression of its own builds a value of that
                // expression rather than a pointer into the context.
                return !self.pointer_only or address_taken or whole;
            }
        };

        /// True when the caller releases the arena after this call or hands it
        /// back.
        ///
        /// The arena has to be settled on every way out of the caller the call
        /// can still reach. A `defer` written as a statement of a scope the call
        /// sits inside runs when that scope ends, so it settles every exit out
        /// of that scope at once - but only where it is written ahead of the
        /// exit it settles. A `defer` written behind an exit of that scope has
        /// not registered by the time control takes it, and that exit settles
        /// nothing:
        ///
        ///     if (drop) return null;
        ///     defer arena.deinit();
        ///
        /// The end of the frame's own body is one exit of its own, and it sits
        /// at that end rather than at the call, so a `defer` written below the
        /// call is registered before control reaches it.
        ///
        /// An `errdefer` settles the one exit a `try` over the call can take,
        /// and the exits that hand an error value back, and nothing else: it
        /// never runs on a success path, so a hand-off it stands beside still
        /// has to carry the arena out of every success exit of its own.
        ///
        /// Handing the arena back counts exit by exit, and only where the
        /// returned expression carries the arena itself. `return
        /// arena.capacity;` hands back a number, `return null;` hands back
        /// nothing at all, and what the arena holds stays charged to a frame
        /// that is gone either way. One exit that carries the arena and one
        /// beside it that does not are a leak on the second, so an exit this
        /// file cannot place against the call settles nothing either. A return
        /// whose own operand is the block the call sits in is an exit the call
        /// does reach, and it counts like any other.
        ///
        /// A bare `deinit()` statement runs on the one path that reaches it. It
        /// settles the exit written after it in the very block both are
        /// statements of, and the fall off the end of the frame only when it
        /// follows the call as the very next statement of that same block,
        /// where nothing sits between the two to leave the block first.
        ///
        /// A `defer` settles every way out of the scope it was written in, and
        /// through that every exit written after the scope has run to its end:
        /// the disposal has happened by the time the frame reaches it.
        ///
        /// Every disposal and every exit below is read out of the caller's own
        /// frame. One written in a function nested inside it belongs to that
        /// frame, and settles nothing here.
        fn arenaDisposedInCaller(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            caller_cfg: *const Cfg,
            call_node: u32,
            arena: ids.VarId,
        ) bool {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            // An exit this file cannot place against the call settles nothing.
            const call_path = statementPath(tree, parent_map, caller_fn, call_node) orelse return false;

            // Disposals written in the caller itself, read once each. A `defer`
            // and an `errdefer` are kept apart from a bare statement, because
            // only the first two run on a path of their own.
            var deferred: [max_caller_deinits]u32 = undefined;
            var deferred_count: usize = 0;
            var plain_deinits: [max_caller_deinits]u32 = undefined;
            var plain_count: usize = 0;
            for (tags, 0..) |tag, index| {
                const node: u32 = @intCast(index);
                if (!call_utils.isCallNode(tag)) continue;
                // A frame of its own is not this frame's story.
                if (enclosingBody(tags, parent_map, node) != caller_fn) continue;
                if (!isArenaDeinit(self, tree, caller_cfg, node, arena)) continue;
                if (parentOfDeferred(tree, parent_map, node)) |defer_node| {
                    if (deferred_count >= deferred.len) continue;
                    deferred[deferred_count] = defer_node;
                    deferred_count += 1;
                    continue;
                }
                if (plain_count >= plain_deinits.len) continue;
                plain_deinits[plain_count] = node;
                plain_count += 1;
            }

            // What is left is the hand-off, and it is settled exit by exit: a
            // caller that carries the arena out of one path and drops it on
            // another leaks on the second.
            for (tags, 0..) |tag, index| {
                const node: u32 = @intCast(index);
                if (tag != .@"return") continue;
                if (enclosingBody(tags, parent_map, node) != caller_fn) continue;
                // A return whose operand is where the call sits is reached by
                // it: `return blk: { call(); break :blk null; };` leaves the
                // frame through that return, not before it.
                if (!ast_walk.isAncestor(node, call_node, parent_map)) {
                    const exit_path = statementPath(tree, parent_map, caller_fn, node) orelse return false;
                    // An exit the call never reaches settles nothing here.
                    if (nodeRunsBefore(&exit_path, node, &call_path, call_node)) continue;
                }
                // Carried on the value, or disposed on a path that has run.
                var error_exit = false;
                if (datas[node].opt_node.unwrap()) |ret_expr| {
                    const value: u32 = @intFromEnum(ret_expr);
                    if (expressionCarriesArena(self, tree, parent_map, caller_fn, caller_cfg, value, arena, 0)) continue;
                    error_exit = returnsErrorValue(tree, value);
                }
                var settled = false;
                for (plain_deinits[0..plain_count]) |deinit| {
                    if (deinitRunsBeforeExit(tree, parent_map, deinit, node)) {
                        settled = true;
                        break;
                    }
                }
                // An `errdefer` runs when the frame leaves holding an error and
                // on nothing else, so which exits it settles is what the value
                // handed back decides.
                if (!settled) {
                    for (deferred[0..deferred_count]) |defer_node| {
                        if (tags[defer_node] == .@"errdefer" and !error_exit) continue;
                        if (deferSettlesExit(tree, parent_map, caller_fn, defer_node, node)) {
                            settled = true;
                            break;
                        }
                    }
                }
                if (!settled) return false;
            }

            // An activated defer or errdefer also covers a failed `try`.
            if (enclosingTry(tree, parent_map, call_node) != null) {
                var covered = false;
                for (deferred[0..deferred_count]) |defer_node| {
                    if (deferSettlesExit(tree, parent_map, caller_fn, defer_node, call_node)) {
                        covered = true;
                        break;
                    }
                }
                if (!covered) return false;
            }

            // Running off the end of the frame's own body is an exit of its own,
            // and a body whose last statement never finishes has no way out that
            // way. That exit sits at the end of the body, not at the call:
            // control below the call runs on to that end, so a `defer` written
            // behind the call has been registered by the time the frame gets
            // there. A block inside the body does not end the frame, so what
            // falls off the end of one of those carries on in the body around
            // it.
            if (frameFallsOff(tree, caller_fn)) {
                var settled = false;
                for (deferred[0..deferred_count]) |defer_node| {
                    if (tags[defer_node] == .@"errdefer") continue;
                    if (deferSettlesFallOff(tree, parent_map, caller_fn, defer_node)) {
                        settled = true;
                        break;
                    }
                }
                if (!settled) {
                    for (plain_deinits[0..plain_count]) |deinit| {
                        if (plainDeinitFollowsCall(tree, parent_map, call_node, deinit)) {
                            settled = true;
                            break;
                        }
                    }
                }
                if (!settled) return false;
            }
            return true;
        }

        /// True when the expression hands the arena itself on, by value. A field
        /// read is a value of its own - a capacity, a size - and carrying the
        /// arena means the binding is the expression, sits inside one that
        /// holds it, or is a local of the frame that was built out of it. The
        /// address of the binding is not a hand-off: what comes back then is a
        /// pointer into a frame that is gone, and everything the arena holds
        /// rides out behind a dead pointer.
        ///
        /// The binding is read by identity through the caller's own scopes, so
        /// the arena a `return` names is the arena it was declared as: another
        /// binding that only spells the name the same way carries nothing.
        fn expressionCarriesArena(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            caller_cfg: *const Cfg,
            expr: u32,
            arena: ids.VarId,
            depth: u8,
        ) bool {
            if (depth >= 8) return false;
            const tags = tree.nodes.items(.tag);
            if (expr >= tags.len) return false;
            switch (tags[expr]) {
                .identifier => {
                    const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, expr, caller_cfg) orelse return false;
                    // The arena this exit carries is the arena the frame
                    // declared only while nothing has written that binding
                    // over. A binding rebound to an arena of its own rides out
                    // holding nothing the frame ever allocated through.
                    if (bound == arena) {
                        return bindingIsUnwritten(self, tree, parent_map, caller_fn, caller_cfg, expr, arena);
                    }
                    // A binding that holds the arena carries it the way the
                    // arena itself does: `const owner = .{ .arena = arena };
                    // return owner;` hands the arena on inside the value.
                    return bindingCarriesArena(self, tree, parent_map, caller_fn, caller_cfg, expr, arena, depth + 1);
                },
                .grouped_expression, .deref, .unwrap_optional, .@"try", .@"catch" => {
                    const child = nodeChild(tree, expr) orelse return false;
                    return expressionCarriesArena(self, tree, parent_map, caller_fn, caller_cfg, child, arena, depth + 1);
                },
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
                    const struct_init = tree.fullStructInit(&buffer, @enumFromInt(expr)) orelse return false;
                    for (struct_init.ast.fields) |field| {
                        const value = structInitFieldValue(tree, @intFromEnum(field)) orelse return false;
                        if (expressionCarriesArena(self, tree, parent_map, caller_fn, caller_cfg, value, arena, depth + 1)) return true;
                    }
                    return false;
                },
                else => return false,
            }
        }

        /// True when the local binding `ident` names holds the arena inside what
        /// it was declared with. The declaration has to be a local of this
        /// frame - a binding of another frame is settled by that frame - and
        /// nothing in the frame may have written it over, or what it holds by
        /// the time the frame leaves is something else entirely.
        fn bindingCarriesArena(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            caller_cfg: *const Cfg,
            ident: u32,
            arena: ids.VarId,
            depth: u8,
        ) bool {
            const decl_info = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, ident, caller_cfg) orelse return false;
            if (decl_info.is_top_level) return false;
            const full = tree.fullVarDecl(@enumFromInt(decl_info.decl_node)) orelse return false;
            const init = full.ast.init_node.unwrap() orelse return false;
            if (!bindingIsUnwritten(self, tree, parent_map, caller_fn, caller_cfg, ident, arena)) return false;
            return expressionCarriesArena(self, tree, parent_map, caller_fn, caller_cfg, @intFromEnum(init), arena, depth);
        }

        /// True when nothing inside `caller_fn` writes the binding `ident` names
        /// again. A binding that is assigned over holds a different value by the
        /// time the frame leaves, so what it was declared with proves nothing.
        /// Both sides are read through the frame's own scopes, so it is the same
        /// binding that is compared and not two names alike. A write this file
        /// cannot place against the binding is not read as one here.
        ///
        /// A write reaches the binding through more than the bare name of it:
        /// through a field the arena rides under - `owner.arena = other` - and
        /// through a pointer a binding of this frame holds to it or to that
        /// field. A field beside that path holds a value of its own and leaves
        /// the arena where the declaration put it. The address of the binding,
        /// or of the field, handed to another function settles nothing either:
        /// what that frame writes through it is not written out in this one.
        fn bindingIsUnwritten(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            caller_cfg: *const Cfg,
            ident: u32,
            arena: ids.VarId,
        ) bool {
            const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, ident, caller_cfg) orelse return false;
            // Where inside the binding the arena rides, so that a write to a
            // field of its own is told apart from a write to a field beside it.
            var arena_path = FieldChain{};
            var arena_fields: []const []const u8 = arena_path.names[0..0];
            if (declaredInitializer(self, tree, caller_cfg, ident)) |init| {
                if (arenaFieldPath(self, tree, caller_cfg, init, arena, &arena_path, 0)) {
                    arena_fields = arena_path.names[0..arena_path.len];
                }
            }
            // A pointer a binding of this frame holds to it, or to a field the
            // arena rides under: a write through one lands where a write
            // through the binding itself lands.
            var aliases: [max_context_aliases]ids.VarId = undefined;
            var alias_count: usize = 0;
            collectContextAliases(
                self,
                tree,
                parent_map,
                caller_fn,
                caller_cfg,
                bound,
                arena_fields,
                true,
                false,
                &aliases,
                &alias_count,
            );

            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            for (tags, 0..) |tag, index| {
                if (!isAssignTag(tag) and !call_utils.isCallNode(tag)) continue;
                const node: u32 = @intCast(index);
                if (!ast_walk.isAncestor(caller_fn, node, parent_map)) continue;
                if (call_utils.isCallNode(tag)) {
                    if (callHandsOutContext(self, tree, parent_map, node, caller_cfg, bound, aliases[0..alias_count], arena_fields)) {
                        return false;
                    }
                    continue;
                }
                const lhs: u32 = @intFromEnum(datas[node].node_and_node[0]);
                var chain = FieldChain{};
                const base = fieldChainOf(tree, lhs, &chain) orelse continue;
                const written = _Engine.VarResolution.resolveVarIdFromIdentifier(self, base, caller_cfg) orelse return false;
                if (!reachesContext(written, bound, aliases[0..alias_count])) continue;
                // The bare name of the binding, and any field the arena itself
                // rides under, replace what the exit carries. A field beside
                // that path is a value of its own.
                if (chain.len == 0) return false;
                if (arena_path.len == 0) continue;
                if (!std.mem.eql(u8, chain.names[0], arena_path.names[0])) continue;
                return false;
            }
            return true;
        }

        /// Fields a declared value carries the arena under, outermost first,
        /// written into `path`. False when the arena does not ride inside it.
        ///
        /// Only the path down to the arena is read: a field beside it holds a
        /// value of its own, and a write to that one swaps nothing the
        /// allocation was charged to.
        fn arenaFieldPath(
            self: *_Engine,
            tree: *const std.zig.Ast,
            caller_cfg: *const Cfg,
            value: u32,
            arena: ids.VarId,
            path: *FieldChain,
            depth: u8,
        ) bool {
            if (depth >= 8 or path.len >= max_field_depth) return false;
            const tags = tree.nodes.items(.tag);
            if (value >= tags.len) return false;
            switch (tags[value]) {
                .grouped_expression => {
                    const child = nodeChild(tree, value) orelse return false;
                    return arenaFieldPath(self, tree, caller_cfg, child, arena, path, depth + 1);
                },
                .identifier => {
                    const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, value, caller_cfg) orelse return false;
                    if (bound == arena) return true;
                    // A local of this frame declared as a copy of the arena
                    // carries it by value exactly as the arena itself does, so
                    // the walk follows that binding's own initializer:
                    // `.{ .arena = held }` rides the arena under `arena` once
                    // `held` was declared `const held = arena`, and a write to
                    // that field then replaces what the frame hands back. A
                    // binding of another frame is settled by that frame, and an
                    // initializer this walk cannot read - the address of the
                    // arena, a call, a field of the arena's own - carries
                    // nothing, so a pointer to the arena is never taken for the
                    // arena. The depth and the path are the only bounds.
                    const decl_info = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, value, caller_cfg) orelse return false;
                    if (decl_info.is_top_level) return false;
                    const init = declaredInitializer(self, tree, caller_cfg, value) orelse return false;
                    return arenaFieldPath(self, tree, caller_cfg, init, arena, path, depth + 1);
                },
                .struct_init,
                .struct_init_comma,
                .struct_init_one,
                .struct_init_one_comma,
                .struct_init_dot,
                .struct_init_dot_comma,
                .struct_init_dot_two,
                .struct_init_dot_two_comma,
                => {},
                else => return false,
            }
            var buffer: [2]std.zig.Ast.Node.Index = undefined;
            const struct_init = tree.fullStructInit(&buffer, @enumFromInt(value)) orelse return false;
            for (struct_init.ast.fields) |field| {
                const name_token = structInitFieldNameToken(tree, field) orelse continue;
                const entry = structInitFieldValue(tree, @intFromEnum(field)) orelse continue;
                path.names[path.len] = import_resolver.normalizeIdentifier(tree.tokenSlice(name_token));
                path.len += 1;
                if (arenaFieldPath(self, tree, caller_cfg, entry, arena, path, depth + 1)) return true;
                path.len -= 1;
            }
            return false;
        }

        /// Initializer of the local an identifier names, and null when it names
        /// no declaration of its own. The declaration is found through the
        /// frame's own scopes, so the binding a use site refers to is the
        /// declaration it was written in.
        fn declaredInitializer(
            self: *_Engine,
            tree: *const std.zig.Ast,
            caller_cfg: *const Cfg,
            ident: u32,
        ) ?u32 {
            const decl_info = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, ident, caller_cfg) orelse return null;
            const tags = tree.nodes.items(.tag);
            if (decl_info.decl_node >= tags.len or !isVarDeclTag(tags[decl_info.decl_node])) return null;
            const full = tree.fullVarDecl(@enumFromInt(decl_info.decl_node)) orelse return null;
            return @intFromEnum(full.ast.init_node.unwrap() orelse return null);
        }

        /// Value expression one field of a struct initializer carries. A field
        /// written out in full is a `container_field` node; the anonymous
        /// `.{ .arena = arena }` stores the value expression itself, so any
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

        /// True when `call_node` is `<arena>.deinit()` on the very binding the
        /// arena came from. The receiver is resolved through the caller's own
        /// scopes, so a same-named arena elsewhere in the file is a different
        /// binding and disposes nothing.
        fn isArenaDeinit(
            self: *_Engine,
            tree: *const std.zig.Ast,
            caller_cfg: *const Cfg,
            call_node: u32,
            arena: ids.VarId,
        ) bool {
            const tags = tree.nodes.items(.tag);
            var call_buf: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buf, @enumFromInt(call_node)) orelse return false;
            const callee: u32 = @intFromEnum(call.ast.fn_expr);
            if (callee >= tags.len or tags[callee] != .field_access) return false;
            const access = tree.nodes.items(.data)[callee].node_and_token;
            if (!fieldNameIs(tree, access[1], "deinit")) return false;
            const base: u32 = @intFromEnum(access[0]);
            if (base >= tags.len or tags[base] != .identifier) return false;
            const base_var = _Engine.VarResolution.resolveVarIdFromIdentifier(self, base, caller_cfg) orelse return false;
            return base_var == arena;
        }

        /// True when a bare `deinit()` has run by the time the frame leaves at
        /// `exit_node`: the disposal is a statement of the very block the exit
        /// leaves, written ahead of it. A `return` unwinds straight out of the
        /// frame, so nothing else can have run by then: a disposal written
        /// further out is jumped over, one behind it never runs on this path,
        /// and one written under a conditional of that block may never run at
        /// all.
        fn deinitRunsBeforeExit(
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            deinit_call: u32,
            exit_node: u32,
        ) bool {
            const block = enclosingBlock(tree, parent_map, exit_node) orelse return false;
            const from = directStatementIndex(tree, block, deinit_call) orelse return false;
            const to = reachedStatementIndex(tree, parent_map, block, exit_node) orelse return false;
            return from < to;
        }

        /// True when the deferred disposal written by `defer_node` settles the
        /// exit at `target`. It runs when the scope it was written in ends, so
        /// it settles an exit that scope contains when it is written ahead of
        /// the registration - a `defer` under a conditional is scheduled by
        /// that conditional and not by its place among the statements, and one
        /// written behind the target registers nothing the target can reach -
        /// and it settles an exit written after a scope it has certainly
        /// already left, which is how a block that runs to its end releases the
        /// arena the frame then returns out of.
        fn deferSettlesExit(
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            defer_node: u32,
            target: u32,
        ) bool {
            const scope = enclosingBlock(tree, parent_map, defer_node) orelse return false;
            const from = directStatementIndex(tree, scope, defer_node) orelse return false;
            if (reachedStatementIndex(tree, parent_map, scope, target)) |to| {
                return from < to;
            }
            return scopeEndsBeforeExit(tree, parent_map, caller_fn, scope, defer_node, target);
        }

        /// True when the deferred disposal written by `defer_node` has run by
        /// the time the frame runs off the end of its own body. Registration
        /// order inside a scope decides nothing about when that scope ends, so
        /// a disposal written below the call is registered before control
        /// reaches the end; the disposal still has to be a statement of a scope
        /// the frame reaches on its way there, and that scope has to run to its
        /// own end. A `break` out of it before the registration leaves the
        /// frame carrying what the arena holds without ever having registered
        /// it, so it settles nothing here.
        fn deferSettlesFallOff(
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            defer_node: u32,
        ) bool {
            const scope = enclosingBlock(tree, parent_map, defer_node) orelse return false;
            if (directStatementIndex(tree, scope, defer_node) == null) return false;
            if (scopeLeftBefore(tree, parent_map, scope, defer_node)) return false;
            return unconditionallyReachedBody(tree, parent_map, caller_fn, scope) != null;
        }

        /// True when control has certainly left `scope` by the time `target`
        /// runs, so a disposal registered in it has already happened. Every
        /// block between that scope and the frame's own body has to be a block
        /// of its own inside the block around it, and the frame has to reach
        /// the target only after the statement of the body that holds the
        /// scope - both are read off the paths the two nodes take.
        fn scopeEndsBeforeExit(
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            scope: u32,
            defer_node: u32,
            target: u32,
        ) bool {
            if (unconditionallyReachedBody(tree, parent_map, caller_fn, scope) == null) return false;
            // A `break` out of the scope ahead of the disposal leaves the frame
            // without ever having registered it, so it cannot have run yet.
            if (scopeLeftBefore(tree, parent_map, scope, defer_node)) return false;
            const defer_path = statementPath(tree, parent_map, caller_fn, defer_node) orelse return false;
            const target_path = statementPath(tree, parent_map, caller_fn, target) orelse return false;
            return nodeRunsBefore(&defer_path, defer_node, &target_path, target);
        }

        /// True when a bare `deinit()` is written immediately after the call, in
        /// the very block both of them sit in. Nothing between the two can leave
        /// that block first, so the way out of the frame that reaches past the
        /// call runs it.
        fn plainDeinitFollowsCall(
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            call_node: u32,
            deinit_call: u32,
        ) bool {
            const block = enclosingBlock(tree, parent_map, deinit_call) orelse return false;
            if (enclosingBlock(tree, parent_map, call_node) != block) return false;
            const from = reachedStatementIndex(tree, parent_map, block, call_node) orelse return false;
            const to = directStatementIndex(tree, block, deinit_call) orelse return false;
            return to == from + 1;
        }

        /// The `try` a call is written under, or null when the call cannot leave
        /// the caller with an error of its own. Only the wrappers that leave
        /// the call alone are walked off.
        fn enclosingTry(
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            node: u32,
        ) ?u32 {
            const tags = tree.nodes.items(.tag);
            var current = node;
            var steps: u32 = 0;
            while (steps < 8 and current < parent_map.len) : (steps += 1) {
                const parent = parent_map[current];
                if (parent == 0 or parent >= tags.len) return null;
                switch (tags[parent]) {
                    .grouped_expression => current = parent,
                    .@"try" => return parent,
                    else => return null,
                }
            }
            return null;
        }

        /// True when the frame uses the context for anything but reading a
        /// field off it, or hands a binding that holds its address to anything
        /// but a read of it. Storing it, handing it to another function or
        /// returning it all let the allocator outlive the arena the caller
        /// disposes, so nothing the caller did carries over to here.
        ///
        /// `may_descend` keeps the two frames from chasing each other: a
        /// hand-off is settled by the frame it reaches, and that frame answers
        /// from its own bindings alone.
        fn parameterEscapes(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            fn_index: u32,
            parent_map: []const u32,
            root_var: ids.VarId,
            aliases: []const ids.VarId,
            may_descend: bool,
        ) bool {
            const tags = tree.nodes.items(.tag);
            for (tags, 0..) |tag, node_index| {
                const node: u32 = @intCast(node_index);
                if (tag != .identifier) continue;
                if (!ast_walk.isAncestor(fn_index, node, parent_map)) continue;
                const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, node, current_cfg) orelse return true;
                // The context itself and the bindings of this frame that hold
                // its address all reach what the caller disposes.
                if (!reachesContext(bound, root_var, aliases)) continue;
                // The name a declaration this set already holds is written
                // with is that declaration's own address: a local that copies
                // one tracked pointer into another hands nothing on.
                if (isTrackedBindingInitializer(self, tree, parent_map, root_var, aliases, node)) continue;
                if (bound == root_var) {
                    if (!isReadThroughField(tree, parent_map, node)) return true;
                    // Reading a field off the context leaves it alone. The
                    // address of that field is not a read of it: it is the
                    // field to write through, and the frame on the other end
                    // of that hand-off decides whether the allocator the
                    // allocation runs through is still the one the caller put
                    // there. A callee this file can read and that leaves the
                    // field alone settles the hand-off; one that writes to it,
                    // or one this file cannot read, settles nothing.
                    //
                    // An address handed to no call is a binding of this frame's
                    // own, and this frame settles it: the writes that land
                    // through it are what `parameterIsWrittenTo` reads, and a
                    // frame that only reads what it points at leaves the
                    // caller's field exactly where it was.
                    const address = fieldAddressNode(tree, parent_map, node) orelse continue;
                    if (may_descend) {
                        if (enclosingCallArgument(tree, parent_map, address)) |argument| {
                            if (calleeMutatesArgument(self, tree, parent_map, argument.call_node, argument.param_index, false)) return true;
                        }
                        continue;
                    }
                    return true;
                }
                if (aliasIsReadInPlace(tree, parent_map, node)) {
                    if (!may_descend) continue;
                    // The address of a field read off an alias is not a read of
                    // it either: `install(&slot.pool, gpa)` writes through it,
                    // and the frame on the other end of that hand-off is what
                    // decides what the allocation is charged to afterwards. An
                    // address handed to no call is a binding of this frame's
                    // own, which `parameterIsWrittenTo` settles.
                    const address = fieldAddressNode(tree, parent_map, node) orelse continue;
                    if (enclosingCallArgument(tree, parent_map, address)) |argument| {
                        if (calleeMutatesArgument(self, tree, parent_map, argument.call_node, argument.param_index, false)) return true;
                    }
                    continue;
                }
                // A hand-off to a function this file can read is settled by
                // that function's own frame, exactly as an earlier hand-off of
                // the context itself is. A callee that writes to it, or one
                // this file cannot read, settles nothing and rejects here.
                if (may_descend) {
                    if (enclosingCallArgument(tree, parent_map, node)) |argument| {
                        if (!calleeMutatesArgument(self, tree, parent_map, argument.call_node, argument.param_index, false)) continue;
                    }
                }
                return true;
            }
            return false;
        }

        /// True when the frame writes to the context or to anything reached
        /// through it. `ctx.arena = other;` swaps in the allocator the
        /// allocation then runs through, and the `deinit` the caller proved
        /// releases something else entirely. A write through a binding of the
        /// frame that holds the address of the context, or of the field, lands
        /// in the same place; a binding of a binding is reached the same way.
        ///
        /// A field beside the path the allocator arrives through is a value of
        /// its own and leaves the proof alone, and so does a hand-off with no
        /// path in hand: there every field of the context counts.
        fn parameterIsWrittenTo(
            self: *_Engine,
            tree: *const std.zig.Ast,
            current_cfg: *const Cfg,
            parent_map: []const u32,
            fn_index: u32,
            root_var: ids.VarId,
            aliases: []const ids.VarId,
            fields: ?[]const []const u8,
        ) bool {
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            for (tags, 0..) |tag, index| {
                const node: u32 = @intCast(index);
                if (!isAssignTag(tag)) continue;
                if (!ast_walk.isAncestor(fn_index, node, parent_map)) continue;
                const lhs: u32 = @intFromEnum(datas[node].node_and_node[0]);
                var chain = FieldChain{};
                const base = fieldChainOf(tree, lhs, &chain) orelse continue;
                const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, base, current_cfg) orelse continue;
                if (!reachesContext(bound, root_var, aliases)) continue;
                if (chain.len == 0) return true;
                const path = fields orelse return true;
                if (chainReachesPath(&chain, path)) return true;
            }
            return false;
        }

        /// True when `node` is the whole initializer of a declaration the alias
        /// set already holds: `const again = slot;` is that same address under
        /// another name, not a hand-off of it. Anything built around the
        /// initializer - a call that takes it, an address taken of it - hands
        /// the pointer on and answers nothing here, and a declaration that
        /// cannot be resolved settles nothing either. A cast that hands the
        /// same pointer back builds nothing around it, so a copy spelled that
        /// way is the same copy under another name.
        fn isTrackedBindingInitializer(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            target: ids.VarId,
            aliases: []const ids.VarId,
            node: u32,
        ) bool {
            const tags = tree.nodes.items(.tag);
            var current = node;
            var steps: u32 = 0;
            while (steps < 8) : (steps += 1) {
                if (current >= parent_map.len) return false;
                const parent = parent_map[current];
                if (parent == 0 or parent >= tags.len) return false;
                switch (tags[parent]) {
                    .grouped_expression, .unwrap_optional, .address_of => current = parent,
                    .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                        if (pointerCastOperand(tree, parent) != current) return false;
                        current = parent;
                    },
                    .simple_var_decl, .local_var_decl, .global_var_decl, .aligned_var_decl => {
                        const full = tree.fullVarDecl(@enumFromInt(parent)) orelse return false;
                        const init = full.ast.init_node.unwrap() orelse return false;
                        if (@intFromEnum(init) != current) return false;
                        const declared = _Engine.VarResolution.resolveVarIdFromVarDecl(self, parent) orelse return false;
                        return reachesContext(declared, target, aliases);
                    },
                    else => return false,
                }
            }
            return false;
        }

        /// Parameter the allocator expression reaches the caller's context
        /// through, and the binding that parameter is declared as.
        ///
        /// The expression may be spelled through a copy of that pointer this
        /// frame declared of its own, which is that same pointer under another
        /// name, so the walk follows the copy back to the parameter it was
        /// copied from. A parameter is bound to the name its declaration
        /// writes, and the use in the body is a different token that only the
        /// frame's own scopes tie back to it.
        fn parameterOfRoot(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            current_cfg: *const Cfg,
            fn_index: u32,
            root_node: u32,
        ) ?ParameterRoot {
            var params: [max_params]std.zig.Ast.TokenIndex = undefined;
            const param_count = prototypeParamNames(tree, fn_index, &params) orelse {
                return null;
            };
            var current = root_node;
            var steps: usize = 0;
            while (steps <= max_context_aliases) : (steps += 1) {
                const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, current, current_cfg) orelse {
                    return null;
                };
                for (params[0..param_count], 0..) |name_token, index| {
                    if (ids.varId(name_token) != bound) continue;
                    return .{ .index = index, .var_id = ids.varId(name_token) };
                }
                current = snapshotSource(self, tree, parent_map, fn_index, current_cfg, current, root_node) orelse {
                    return null;
                };
            }
            return null;
        }

        /// Binding a copy of the allocator's base took its pointer from, or
        /// null when that binding is not such a copy. The initializer has to
        /// be that name as the whole expression: a grouping and a cast that
        /// hands the same address back leave the pointer alone, while a field
        /// read or a call standing in front of the name builds a value of its
        /// own and settles nothing. Nothing may have written the copy over
        /// between its declaration and the read that runs through it, or the
        /// copy is a different pointer by then.
        fn snapshotSource(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            fn_index: u32,
            current_cfg: *const Cfg,
            ident: u32,
            use_node: u32,
        ) ?u32 {
            const init = bindingInitializer(self, tree, current_cfg, ident) orelse return null;
            // The initializer has to be that one name and nothing else.
            // `wholeExpressionBase` walks off the groupings and the casts that
            // hand the same address back and answers the name under them, while
            // a field read, a call or an address taken of the name builds a
            // value of its own and answers nothing. The name it answers is not
            // compared with `ident` as a node - the initializer is written in
            // the declaration while `ident` is a use site of it - so what the
            // copy was taken from is left to the resolver, which reads both
            // through the frame's own scopes on the next turn of the walk.
            const base = wholeExpressionBase(tree, init) orelse return null;
            if (!bindingUnwrittenUntilUse(self, tree, parent_map, fn_index, current_cfg, ident, use_node)) return null;
            return base;
        }

        /// Value a call argument denotes: the expression itself, or what the
        /// local it names was declared with. The walk keeps going through the
        /// address standing in front of a binding and through bindings of
        /// bindings: a context handed over as `&context` is the context itself
        /// as far as the call is concerned, which is how a parameter that takes
        /// a pointer receives it.
        fn argumentValue(
            self: *_Engine,
            tree: *const std.zig.Ast,
            caller_cfg: *const Cfg,
            arg: u32,
            depth: u8,
        ) ?u32 {
            if (depth >= 8) return null;
            const tags = tree.nodes.items(.tag);
            var current = arg;
            var steps: u8 = 0;
            while (steps < 8) : (steps += 1) {
                if (current >= tags.len) return null;
                switch (tags[current]) {
                    .address_of, .grouped_expression, .unwrap_optional => {
                        current = nodeChild(tree, current) orelse return null;
                    },
                    .identifier => {
                        current = bindingInitializer(self, tree, caller_cfg, current) orelse return null;
                    },
                    else => return current,
                }
            }
            return null;
        }

        /// Initializer of the local an identifier names, and null when the
        /// identifier names a binding this frame cannot read a value out of.
        /// The declaration is found through the frame's own scopes, so the
        /// binding a use site refers to is the declaration it was written in.
        fn bindingInitializer(
            self: *_Engine,
            tree: *const std.zig.Ast,
            caller_cfg: *const Cfg,
            ident: u32,
        ) ?u32 {
            const decl_info = _Engine.VarResolution.resolveDeclInfoFromIdentifier(self, ident, caller_cfg) orelse return null;
            const tags = tree.nodes.items(.tag);
            if (decl_info.decl_node >= tags.len or !isVarDeclTag(tags[decl_info.decl_node])) return null;
            const full = tree.fullVarDecl(@enumFromInt(decl_info.decl_node)) orelse return null;
            return @intFromEnum(full.ast.init_node.unwrap() orelse return null);
        }

        /// Follow the field chain from a struct value to the field the callee
        /// reads its allocator from.
        ///
        /// The chain compares field *names*. The callee spells the field in its
        /// own frame and the caller spells it in another, so the two are
        /// different tokens that stand for one name. A struct initialiser keeps
        /// only the value of each of its fields: `.name = value` puts the name
        /// two tokens ahead of the value's first token.
        ///
        /// A context can carry the one holding the allocator by value, so the
        /// field is often reached through a binding of its own instead of
        /// written out: `.{ .inner = inner }` carries whatever `inner` holds
        /// where the copy is made. The walk follows such a binding by its own
        /// declaration identity, never by the name it is spelled with, and
        /// refuses a binding this frame has written over before that copy: a
        /// rewrite behind the copy does not reach it, and only a rewrite ahead
        /// of it says what the copy was taken of.
        fn selectFieldPath(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            caller_cfg: *const Cfg,
            value: u32,
            fields: []const []const u8,
            index: usize,
            depth: u8,
        ) ?u32 {
            if (index >= fields.len) return value;
            if (depth >= 8) return null;
            const tags = tree.nodes.items(.tag);
            // Wrappers and plain bindings in front of the field are walked off
            // before any name is consumed: none of them names a field.
            var current = value;
            var steps: u8 = 0;
            while (steps < 8) : (steps += 1) {
                if (current >= tags.len) return null;
                switch (tags[current]) {
                    .identifier => {
                        if (!bindingUnwrittenUntilUse(self, tree, parent_map, caller_fn, caller_cfg, current, value)) return null;
                        current = bindingInitializer(self, tree, caller_cfg, current) orelse return null;
                    },
                    .address_of, .deref, .@"try", .@"catch", .grouped_expression, .unwrap_optional => {
                        current = nodeChild(tree, current) orelse return null;
                    },
                    else => break,
                }
            }
            if (current >= tags.len) return null;
            switch (tags[current]) {
                .field_access => {
                    const access = tree.nodes.items(.data)[current].node_and_token;
                    if (!fieldNameIs(tree, access[1], fields[index])) return null;
                    return selectFieldPath(self, tree, parent_map, caller_fn, caller_cfg, @intFromEnum(access[0]), fields, index + 1, depth + 1);
                },
                .struct_init,
                .struct_init_comma,
                .struct_init_one,
                .struct_init_one_comma,
                .struct_init_dot,
                .struct_init_dot_comma,
                .struct_init_dot_two,
                .struct_init_dot_two_comma,
                => {},
                else => return null,
            }

            var buffer: [2]std.zig.Ast.Node.Index = undefined;
            const struct_init = tree.fullStructInit(&buffer, @enumFromInt(current)) orelse return null;
            for (struct_init.ast.fields) |field| {
                const field_value: u32 = @intFromEnum(field);
                if (field_value >= tags.len) continue;
                // The entry is the value the field holds; the `.name =` that
                // names it is written in the tokens ahead of that value, so
                // the tree names the field nowhere else.
                const name_token = structInitFieldNameToken(tree, field) orelse continue;
                if (!fieldNameIs(tree, name_token, fields[index])) continue;
                return selectFieldPath(self, tree, parent_map, caller_fn, caller_cfg, field_value, fields, index + 1, depth + 1);
            }
            return null;
        }

        /// Binding a pointer argument points into: the value the argument was
        /// copied out of, followed through every copy of it the caller made.
        /// Null when the argument is not handed over as a pointer at all, or
        /// when the copy was taken out of a value rather than out of another
        /// pointer.
        fn pointerArgumentSource(
            self: *_Engine,
            tree: *const std.zig.Ast,
            caller_cfg: *const Cfg,
            arg: u32,
        ) ?u32 {
            const tags = tree.nodes.items(.tag);
            var current = arg;
            var steps: u8 = 0;
            while (steps < 8) : (steps += 1) {
                if (current >= tags.len) return null;
                switch (tags[current]) {
                    .address_of, .grouped_expression, .unwrap_optional => {
                        current = nodeChild(tree, current) orelse return null;
                    },
                    .identifier => {
                        const init = bindingInitializer(self, tree, caller_cfg, current) orelse return null;
                        if (init >= tags.len or !isPointerHopTag(tags[init])) return current;
                        current = init;
                    },
                    else => return null,
                }
            }
            return null;
        }

        /// True when nothing writes the binding `ident` names between its
        /// declaration and `use_node`, which is where the value in hand was
        /// copied out of it. A copy already taken is a value of its own: a
        /// write behind it does not reach it, and a write this file cannot
        /// place against the binding is not read as one here.
        fn bindingUnwrittenUntilUse(
            self: *_Engine,
            tree: *const std.zig.Ast,
            parent_map: []const u32,
            caller_fn: u32,
            caller_cfg: *const Cfg,
            ident: u32,
            use_node: u32,
        ) bool {
            const bound = _Engine.VarResolution.resolveVarIdFromIdentifier(self, ident, caller_cfg) orelse return false;
            const tags = tree.nodes.items(.tag);
            const datas = tree.nodes.items(.data);
            const use_path = statementPath(tree, parent_map, caller_fn, use_node) orelse return false;
            for (tags, 0..) |tag, index| {
                if (!isAssignTag(tag)) continue;
                const node: u32 = @intCast(index);
                if (!ast_walk.isAncestor(caller_fn, node, parent_map)) continue;
                const lhs: u32 = @intFromEnum(datas[node].node_and_node[0]);
                var chain = FieldChain{};
                const base = fieldChainOf(tree, lhs, &chain) orelse continue;
                const written = _Engine.VarResolution.resolveVarIdFromIdentifier(self, base, caller_cfg) orelse return false;
                if (written != bound) continue;
                const path = statementPath(tree, parent_map, caller_fn, node) orelse return false;
                if (nodeRunsBefore(&path, node, &use_path, use_node)) return false;
            }
            return true;
        }

        /// Strip `&`, derefs, groupings and field accesses off `expr`, leaving
        /// the base identifier and the names of the fields walked over.
        fn stripProjections(tree: *const std.zig.Ast, expr: u32) ?RootPath {
            const tags = tree.nodes.items(.tag);
            const token_tags = tree.tokens.items(.tag);
            var result = RootPath{ .root = 0 };
            var current = expr;
            var depth: u8 = 0;
            while (depth < 32) : (depth += 1) {
                if (current >= tags.len) return null;
                switch (tags[current]) {
                    .identifier => {
                        result.root = current;
                        // The walk came in from the outermost field, so the
                        // names went in back to front. Every consumer of this
                        // path compares it from the base outwards - the name
                        // on the outermost field comes first - so it is put
                        // back in that order here.
                        reverseFieldPath(&result);
                        return result;
                    },
                    .field_access => {
                        if (result.depth >= max_field_depth) return null;
                        const access = tree.nodes.items(.data)[current].node_and_token;
                        if (access[1] >= token_tags.len or token_tags[access[1]] != .identifier) return null;
                        result.fields[result.depth] = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                        result.depth += 1;
                        current = @intFromEnum(access[0]);
                    },
                    .deref, .address_of, .grouped_expression, .unwrap_optional => {
                        current = nodeChild(tree, current) orelse return null;
                    },
                    else => return null,
                }
            }
            return null;
        }

        fn fieldNameIs(tree: *const std.zig.Ast, token: std.zig.Ast.TokenIndex, name: []const u8) bool {
            if (token >= tree.tokens.items(.tag).len) return false;
            if (tree.tokenTag(token) != .identifier) return false;
            return std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(token)), name);
        }
    };
}

/// Put a field path read from the outside in back into the order the field
/// chain spells it, which is the order everything that compares one expects.
fn reverseFieldPath(path: *RootPath) void {
    var low: usize = 0;
    var high = path.depth;
    while (low < high) {
        high -= 1;
        const held = path.fields[low];
        path.fields[low] = path.fields[high];
        path.fields[high] = held;
        low += 1;
    }
}

/// True when nothing inside `fn_node` writes the identifier `token` again.
/// A binding that is assigned over may hold a different value where an
/// allocation happens, so whatever it was declared with proves nothing.
fn bindingIsStable(
    tree: *const std.zig.Ast,
    parent_map: []const u32,
    fn_node: u32,
    token: std.zig.Ast.TokenIndex,
) bool {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    for (tags, 0..) |tag, index| {
        const node: u32 = @intCast(index);
        if (!isAssignTag(tag)) continue;
        if (!ast_walk.isAncestor(fn_node, node, parent_map)) continue;
        const lhs: u32 = @intFromEnum(datas[node].node_and_node[0]);
        if (lhs >= tags.len or tags[lhs] != .identifier) continue;
        if (main_tokens[lhs] != token) continue;
        return false;
    }
    return true;
}

/// Every tag that writes its left side. A compound assignment reads the value
/// it overwrites, so it rebinds just as plainly as a plain one does.
fn isAssignTag(tag: std.zig.Ast.Node.Tag) bool {
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

/// Every tag a declaration is written with.
fn isVarDeclTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .simple_var_decl,
        .aligned_var_decl,
        .local_var_decl,
        .global_var_decl,
        => true,
        else => false,
    };
}

fn isBlockTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => true,
        else => false,
    };
}

/// Fields read off a binding and the binding they are read off. The expression
/// is written outside in and the walk goes inwards, so the names come off it
/// last first and are put back the way they are reached. Pointers and groupings
/// in front of the name are walked off as well: a write through one of them
/// lands in the same place.
fn fieldChainOf(tree: *const std.zig.Ast, expr: u32, chain: *FieldChain) ?u32 {
    const tags = tree.nodes.items(.tag);
    var current = expr;
    var steps: u32 = 0;
    while (steps < 32 and current < tags.len) : (steps += 1) {
        switch (tags[current]) {
            .identifier => {
                var low: usize = 0;
                var high: usize = chain.len;
                while (low < high) {
                    high -= 1;
                    const held = chain.names[low];
                    chain.names[low] = chain.names[high];
                    chain.names[high] = held;
                    low += 1;
                }
                return current;
            },
            .field_access => {
                const access = tree.nodes.items(.data)[current].node_and_token;
                if (access[1] >= tree.tokens.items(.tag).len) return null;
                if (tree.tokenTag(access[1]) != .identifier) return null;
                if (chain.len >= max_field_depth) return null;
                chain.names[chain.len] = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                chain.len += 1;
                current = @intFromEnum(access[0]);
            },
            .deref, .address_of, .@"try" => {
                current = @intFromEnum(tree.nodes.items(.data)[current].node);
            },
            // Each tag carries its operand under the member its own parser
            // writes: `catch` pairs two nodes, while a grouping and an
            // unwrap pair the value with the token beside it. The two members
            // hold the same two words, so the wrong one reads the right value
            // - but a checked build refuses to read a member that is not the
            // one active, which is what this split keeps it from.
            .grouped_expression, .unwrap_optional => {
                current = @intFromEnum(tree.nodes.items(.data)[current].node_and_token[0]);
            },
            .@"catch" => {
                current = @intFromEnum(tree.nodes.items(.data)[current].node_and_node[0]);
            },
            else => return null,
        }
    }
    return null;
}

/// True when the fields read off a binding name the way to the allocator or a
/// container on the way to it. A field beside that path is a value of its own
/// and says nothing about what the allocator is handed.
fn chainReachesPath(chain: *const FieldChain, fields: []const []const u8) bool {
    if (chain.len > fields.len) return false;
    for (chain.names[0..chain.len], fields[0..chain.len]) |read, expected| {
        if (!std.mem.eql(u8, read, expected)) return false;
    }
    return true;
}

/// True when the parameter at `index` is declared with a pointer type. The
/// declaration is the only place the question is asked from: a use site writes
/// the parameter as it writes any other name.
fn parameterIsPointer(tree: *const std.zig.Ast, fn_node: u32, index: usize) bool {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = fnProtoOf(tree, fn_node, &buffer) orelse return false;
    const tags = tree.nodes.items(.tag);
    var position: usize = 0;
    var it = proto.iterate(tree);
    while (it.next()) |param| : (position += 1) {
        if (position != index) continue;
        const type_expr = @intFromEnum(param.type_expr orelse return false);
        if (type_expr >= tags.len) return false;
        return switch (tags[type_expr]) {
            .ptr_type, .ptr_type_aligned, .ptr_type_sentinel => true,
            else => false,
        };
    }
    return false;
}

/// Tags that carry a pointer forward rather than build a value out of it: the
/// wrappers that leave one alone, and the name of another pointer.
fn isPointerHopTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .address_of, .grouped_expression, .unwrap_optional, .identifier => true,
        else => false,
    };
}

/// True when a binding is the context itself or one that holds a pointer to it.
fn reachesContext(bound: ids.VarId, target: ids.VarId, aliases: []const ids.VarId) bool {
    if (bound == target) return true;
    for (aliases) |alias| {
        if (bound == alias) return true;
    }
    return false;
}

/// Statements walked to reach a node, outermost block first. A node this frame
/// cannot place is not placed at all, and the caller reads that as unsettled.
fn statementPath(
    tree: *const std.zig.Ast,
    parent_map: []const u32,
    body: u32,
    node: u32,
) ?StatementPath {
    const tags = tree.nodes.items(.tag);
    var path = StatementPath{};
    var current = node;
    var steps: u32 = 0;
    while (steps < 128) : (steps += 1) {
        if (current == body) {
            reverseStatementPath(&path);
            return path;
        }
        if (current >= parent_map.len) return null;
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return null;
        if (parent == body) {
            reverseStatementPath(&path);
            return path;
        }
        if (tags[parent] == .fn_decl or tags[parent] == .test_decl) return null;
        if (isBlockTag(tags[parent])) {
            if (path.len >= max_block_nesting) return null;
            var buffer: [2]u32 = undefined;
            const statements = ast_walk.getBlockStatements(tree, parent, &buffer) orelse return null;
            var level: ?usize = null;
            for (statements, 0..) |statement, index| {
                if (statement == current) level = index;
            }
            path.levels[path.len] = level orelse return null;
            path.len += 1;
        }
        current = parent;
    }
    return null;
}

fn reverseStatementPath(path: *StatementPath) void {
    var low: usize = 0;
    var high: usize = path.len;
    while (low < high) {
        high -= 1;
        const held = path.levels[low];
        path.levels[low] = path.levels[high];
        path.levels[high] = held;
        low += 1;
    }
}

/// True when the frame reaches one node before it reaches the other: the paths
/// part company in a block they share, or the shorter one leaves a block the
/// longer one is still written inside. Two nodes of one statement are ordered
/// by where they sit in it.
fn nodeRunsBefore(
    candidate: *const StatementPath,
    candidate_node: u32,
    other: *const StatementPath,
    other_node: u32,
) bool {
    const shared = @min(candidate.len, other.len);
    for (candidate.levels[0..shared], other.levels[0..shared]) |left, right| {
        if (left != right) return left < right;
    }
    if (candidate.len != other.len) return candidate.len < other.len;
    return candidate_node < other_node;
}

/// Declaration a prototype node belongs to.
fn declarationOfProto(tree: *const std.zig.Ast, proto_node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    for (tags, 0..) |tag, index| {
        if (tag != .fn_decl) continue;
        const node: u32 = @intCast(index);
        if (@intFromEnum(datas[node].node_and_node[0]) == proto_node) return node;
    }
    return null;
}

/// Index of `tree` when it is this source's own AST, null otherwise.
/// Ownership stays with the source, so the answer only borrows: a foreign
/// tree, a source that cannot parse, and a syntax index that cannot be built
/// all answer conservatively instead of failing a query.
fn lexicalIndexFor(source: *Source, tree: *const std.zig.Ast) ?*const LexicalIndex {
    const source_tree = source.ast() catch return null;
    if (tree != source_tree) return null;
    return source.lexicalIndex() catch null;
}

/// Nearest enclosing callable of `node`: a function or a test declaration.
/// Both hold statements that can call out, and a test's frame disposes an arena
/// exactly like a function's does.
fn enclosingBody(
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

/// Block a statement belongs to, or null when it is not inside one.
fn enclosingBlock(tree: *const std.zig.Ast, parent_map: []const u32, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    var current = node;
    var steps: u32 = 0;
    while (steps < 32 and current < parent_map.len) : (steps += 1) {
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return null;
        switch (tags[parent]) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => return parent,
            else => current = parent,
        }
    }
    return null;
}

/// Block a frame's own body is written as. A call read out of a block inside
/// that body belongs to the inner block, but the way out of the frame is the
/// end of its own body: running off the end of an inner block carries on in
/// the block around it. A frame this file cannot read the body of proves
/// nothing about how it leaves.
fn frameOwnBodyBlock(tree: *const std.zig.Ast, frame: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (frame >= tags.len) return null;
    const datas = tree.nodes.items(.data);
    const body: u32 = switch (tags[frame]) {
        .fn_decl => @intFromEnum(datas[frame].node_and_node[1]),
        // A test's body sits beside its optional name, so the member of the
        // union it is read through is not the one a function uses.
        .test_decl => @intFromEnum(datas[frame].opt_token_and_node[1]),
        else => return null,
    };
    if (body == 0 or body >= tags.len or !isBlockTag(tags[body])) return null;
    return body;
}

/// True when a frame can run off the end of its own body, which is a way out of
/// it like any other and leaves it holding whatever it was holding. The exit
/// exists when control can reach the end of the body, so a body whose last
/// statement never finishes has no way out that way, and a body this file
/// cannot read is read as one control does reach the end of.
fn frameFallsOff(tree: *const std.zig.Ast, frame: u32) bool {
    const body = frameOwnBodyBlock(tree, frame) orelse return true;
    var buffer: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, body, &buffer) orelse return true;
    if (statements.len == 0) return true;
    return canCompleteThrough(tree, statements[statements.len - 1], 0);
}

/// Whether a statement can reach the next statement in its frame.
/// A return or unreachable statement cannot complete. An unlabeled block
/// depends on its final statement. An if cannot complete when neither arm can.
/// Labeled blocks remain conservative: an earlier break can skip a terminal
/// final statement and still complete the block.
/// Unreadable, depth-exceeded, loop, switch, defer, and break shapes can complete.
fn canCompleteThrough(tree: *const std.zig.Ast, node: u32, depth: usize) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return true;
    if (depth >= max_block_nesting) return true;
    return switch (tags[node]) {
        .@"return", .unreachable_literal => false,
        .grouped_expression => canCompleteThrough(
            tree,
            @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
            depth + 1,
        ),
        .block, .block_semicolon, .block_two, .block_two_semicolon => blk: {
            const brace = tree.nodes.items(.main_token)[node];
            if (brace >= 2 and tree.tokenTag(brace - 1) == .colon and
                tree.tokenTag(brace - 2) == .identifier) break :blk true;
            var buffer: [2]u32 = undefined;
            const statements = ast_walk.getBlockStatements(tree, node, &buffer) orelse break :blk true;
            if (statements.len == 0) break :blk true;
            break :blk canCompleteThrough(tree, statements[statements.len - 1], depth + 1);
        },
        .@"if", .if_simple => blk: {
            const full = tree.fullIf(@enumFromInt(node)) orelse break :blk true;
            const then_node: u32 = @intFromEnum(full.ast.then_expr);
            if (canCompleteThrough(tree, then_node, depth + 1)) break :blk true;
            const else_node: u32 = @intFromEnum(full.ast.else_expr.unwrap() orelse break :blk true);
            break :blk canCompleteThrough(tree, else_node, depth + 1);
        },
        else => true,
    };
}

/// The `defer` or `errdefer` whose body is `node`, or null when the disposal is
/// a bare statement that runs only where control reaches it. A grouping and a
/// block body are walked off and nothing else is: `defer { arena.deinit(); }`
/// registers the same disposal `defer arena.deinit();` does, and an `errdefer`
/// is read as its own node, never as the plain `defer` that also settles the
/// exits a success path takes.
fn parentOfDeferred(tree: *const std.zig.Ast, parent_map: []const u32, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    var current = node;
    var steps: u32 = 0;
    while (steps < 8 and current < parent_map.len) : (steps += 1) {
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return null;
        switch (tags[parent]) {
            .@"defer", .@"errdefer" => return parent,
            // A block body is the same registration spelled another way, so the
            // walk crosses it: `defer { arena.deinit(); }` is the defer that
            // `defer arena.deinit();` is.
            .grouped_expression, .block, .block_semicolon, .block_two, .block_two_semicolon => current = parent,
            else => return null,
        }
    }
    return null;
}

/// Frame body a scope belongs to, when every block between that scope and the
/// body's own block is a block of its own inside the block around it. A plain
/// block is one control reaches on its way through; a block written under a
/// conditional, a loop or a prong is entered some of the time, so what is
/// registered in it settles nothing.
fn unconditionallyReachedBody(
    tree: *const std.zig.Ast,
    parent_map: []const u32,
    frame: u32,
    scope: u32,
) ?u32 {
    const body = frameOwnBodyBlock(tree, frame) orelse return null;
    const tags = tree.nodes.items(.tag);
    var current = scope;
    var steps: usize = 0;
    while (steps < max_block_nesting) : (steps += 1) {
        if (current == body) return body;
        if (current >= parent_map.len) return null;
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return null;
        if (!isBlockTag(tags[parent])) return null;
        current = parent;
    }
    return null;
}

/// Label a block is written under - `inner: { ... }` - and null when the block
/// is written bare. The name in front of the brace is what a `break` written
/// in front of that block carries.
fn blockLabelToken(tree: *const std.zig.Ast, block: u32) ?std.zig.Ast.TokenIndex {
    const tags = tree.nodes.items(.tag);
    if (block >= tags.len or !isBlockTag(tags[block])) return null;
    const brace = tree.nodes.items(.main_token)[block];
    if (brace < 2 or brace >= tree.tokens.items(.tag).len) return null;
    if (tree.tokenTag(brace - 1) != .colon) return null;
    if (tree.tokenTag(brace - 2) != .identifier) return null;
    return brace - 2;
}

/// Label a `break` names, and null when it carries none. A break written
/// without a label leaves the loop or the switch it stands in, never a labeled
/// block, so it says nothing about leaving one.
fn breakLabelToken(tree: *const std.zig.Ast, node: u32) ?std.zig.Ast.TokenIndex {
    const label = tree.nodes.items(.data)[node].opt_token_and_opt_node[0].unwrap() orelse return null;
    if (label >= tree.tokens.items(.tag).len) return null;
    if (tree.tokenTag(label) != .identifier) return null;
    return label;
}

/// Looks for a `break` naming one of the labels a scope is written under,
/// anywhere inside one expression. The parent map is not read: the search runs
/// over the statements written ahead of a registration, and a break nested in
/// any of them is written ahead of it however deeply it sits.
///
/// The labels are compared as names, not as tokens: a block written
/// `inner: { ... }` and a `break :inner` written inside it spell the label with
/// two different tokens, and only the name tells them to be one label.
const ScopeLeavingBreak = struct {
    labels: []const []const u8,
    stop: bool = false,
    found: bool = false,

    pub fn visit(self: *@This(), tree: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) anyerror!void {
        if (tag != .@"break") return;
        const label = breakLabelToken(tree, node) orelse return;
        const name = import_resolver.normalizeIdentifier(tree.tokenSlice(label));
        for (self.labels) |candidate| {
            if (!std.mem.eql(u8, candidate, name)) continue;
            self.found = true;
            self.stop = true;
            return;
        }
    }
};

/// True when a `break` written inside `scope` leaves that scope before control
/// reaches `defer_node`, so a disposal registered there is never registered on
/// the path the break takes and never runs on it. Naming the label of the scope
/// or of a block the scope is written inside leaves it outright. Only the
/// blocks on the way up to the frame are named here, and the walk stops at the
/// first construct that is not a block, so nothing above the frame is read.
fn scopeLeftBefore(
    tree: *const std.zig.Ast,
    parent_map: []const u32,
    scope: u32,
    defer_node: u32,
) bool {
    const tags = tree.nodes.items(.tag);
    const defer_index = directStatementIndex(tree, scope, defer_node) orelse return false;
    var labels: [max_block_nesting][]const u8 = undefined;
    var label_count: usize = 0;
    var current: u32 = scope;
    var steps: usize = 0;
    while (steps < max_block_nesting) : (steps += 1) {
        if (current >= parent_map.len) break;
        if (blockLabelToken(tree, current)) |label| {
            if (label_count >= labels.len) break;
            labels[label_count] = import_resolver.normalizeIdentifier(tree.tokenSlice(label));
            label_count += 1;
        }
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len or !isBlockTag(tags[parent])) break;
        current = parent;
    }
    if (label_count == 0) return false;
    // The break is looked for in the statements the disposal is written behind
    // rather than placed against it: a break under a conditional is scheduled
    // by that conditional and not by the order of the statements, and walking
    // the statements ahead of the registration settles the question from where
    // the break is written. A break behind the disposal settles nothing: by
    // then the disposal is registered and the scope still has to end before it
    // runs.
    var buffer: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, scope, &buffer) orelse return false;
    for (statements[0..@min(defer_index, statements.len)]) |statement| {
        var finder = ScopeLeavingBreak{ .labels = labels[0..label_count] };
        ast_walk.walk(ScopeLeavingBreak, tree, statement, &finder) catch return true;
        if (finder.found) return true;
    }
    return false;
}

/// The `&` standing in front of the field read off `node`, or null when the
/// field is read where it stands. `&ctx.arena` is not a read of that field -
/// it is the field to write through - so a read and a hand-off spelled the same
/// way are told apart here. The field reads and the derefs in between are walked
/// off in order: `&ctx.inner.pool` is the address of that field, and
/// `&ctx.*.pool` is the address of that same field reached through a pointer to
/// the context.
fn fieldAddressNode(tree: *const std.zig.Ast, parent_map: []const u32, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    var current = node;
    var steps: u32 = 0;
    while (steps < 16) : (steps += 1) {
        if (current >= parent_map.len) return null;
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return null;
        switch (tags[parent]) {
            .grouped_expression, .unwrap_optional, .@"try", .deref => current = parent,
            .field_access => {
                const access = tree.nodes.items(.data)[parent].node_and_token;
                if (@intFromEnum(access[0]) != current) return null;
                current = parent;
            },
            .address_of => return parent,
            else => return null,
        }
    }
    return null;
}

/// True when `node` is the whole expression the walk started from, wrappers
/// apart. A bare copy of a binding that holds a pointer - `const alias =
/// context;` - hands that pointer on under another name, and a grouping or a
/// cast standing in front of the name changes nothing about that. The
/// same name read inside an expression of its own - `const label =
/// allocPrint(context.pool, ...);` - is a value that expression builds, not a
/// pointer into what the binding names. A field read or a call in front of the
/// name is such an expression, and answers nothing.
fn isWholeExpression(tree: *const std.zig.Ast, parent_map: []const u32, node: u32, expression: u32) bool {
    if (node == expression) return true;
    const tags = tree.nodes.items(.tag);
    var current = node;
    // The parent map is a tree and every node's parent is written after it, so
    // each step is a strictly larger index and the climb ends at the root on
    // its own. No step budget of its own is needed, and none of the shapes
    // below can turn it into a walk that never lands.
    while (current < parent_map.len) {
        if (current == expression) return true;
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return false;
        switch (tags[parent]) {
            .grouped_expression, .unwrap_optional, .@"try", .address_of => current = parent,
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                // Only a cast that takes a pointer and hands back that same
                // address leaves the value under it where it was.
                if (pointerCastOperand(tree, parent) != current) return false;
                current = parent;
            },
            else => return false,
        }
    }
    return false;
}

/// Operand of a cast that preserves the pointer it is given, and null for
/// every other builtin. `@ptrCast`, `@constCast`, `@alignCast`,
/// `@addrspaceCast` and `@volatileCast` each take a pointer and hand back that
/// same address. `@as` is written the other way round: it names the type the
/// value already has, and a conversion off a pointer cannot reach a number or
/// a slice, so the value under it is that same pointer too. Nothing else is
/// read this way - `@intFromPtr` builds an integer out of an address and
/// `@fieldParentPtr` builds a pointer into a field, and neither reaches what
/// the pointer it is handed came from.
fn pointerCastOperand(tree: *const std.zig.Ast, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return null;
    switch (tags[node]) {
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
        else => return null,
    }
    const token = tree.nodes.items(.main_token)[node];
    if (token >= tree.tokens.items(.tag).len) return null;
    const name = tree.tokenSlice(token);
    var buffer: [2]std.zig.Ast.Node.Index = undefined;
    const params = tree.builtinCallParams(&buffer, @enumFromInt(node)) orelse return null;
    // `@as` writes its result type ahead of the value, so the value is its
    // second argument. Only that position answers: the type it is written
    // against is a type of the program's and never reaches anything.
    if (std.mem.eql(u8, name, "@as")) {
        if (params.len != 2) return null;
        return @intFromEnum(params[1]);
    }
    const preserves_pointer = std.mem.eql(u8, name, "@ptrCast") or std.mem.eql(u8, name, "@constCast") or
        std.mem.eql(u8, name, "@alignCast") or std.mem.eql(u8, name, "@addrspaceCast") or
        std.mem.eql(u8, name, "@volatileCast");
    if (!preserves_pointer) return null;
    // A cast that spells out its result type carries the value as its last
    // argument; one that does not carries the value alone.
    if (params.len == 0 or params.len > 2) return null;
    return @intFromEnum(params[params.len - 1]);
}

/// Name an expression `isWholeExpression` accepted stands for: the wrappers
/// and the casts that hand a pointer back are walked off in the order the
/// climb walked them, and what is left is the binding the value was copied
/// from. An address taken of a name is not among them - that is a pointer to
/// the binding rather than the binding's own pointer - so it answers nothing
/// here.
fn wholeExpressionBase(tree: *const std.zig.Ast, expr: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    var current = expr;
    var steps: u8 = 0;
    while (steps < 8) : (steps += 1) {
        if (current >= tags.len) return null;
        switch (tags[current]) {
            .identifier => return current,
            .grouped_expression, .unwrap_optional, .@"try" => {
                current = nodeChild(tree, current) orelse return null;
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                current = pointerCastOperand(tree, current) orelse return null;
            },
            else => return null,
        }
    }
    return null;
}

/// Fields read off a binding above it: the walk goes outwards from the
/// identifier through the wrappers that leave a value alone, and every field
/// read that has it as its base adds its name. The parent walk visits fields
/// in base-to-member order, which is already the order consumers compare.
///
/// False when the path is longer than this file reads. The names gathered so
/// far name no path the callers compare against, so the caller is answered
/// from the context as a whole rather than from one field of it.
fn fieldChainAbove(tree: *const std.zig.Ast, parent_map: []const u32, node: u32, chain: *FieldChain) bool {
    const tags = tree.nodes.items(.tag);
    var current = node;
    var steps: u32 = 0;
    while (current < parent_map.len) {
        steps += 1;
        if (steps > max_field_depth + 1) {
            chain.len = 0;
            return false;
        }
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) break;
        switch (tags[parent]) {
            .grouped_expression, .unwrap_optional, .@"try" => current = parent,
            .field_access => {
                const access = tree.nodes.items(.data)[parent].node_and_token;
                if (@intFromEnum(access[0]) != current) break;
                if (access[1] >= tree.tokens.items(.tag).len) break;
                if (tree.tokenTag(access[1]) != .identifier) break;
                if (chain.len >= max_field_depth) {
                    chain.len = 0;
                    return false;
                }
                chain.names[chain.len] = import_resolver.normalizeIdentifier(tree.tokenSlice(access[1]));
                chain.len += 1;
                current = parent;
            },
            else => break,
        }
    }
    return true;
}

/// Index of the statement of `scope` that `node` is written inside, so a node
/// set in the middle of a nested block is placed by the statement of the
/// enclosing block that reaches it. Null when nothing in `scope` reaches `node`,
/// which leaves the caller to read that as unplaced rather than as somewhere.
fn reachedStatementIndex(
    tree: *const std.zig.Ast,
    parent_map: []const u32,
    scope: u32,
    node: u32,
) ?usize {
    var buffer: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, scope, &buffer) orelse return null;
    var current = node;
    var steps: u32 = 0;
    while (steps < 128 and current < parent_map.len) : (steps += 1) {
        const parent = parent_map[current];
        if (parent == 0) return null;
        if (parent == scope) {
            for (statements, 0..) |statement, index| {
                if (statement == current) return index;
            }
            return null;
        }
        current = parent;
    }
    return null;
}

/// Index of `node` among the statements of `scope`, and null unless it is a
/// statement of that block. A node written under a conditional is written in
/// the block but scheduled by the conditional, so where it sits among the
/// statements says nothing about when - or whether - it runs.
fn directStatementIndex(
    tree: *const std.zig.Ast,
    scope: u32,
    node: u32,
) ?usize {
    var buffer: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, scope, &buffer) orelse return null;
    for (statements, 0..) |statement, index| {
        if (statement == node) return index;
    }
    return null;
}

/// True when a `return` hands back an error value the source spells out:
/// `return error.NoOwner;`, and whatever groupings stand in front of it. An
/// identifier or a call that happens to produce one says nothing about the exit
/// it is written on, so a value this file cannot classify is settled the way
/// any other success exit is.
fn returnsErrorValue(tree: *const std.zig.Ast, expr: u32) bool {
    const tags = tree.nodes.items(.tag);
    var current = expr;
    var steps: u32 = 0;
    while (steps < 8 and current < tags.len) : (steps += 1) {
        switch (tags[current]) {
            .error_value => return true,
            // A grouping writes its sub-expression into `.node_and_token`; a
            // pair of nodes is a different member, and a checked build
            // refuses to read one that is not the member active.
            .grouped_expression => current = @intFromEnum(tree.nodes.items(.data)[current].node_and_token[0]),
            else => return false,
        }
    }
    return false;
}

/// True when `node` sits only where reading a field off it is possible: the
/// wrappers that leave a value alone, and then one field access that has it
/// as its base. Anything else - a call argument, a container field, a return -
/// hands the context itself somewhere else.
fn isReadThroughField(tree: *const std.zig.Ast, parent_map: []const u32, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    var current = node;
    var steps: u32 = 0;
    while (steps < 16) : (steps += 1) {
        if (current >= parent_map.len) return false;
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return false;
        switch (tags[parent]) {
            .grouped_expression, .unwrap_optional, .address_of, .deref, .@"try" => current = parent,
            .field_access => return @intFromEnum(tree.nodes.items(.data)[parent].node_and_token[0]) == current,
            else => return false,
        }
    }
    return false;
}

/// True when a binding that holds the address of the context is read where it
/// stands: dereferenced, or read as the base of a field. Handing it to a call,
/// storing it or returning it lets the frame write what it points at, and the
/// arena the caller disposes is then not what holds what is allocated next.
fn aliasIsReadInPlace(tree: *const std.zig.Ast, parent_map: []const u32, node: u32) bool {
    if (isReadThroughField(tree, parent_map, node)) return true;
    const tags = tree.nodes.items(.tag);
    var current = node;
    var steps: u32 = 0;
    while (steps < 16) : (steps += 1) {
        if (current >= parent_map.len) return false;
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return false;
        switch (tags[parent]) {
            .grouped_expression, .unwrap_optional, .@"try" => current = parent,
            // Reading through the pointer leaves the context alone; taking the
            // address of what it points at hands that address on.
            .deref => {
                if (parent >= parent_map.len) return false;
                const above = parent_map[parent];
                if (above == 0 or above >= tags.len) return false;
                return tags[above] != .address_of;
            },
            else => return false,
        }
    }
    return false;
}

/// Written argument of the nearest call around `node`, with the call that
/// takes it. Only the wrappers that leave a value alone are walked off: an
/// expression built around the pointer reaches that call whole, and the callee
/// is then settled on the argument it is actually written at.
fn enclosingCallArgument(tree: *const std.zig.Ast, parent_map: []const u32, node: u32) ?CallArgument {
    const tags = tree.nodes.items(.tag);
    var current = node;
    var steps: u32 = 0;
    while (steps < 16) : (steps += 1) {
        if (current >= parent_map.len) return null;
        const parent = parent_map[current];
        if (parent == 0 or parent >= tags.len) return null;
        switch (tags[parent]) {
            .grouped_expression, .unwrap_optional, .@"try" => current = parent,
            .call, .call_comma, .call_one, .call_one_comma => {
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const call = tree.fullCall(&buffer, @enumFromInt(parent)) orelse return null;
                for (call.ast.params, 0..) |param, index| {
                    if (@intFromEnum(param) == current) {
                        return .{ .call_node = parent, .param_index = index };
                    }
                }
                return null;
            },
            else => return null,
        }
    }
    return null;
}

/// Field name of a struct initialiser entry, read off the value it holds:
/// `.name = value` puts the name two tokens ahead of the value's first token.
fn structInitFieldNameToken(tree: *const std.zig.Ast, value_node: std.zig.Ast.Node.Index) ?std.zig.Ast.TokenIndex {
    const first = tree.firstToken(value_node);
    const token_tags = tree.tokens.items(.tag);
    if (first < 3 or first >= token_tags.len) return null;
    if (token_tags[first - 1] != .equal) return null;
    if (token_tags[first - 2] != .identifier) return null;
    if (token_tags[first - 3] != .period) return null;
    return first - 2;
}

/// Token written for a prototype parameter that carries no name. No
/// identifier resolves to it, so a hand-off settled on that parameter settles
/// nothing.
const no_param_name: std.zig.Ast.TokenIndex = std.math.maxInt(u32);

/// Parameter name tokens of a function declaration, one slot per prototype
/// parameter and in the order the canonical iterator yields them. A parameter
/// that carries no name still takes its position - `no_param_name` is written
/// in its slot - so a written argument `i` lands on prototype parameter
/// `i + implicit_self_count` whatever the prototype spells. Skipping a
/// nameless parameter would shift every name behind it onto the argument
/// before it.
fn prototypeParamNames(
    tree: *const std.zig.Ast,
    fn_node: u32,
    out: *[max_params]std.zig.Ast.TokenIndex,
) ?usize {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = fnProtoOf(tree, fn_node, &buffer) orelse return null;
    var count: usize = 0;
    var it = proto.iterate(tree);
    while (it.next()) |param| {
        if (count >= out.len) return count;
        out[count] = param.name_token orelse no_param_name;
        count += 1;
    }
    return count;
}

/// Prototype node of a function declaration, or null when `fn_node` is not
/// one. The node is what a call resolves to, so comparing prototypes is what
/// tells two same-named functions apart.
fn functionProtoNode(tree: *const std.zig.Ast, fn_node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (fn_node >= tags.len or tags[fn_node] != .fn_decl) return null;
    const proto_node = @intFromEnum(tree.nodes.items(.data)[fn_node].node_and_node[0]);
    if (proto_node >= tags.len) return null;
    return switch (tags[proto_node]) {
        .fn_proto, .fn_proto_simple, .fn_proto_one, .fn_proto_multi => proto_node,
        else => null,
    };
}

fn fnProtoOf(
    tree: *const std.zig.Ast,
    fn_node: u32,
    buffer: *[1]std.zig.Ast.Node.Index,
) ?std.zig.Ast.full.FnProto {
    return protoOf(tree, functionProtoNode(tree, fn_node) orelse return null, buffer);
}

/// Name token of a prototype, which is the binding a bare call spells.
fn prototypeNameToken(tree: *const std.zig.Ast, proto_node: u32) ?std.zig.Ast.TokenIndex {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = protoOf(tree, proto_node, &buffer) orelse return null;
    return proto.name_token;
}

fn protoOf(
    tree: *const std.zig.Ast,
    proto_node: u32,
    buffer: *[1]std.zig.Ast.Node.Index,
) ?std.zig.Ast.full.FnProto {
    const tags = tree.nodes.items(.tag);
    if (proto_node >= tags.len) return null;
    return switch (tags[proto_node]) {
        .fn_proto => tree.fnProto(@enumFromInt(proto_node)),
        .fn_proto_simple => tree.fnProtoSimple(buffer, @enumFromInt(proto_node)),
        .fn_proto_one => tree.fnProtoOne(buffer, @enumFromInt(proto_node)),
        .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)),
        else => null,
    };
}

/// The one child node an expression wraps: the value behind `&`, `*`, `try`,
/// `?`, `catch` and a grouping. A field read is not one of these, because the
/// field it names is a value of its own rather than the thing underneath.
///
/// Each tag is read through the member its own parser writes the operand into:
/// `.node` for the prefix operators, `.node_and_token` for a grouping and an
/// unwrap, `.node_and_node` for `catch`. The last two hold the operand first
/// and the same two words wide, so reading one for the other answers the same
/// number - but `Data` is a union, and a checked build refuses to read a member
/// that is not the one active.
fn nodeChild(tree: *const std.zig.Ast, expr: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (expr >= tags.len) return null;
    return switch (tags[expr]) {
        .deref, .address_of, .@"try" => @intFromEnum(tree.nodes.items(.data)[expr].node),
        .grouped_expression, .unwrap_optional => @intFromEnum(tree.nodes.items(.data)[expr].node_and_token[0]),
        .@"catch" => @intFromEnum(tree.nodes.items(.data)[expr].node_and_node[0]),
        else => null,
    };
}

/// How many nodes of `tree` carry `tag`, with the first of them written into
/// `first`. The wrapper tags the tests below walk are each written once, so a
/// count of one is the proof that the node kept is the only one of its kind and
/// that the assertions about it are about the expression they mean.
fn countNodesOfTag(tree: *const std.zig.Ast, tag: std.zig.Ast.Node.Tag, first: *u32) usize {
    var count: usize = 0;
    for (tree.nodes.items(.tag), 0..) |candidate, index| {
        if (candidate != tag) continue;
        if (count == 0) first.* = @intCast(index);
        count += 1;
    }
    return count;
}

test "arena_provenance - nodeChild reads every wrapper tag through its own union member" {
    // Each of the six tags is written exactly once, so a count of one says the
    // node under test is the only one of its kind, and the name its child carries
    // says the walk stopped on the expression that was wrapped rather than
    // anywhere else. `Node.Data` is a union, so a tag read through a member
    // other than the one its parser wrote aborts a checked build instead of
    // returning: this test is what keeps each of the six prongs on the member it
    // belongs to.
    const code: [:0]const u8 =
        \\fn sample(optional: ?u8, failing: anyerror!u8, pointer: *u8) void {
        \\    _ = (pointer);
        \\    _ = optional.?;
        \\    _ = try failing;
        \\    _ = pointer.*;
        \\    _ = &failing;
        \\    _ = failing catch 0;
        \\}
    ;
    var source = Source.init(std.testing.allocator, "node-child.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);

    const Case = struct { tag: std.zig.Ast.Node.Tag, name: []const u8 };
    const cases = [_]Case{
        .{ .tag = .grouped_expression, .name = "pointer" },
        .{ .tag = .unwrap_optional, .name = "optional" },
        .{ .tag = .@"try", .name = "failing" },
        .{ .tag = .deref, .name = "pointer" },
        .{ .tag = .address_of, .name = "failing" },
        .{ .tag = .@"catch", .name = "failing" },
    };
    for (cases) |case| {
        var wrapper: u32 = 0;
        try std.testing.expectEqual(@as(usize, 1), countNodesOfTag(tree, case.tag, &wrapper));

        const child = nodeChild(tree, wrapper) orelse return error.TestUnexpectedResult;
        try std.testing.expectEqual(std.zig.Ast.Node.Tag.identifier, tags[child]);
        try std.testing.expectEqualStrings(case.name, tree.tokenSlice(main_tokens[child]));
    }

    // The negative space: a tag that wraps nothing answers nothing, and an
    // index past the tree is refused rather than read.
    try std.testing.expectEqual(@as(?u32, null), nodeChild(tree, 0));
    try std.testing.expectEqual(@as(?u32, null), nodeChild(tree, @intCast(tags.len)));
}

test "arena_provenance - a field chain is walked through the member each wrapper carries" {
    // `fieldChainOf` walks the same three wrapper tags `nodeChild` does, and each
    // is read from the member its own parser wrote. A tag read through the other
    // member would answer the same number - the operand sits first either way -
    // so the names gathered are what tell the two apart, and a checked build
    // refuses the wrong member outright. Every source puts a field access under
    // its wrapper and starts the walk at the wrapper, so a member read off by
    // one slot lands on `other` instead of `pool` and is caught.
    const Walk = struct {
        code: [:0]const u8,
        tag: std.zig.Ast.Node.Tag,
        name: []const u8,
        fields: []const []const u8,
    };
    const walks = [_]Walk{
        .{
            .code = "fn sample(holder: Holder) void { _ = (holder.pool); }",
            .tag = .grouped_expression,
            .name = "holder",
            .fields = &.{"pool"},
        },
        .{
            .code = "fn sample(holder: Holder) void { _ = holder.pool.?; }",
            .tag = .unwrap_optional,
            .name = "holder",
            .fields = &.{"pool"},
        },
        .{
            .code = "fn sample(holder: Holder) void { _ = holder.pool catch holder.other; }",
            .tag = .@"catch",
            .name = "holder",
            .fields = &.{"pool"},
        },
    };
    for (walks) |walk| {
        var source = Source.init(std.testing.allocator, "wrapper-walk.zig", walk.code);
        defer source.deinit();
        const tree = try source.ast();
        const main_tokens = tree.nodes.items(.main_token);

        var wrapper: u32 = 0;
        try std.testing.expectEqual(@as(usize, 1), countNodesOfTag(tree, walk.tag, &wrapper));

        var chain = FieldChain{};
        const base = fieldChainOf(tree, wrapper, &chain) orelse return error.TestUnexpectedResult;
        try std.testing.expectEqualStrings(walk.name, tree.tokenSlice(main_tokens[base]));
        try std.testing.expectEqual(walk.fields.len, chain.len);
        for (walk.fields, 0..) |name, index| {
            try std.testing.expectEqualStrings(name, chain.names[index]);
        }
    }
}

test "arena_provenance - a grouping in front of an error value still reads as one" {
    // `returnsErrorValue` steps off a grouping before it reads the exit, so the
    // grouping is read through `.node_and_token` while `return` itself is read
    // through its own optional operand. A value that is not an error value
    // settles nothing either way round.
    const Case = struct { code: [:0]const u8, expected: bool };
    const cases = [_]Case{
        .{ .code = "fn sample() !void { return error.Failed; }", .expected = true },
        .{ .code = "fn sample() !void { return (error.Failed); }", .expected = true },
        .{ .code = "fn sample() !void { return (1); }", .expected = false },
    };
    for (cases) |case| {
        var source = Source.init(std.testing.allocator, "error-exit.zig", case.code);
        defer source.deinit();
        const tree = try source.ast();

        var ret_node: u32 = 0;
        try std.testing.expectEqual(@as(usize, 1), countNodesOfTag(tree, .@"return", &ret_node));
        const operand = tree.nodes.items(.data)[ret_node].opt_node.unwrap() orelse return error.TestUnexpectedResult;
        try std.testing.expectEqual(case.expected, returnsErrorValue(tree, @intFromEnum(operand)));
    }
}

test "arena_provenance - a labeled break is matched to its block by name, not by token" {
    // `scopeLeftBefore` answers whether a `break` written ahead of the
    // registration leaves the scope the disposal is written in. The label is
    // spelled twice - once in front of the brace, once after the `break` - so
    // the two are different tokens of one name, and only comparing the names
    // tells a break that leaves the scope from one that names nothing at all.
    // Each source below writes the `break` in the one position the question is
    // about, so the two answers are read off the placement and not off the
    // spelling.
    const Case = struct { code: [:0]const u8, expected: bool };
    const cases = [_]Case{
        // The break is written ahead of the registration: it leaves the block
        // before the disposal is registered, so the disposal settles nothing.
        .{
            .code = "fn sample(drop: bool) void { inner: { if (drop) break :inner; defer release(); } }",
            .expected = true,
        },
        // The break is written behind the registration: the disposal is already
        // registered on the path it takes, so it settles that path.
        .{
            .code = "fn sample(drop: bool) void { inner: { defer release(); if (drop) break :inner; } }",
            .expected = false,
        },
        // A break that names a label of its own leaves the block it is written
        // in, not the scope the disposal is registered in.
        .{
            .code = "fn sample(drop: bool) void { inner: { if (drop) break :other; defer release(); } }",
            .expected = false,
        },
        // A break written with no label leaves the loop it stands in, which
        // says nothing about leaving a labeled block.
        .{
            .code = "fn sample(flag: bool) void { inner: { while (flag) { break; } defer release(); } }",
            .expected = false,
        },
    };
    for (cases) |case| {
        var source = Source.init(std.testing.allocator, "labeled-break.zig", case.code);
        defer source.deinit();
        const tree = try source.ast();

        const parent_map = try std.testing.allocator.alloc(u32, tree.nodes.items(.tag).len);
        defer std.testing.allocator.free(parent_map);
        @memset(parent_map, 0);
        for (tree.rootDecls()) |root| {
            ast_walk.fillParentMap(tree, @intFromEnum(root), parent_map);
        }

        // The scope is the labeled block the registration is written in, which
        // is the only block in these sources carrying a label.
        var scope: u32 = 0;
        for (tree.nodes.items(.tag), 0..) |tag, index| {
            if (!isBlockTag(tag)) continue;
            if (blockLabelToken(tree, @intCast(index)) == null) continue;
            scope = @intCast(index);
        }
        var defer_node: u32 = 0;
        try std.testing.expectEqual(@as(usize, 1), countNodesOfTag(tree, .@"defer", &defer_node));

        try std.testing.expectEqual(case.expected, scopeLeftBefore(tree, parent_map, scope, defer_node));
    }
}
