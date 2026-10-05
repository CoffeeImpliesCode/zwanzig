const std = @import("std");
const import_resolver = @import("../analysis/import_resolver.zig");
const call_resolver = @import("../analysis/call_resolver.zig");
const Rule = @import("../rule.zig").Rule;
const Source = @import("../source.zig").Source;
const Diagnostic = @import("../diagnostic.zig").Diagnostic;
const RuleError = @import("../rule.zig").RuleError;
const zir_bridge_mod = @import("../zir_bridge.zig");

/// Rule that enforces Zig naming conventions:
/// - Type names (struct, enum, union, opaque, error set): PascalCase
/// - Function names: camelCase
/// - Variable/constant names: snake_case
/// - Parameter and payload names: snake_case
/// - SCREAMING_SNAKE_CASE is allowed only when aliasing external conventions
///
/// The convention is chosen from the resolved type-versus-value result of the
/// declaration, not from the capitalization of what it is bound to. A type
/// value is proved by the initializer expression itself: a type-producing
/// builtin, a generic type factory call, a `@typeInfo` field that carries a
/// type, a namespace member the resolver proves to be a type, a labeled block
/// whose every break carries one, or a conditional or switch whose every branch
/// carries one. A value member is proved the same way, and a member of a
/// namespace declared by another file is left alone because its result is
/// unknown rather than assumed.
///
/// Names starting with underscore (_) are ignored as they indicate
/// intentionally ignored/internal identifiers.
pub const IdentifierStyleRule = struct {
    pub const rule: Rule = .{
        .name = "identifier-style",
        .default_severity = .warning,
        .checkFn = check,
    };

    const Style = enum {
        pascal_case,
        camel_case,
        snake_case,
    };

    /// Result of type-aware classification for a declaration.
    /// When ZIR-based type information is available, we can definitively
    /// classify the declaration. Otherwise, we fall back to heuristics.
    const DeclClassification = enum {
        type_decl, // Struct, enum, union, or type alias - should be PascalCase
        function_type, // Function type (fn() void) - should be PascalCase
        function, // Function declaration - should be camelCase
        constant, // Constant value - should be snake_case
        variable, // Variable - should be snake_case
        unknown, // Could not determine - fall back to heuristics
    };

    /// Classify a declaration using ZIR-based type information.
    /// Returns .unknown if type info is not available, allowing fallback to heuristics.
    fn classifyDeclWithTypeInfo(src: *Source, name: []const u8, node_idx: u32) DeclClassification {
        const decl = findDeclByAstNode(src, node_idx) orelse return .unknown;
        if (!std.mem.eql(u8, decl.name, name)) return .unknown;

        // Check if it's a function
        if (decl.is_fn) return .function;

        // Check type kind from ZIR
        switch (decl.type_info.kind) {
            .@"struct" => {
                if (isNamespaceStructDecl(src, decl)) return .unknown;
                return .type_decl;
            },
            .@"enum", .@"union", .type_type => return .type_decl,
            .function => return .function_type,
            .unknown => return .unknown,
            else => {},
        }

        // It's a value declaration
        if (decl.is_const) return .constant;
        return .variable;
    }

    fn check(src: *Source, allocator: std.mem.Allocator, diagnostics: *std.ArrayList(Diagnostic)) RuleError!void {
        const tree = try src.ast();
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        const main_tokens = tree.nodes.items(.main_token);
        const token_tags = tree.tokens.items(.tag);
        const token_starts = tree.tokens.items(.start);

        for (tags, 0..) |tag, i| {
            switch (tag) {
                .fn_decl => {
                    const proto_node = @intFromEnum(datas[i].node_and_node[0]);
                    try checkFnProto(src, allocator, diagnostics, tree, proto_node, token_tags, token_starts);
                },
                // Note: standalone fn_proto nodes are function types (e.g., const Fn = fn() void)
                // not function declarations, so we don't check their naming here
                .simple_var_decl, .aligned_var_decl, .local_var_decl, .global_var_decl => {
                    try checkVarDecl(src, allocator, diagnostics, tree, @intCast(i), tags, datas, main_tokens, token_tags, token_starts);
                },
                .@"if", .if_simple => {
                    try checkIfPayloads(src, allocator, diagnostics, tree, @intCast(i), token_tags, token_starts);
                },
                .@"while", .while_simple, .while_cont => {
                    try checkWhilePayloads(src, allocator, diagnostics, tree, @intCast(i), token_tags, token_starts);
                },
                .@"for", .for_simple => {
                    try checkForPayloads(src, allocator, diagnostics, tree, @intCast(i), token_tags, token_starts);
                },
                .@"switch", .switch_comma => {
                    try checkSwitchPayloads(src, allocator, diagnostics, tree, @intCast(i), token_tags, token_starts);
                },
                .@"catch" => {
                    try checkCatchPayload(src, allocator, diagnostics, tree, @intCast(i), token_tags, token_starts);
                },
                .@"errdefer" => {
                    try checkErrdeferPayload(src, allocator, diagnostics, tree, @intCast(i), token_tags, token_starts);
                },
                else => {},
            }
        }
    }

    fn checkFnProto(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
    ) RuleError!void {
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const tags = tree.nodes.items(.tag);
        const tag = tags[node_idx];

        const proto = switch (tag) {
            .fn_proto => tree.fnProto(@enumFromInt(node_idx)),
            .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(node_idx)),
            .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(node_idx)),
            .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(node_idx)),
            else => return,
        };

        if (proto.name_token) |name_token| {
            if (token_tags[name_token] == .identifier) {
                const name = tree.tokenSlice(name_token);
                if (!shouldSkipName(name)) {
                    if (isBuiltinTypeExpr(tree, @intFromEnum(proto.ast.return_type))) {
                        if (!isPascalCase(name)) {
                            try emitDiagnostic(
                                src,
                                allocator,
                                diagnostics,
                                token_starts[name_token],
                                name,
                                "type factory",
                                .pascal_case,
                            );
                        }
                    } else if (!isCamelCase(name)) {
                        try emitDiagnostic(
                            src,
                            allocator,
                            diagnostics,
                            token_starts[name_token],
                            name,
                            "function",
                            .camel_case,
                        );
                    }
                }
            }
        }

        var it = proto.iterate(tree);
        while (it.next()) |param| {
            if (param.name_token) |tok| {
                try checkParamName(src, allocator, diagnostics, tree, token_tags, token_starts, tok, param);
            }
        }
    }

    fn checkVarDecl(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        node_idx: u32,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
    ) RuleError!void {
        const full = tree.fullVarDecl(@enumFromInt(node_idx)) orelse return;
        const name_token = full.ast.mut_token + 1;
        if (name_token >= token_tags.len) return;
        if (token_tags[name_token] != .identifier) return;

        const name = tree.tokenSlice(name_token);
        if (shouldSkipName(name)) return;

        const is_const = token_tags[full.ast.mut_token] == .keyword_const;
        const init_idx_opt = if (full.ast.init_node.unwrap()) |init_node|
            @intFromEnum(init_node)
        else
            null;

        // An explicit `: type` is definitive even when nested ZIR reports a constant value.
        const is_explicit_type_alias = if (full.ast.type_node.unwrap()) |type_node|
            isBuiltinTypeExpr(tree, @intFromEnum(type_node))
        else
            false;

        // A direct import is a namespace alias even when ZIR reports a constant value.
        if (is_const and !is_explicit_type_alias) {
            if (init_idx_opt) |init_idx| {
                if (init_idx < tags.len) {
                    if (isDirectImport(tree, tags, token_tags, init_idx)) {
                        if (!isLowerSnakeCase(name) and !isPascalCase(name)) {
                            try emitDiagnostic(
                                src,
                                allocator,
                                diagnostics,
                                token_starts[name_token],
                                name,
                                "namespace",
                                .snake_case,
                            );
                        }
                        return;
                    }
                }
            }
        }

        // Type-valued initializers are proved from the expression itself: ZIR
        // only sees the call/conditional node of a type expression and reports
        // its result as an unknown value, so this evidence must be collected
        // before the ZIR-based classification.
        const is_type_value_expr = blk: {
            if (!is_const) break :blk false;
            const init_idx = init_idx_opt orelse break :blk false;
            break :blk isTypeValueInitExpr(tree, tags, datas, main_tokens, token_tags, init_idx, type_value_hops);
        };

        const zir_classification = classifyDeclWithTypeInfo(src, name, node_idx);
        // A ZIR classification that knows the declaration is a plain value is
        // final. The expression proof is naming-based, so letting it promote a
        // known value to a type alias would demand PascalCase for a value.
        const zir_knows_value = zir_classification == .constant or zir_classification == .variable;
        const type_classification: DeclClassification = if (!zir_knows_value and (is_explicit_type_alias or is_type_value_expr))
            .type_decl
        else
            zir_classification;
        switch (type_classification) {
            .type_decl => {
                // Proved to be a type value - must be PascalCase
                if (!isPascalCase(name) and !isCTypeAliasName(name)) {
                    try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "type", .pascal_case);
                }
                return;
            },
            .function_type => {
                // ZIR confirms this is a function type alias - must be PascalCase
                if (!isPascalCase(name) and !isCTypeAliasName(name)) {
                    try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "function type", .pascal_case);
                }
                return;
            },
            .function => {
                // This shouldn't happen for var decls, but handle gracefully
                if (!isCamelCase(name)) {
                    try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "function", .camel_case);
                }
                return;
            },
            .constant => {
                // ZIR confirms this is a constant value (not a type)
                // Check for external convention aliasing
                const is_external_alias = isScreamingSnakeCase(name) and
                    (if (init_idx_opt) |init_idx|
                        isExternalConventionAlias(tree, tags, datas, token_tags, init_idx)
                    else
                        false);
                if (!isLowerSnakeCase(name) and !is_external_alias) {
                    // Allow function aliases to use camelCase
                    if (init_idx_opt) |init_idx| {
                        if (isFunctionAlias(tree, tags, datas, token_tags, init_idx) and isCamelCase(name)) {
                            return;
                        }
                    }
                    try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "constant", .snake_case);
                }
                return;
            },
            .variable => {
                // ZIR confirms this is a variable
                if (!isLowerSnakeCase(name)) {
                    try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "variable", .snake_case);
                }
                return;
            },
            .unknown => {
                // A member of a namespace declared by another file has no
                // resolved type-versus-value result here. Asserting either
                // convention from the member's spelling would report a rule the
                // resolution never proved, so the alias is left alone.
                if (is_const) {
                    if (init_idx_opt) |init_idx| {
                        if (isInvisibleNamespaceMember(tree, tags, datas, token_tags, init_idx)) return;
                    }
                }
                // ZIR info not available, fall back to heuristic analysis
            },
        }

        // Fallback: heuristic-based analysis when ZIR type info is not available
        // Check if this is a type definition (const Foo = struct { ... })
        if (is_const) {
            if (init_idx_opt) |init_idx| {
                if (init_idx < tags.len) {
                    const init_tag = tags[init_idx];
                    if (isTypeDefinitionTag(init_tag)) {
                        const is_struct = isStructContainer(init_idx, main_tokens, token_tags);
                        if (!is_struct or init_tag == .error_set_decl) {
                            if (!isPascalCase(name) and !isCTypeAliasName(name)) {
                                try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "type", .pascal_case);
                            }
                            return;
                        }

                        const has_fields = containerHasFields(tree, tags, init_idx);
                        if (has_fields) {
                            if (!isPascalCase(name) and !isCTypeAliasName(name)) {
                                try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "type", .pascal_case);
                            }
                            return;
                        }

                        if (!isLowerSnakeCase(name) and !isPascalCase(name)) {
                            try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "namespace", .snake_case);
                        }
                        return;
                    }

                    // Check for function type (const foo = fn() void)
                    if (isFunctionTypeTag(init_tag)) {
                        // Function type alias - check for PascalCase
                        if (!isPascalCase(name) and !isCTypeAliasName(name)) {
                            try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "function type", .pascal_case);
                        }
                        return;
                    }

                    // Check for type alias from import: const Foo = @import("...").Foo
                    // or type alias: const Foo = SomeType
                    if (isLikelyTypeAlias(tree, tags, datas, main_tokens, token_tags, init_idx, type_value_hops)) {
                        // This is likely a type alias - check for PascalCase
                        if (!isPascalCase(name) and !isCTypeAliasName(name)) {
                            try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "type alias", .pascal_case);
                        }
                        return;
                    }

                    if (isFunctionAlias(tree, tags, datas, token_tags, init_idx)) {
                        if (!isCamelCase(name) and !isLowerSnakeCase(name)) {
                            try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "constant", .snake_case);
                        }
                        return;
                    }
                }
            }
        }

        // For constants: require snake_case unless aliasing an external convention
        if (is_const) {
            const is_external_alias = isScreamingSnakeCase(name) and
                (if (init_idx_opt) |init_idx|
                    isExternalConventionAlias(tree, tags, datas, token_tags, init_idx)
                else
                    false);
            if (!isLowerSnakeCase(name) and !is_external_alias) {
                try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "constant", .snake_case);
            }
            return;
        }

        // For var declarations: require snake_case
        if (!isLowerSnakeCase(name)) {
            try emitDiagnostic(src, allocator, diagnostics, token_starts[name_token], name, "variable", .snake_case);
        }
    }

    /// How many binding hops one type-value proof may follow.
    ///
    /// The block, identifier and wrapper walks below are mutually recursive: an
    /// identifier resolves to the initializer of the declaration it names, and
    /// that initializer can be a labeled block whose breaks name declarations
    /// again. All of them spend one budget, so an alias cycle runs out of it
    /// and proves nothing instead of recursing until the stack is exhausted.
    /// Counting hops keeps the proof allocation-free.
    const type_value_hops: u8 = 32;

    /// Prove that an initializer expression evaluates to a type value.
    ///
    /// Only expression forms that cannot be mistaken for a value are accepted:
    /// a type-producing builtin, a generic type factory call, a reflection
    /// field that carries a type, a namespace member the resolver proves to be
    /// a type, a labeled block whose every break carries one, or a conditional
    /// or switch expression whose every branch is itself a type value.
    ///
    /// The budget is what the walks that call this one have left, so an alias
    /// cycle between them proves nothing rather than recursing without end.
    fn isTypeValueInitExpr(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
        budget: u8,
    ) bool {
        if (budget == 0) return false;
        if (init_idx >= tags.len) return false;
        if (isTypeValueDeclaration(tree, tags, main_tokens, token_tags, init_idx)) return true;
        return switch (tags[init_idx]) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => blk: {
                const builtin_name = builtinCallName(tree, tags, token_tags, init_idx) orelse break :blk false;
                break :blk isTypeFactoryBuiltin(builtin_name);
            },
            .call, .call_comma, .call_one, .call_one_comma => isTypeFactoryCall(
                tree,
                tags,
                datas,
                main_tokens,
                token_tags,
                init_idx,
                budget - 1,
            ),
            .identifier, .field_access => resolvedInitIsTypeValue(
                tree,
                tags,
                datas,
                main_tokens,
                token_tags,
                init_idx,
                budget - 1,
            ),
            .block, .block_semicolon, .block_two, .block_two_semicolon => isTypeValueLabeledBlock(
                tree,
                tags,
                datas,
                main_tokens,
                token_tags,
                init_idx,
                budget - 1,
            ),
            .@"switch", .switch_comma => isTypeSwitchAlias(
                tree,
                tags,
                datas,
                main_tokens,
                token_tags,
                init_idx,
                budget - 1,
            ),
            .@"if", .if_simple => isTypeIfAlias(
                tree,
                tags,
                datas,
                main_tokens,
                token_tags,
                init_idx,
                budget - 1,
            ),
            .unwrap_optional,
            .grouped_expression,
            => blk: {
                const data = datas[init_idx].node_and_token;
                break :blk isTypeValueInitExpr(tree, tags, datas, main_tokens, token_tags, @intFromEnum(data[0]), budget - 1);
            },
            else => false,
        };
    }

    /// A declaration that names a type: a type expression, an error set, or a
    /// container that is not a fieldless namespace struct. A fieldless struct
    /// is a namespace, which holds declarations rather than types, so it keeps
    /// the namespace naming rule instead of the type rule.
    fn isTypeValueDeclaration(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        if (node_idx >= tags.len) return false;
        if (isTypeExpressionTag(tags[node_idx])) return true;
        if (!isTypeDefinitionTag(tags[node_idx])) return false;
        if (isStructContainer(node_idx, main_tokens, token_tags)) {
            return containerHasFields(tree, tags, node_idx);
        }
        return true;
    }

    /// How many alias hops the invisible-namespace walk may take. That walk
    /// follows one chain of bindings at a time and calls nothing else, so a
    /// cycle terminates as "unresolved" instead of spinning or deciding the
    /// classification on its own repetition. The type-value proof shares its
    /// own budget, `type_value_hops`, because it recurses between the walks.
    const resolved_alias_hops = 8;

    /// The single-file project view the type-aware helpers share. A member of a
    /// namespace this pass cannot read is never guessed from its capitalization,
    /// so the view is deliberately limited to the file under analysis. The
    /// caller keeps the array alive for as long as the resolver borrows it.
    fn singleFileProject(tree: *const std.zig.Ast) [1]import_resolver.File {
        return .{.{ .path = "", .tree = tree }};
    }

    /// Resolve an identifier or member access to the declaration it names and
    /// decide from that declaration whether the expression carries a type.
    ///
    /// Each hop moves one binding closer to the declaration and spends one unit
    /// of the shared budget: an identifier to its own initializer, a member to
    /// the initializer of the member it names. A builtin type name is conclusive
    /// on its own, and a form that cannot produce a type value ends the walk.
    /// The declaration a hop lands on is read through the same refinement every
    /// other declaration gets, so a fieldless struct stays the namespace it is
    /// rather than turning into a type.
    fn resolvedInitIsTypeValue(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
        budget: u8,
    ) bool {
        const files = singleFileProject(tree);
        const resolver = call_resolver.ProjectTypeResolver{ .files = &files, .file_index = 0 };
        var node = init_idx;
        var remaining = budget;
        while (remaining > 0) : (remaining -= 1) {
            if (node >= tags.len) return false;
            switch (tags[node]) {
                .identifier => {
                    if (isBuiltinTypeNode(tree, main_tokens, token_tags, node)) return true;
                    const target = resolver.resolveTypeAliasNode(@intCast(node)) orelse return false;
                    node = target.node_index;
                },
                .field_access => {
                    // A reflection field is not a declaration, so the resolver
                    // has no binding for it; the field name is the proof.
                    if (isTypeInfoDerivedExpr(tree, tags, datas, token_tags, node)) return true;
                    const target = resolver.resolveTypeAliasNode(@intCast(node)) orelse return false;
                    node = target.node_index;
                },
                .unwrap_optional,
                .grouped_expression,
                => node = @intFromEnum(datas[node].node_and_token[0]),
                else => return isTypeValueDeclaration(tree, tags, main_tokens, token_tags, node) or
                    isFunctionTypeTag(tags[node]) or
                    isTypeValueInitExpr(tree, tags, datas, main_tokens, token_tags, node, remaining - 1),
            }
        }
        return false;
    }

    fn isBuiltinTypeNode(
        tree: *const std.zig.Ast,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        if (node_idx >= main_tokens.len) return false;
        const ident_token = main_tokens[node_idx];
        if (ident_token >= token_tags.len or token_tags[ident_token] != .identifier) return false;
        return isBuiltinTypeName(tree.tokenSlice(ident_token));
    }

    /// Prove that a labeled block yields a type value.
    ///
    /// The block produces the value of every `break :label` expression that can
    /// leave it, so all of them must carry a type, and the body has to end by
    /// leaving through that label: a body that can run off its end, or that
    /// leaves through a `return` or another label, evaluates to `void` and
    /// proves nothing. A break with no operand carries nothing to classify, a
    /// break aimed at an inner block of the same name leaves that block
    /// instead, and a body without a break yields nothing at all, so none of
    /// them is accepted as a type.
    fn isTypeValueLabeledBlock(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
        budget: u8,
    ) bool {
        if (budget == 0 or init_idx >= tags.len) return false;
        const block_node: std.zig.Ast.Node.Index = @enumFromInt(init_idx);
        const label_token = labeledBlockLabelToken(tree, block_node) orelse return false;

        var scratch: [2]u32 = undefined;
        const statements = blockStatements(tree, tags, datas, init_idx, &scratch);
        if (statements.len == 0) return false;
        const last_statement: std.zig.Ast.Node.Index = @enumFromInt(statements[statements.len - 1]);
        // Running off the end of the body leaves the label with no value, so
        // the block would be `void` rather than the type a break carries.
        if (!statementExitsBlock(tree, tags, datas, last_statement, block_node)) return false;

        const block_function = enclosingFunctionScope(tree, tags, tree.nodeMainToken(block_node));
        var saw_typed_break = false;
        for (tags, 0..) |tag, node_index| {
            if (tag != .@"break") continue;
            const pair = datas[node_index].opt_token_and_opt_node;
            // A break without a label cannot leave a labeled block.
            const break_label = pair[0].unwrap() orelse continue;
            // A label declaration and a `break :label` are two different
            // tokens, so the name decides which block the break reaches.
            if (!labelsMatch(tree, label_token, break_label)) continue;
            const break_token = main_tokens[node_index];
            if (!breakReachesBlock(tree, tags, break_token, break_label, block_node)) continue;
            // A function body opens its own label scope, so a break inside a
            // nested function cannot leave this block even where the tokens of
            // that function put it inside the block.
            if (enclosingFunctionScope(tree, tags, break_token) != block_function) continue;
            const operand = pair[1].unwrap() orelse return false;
            if (!isTypeValueInitExpr(tree, tags, datas, main_tokens, token_tags, @intFromEnum(operand), budget - 1)) {
                return false;
            }
            saw_typed_break = true;
        }
        return saw_typed_break;
    }

    /// The label a block carries, or null when it is unlabeled. A block's main
    /// token is its `{`, so a label is the identifier in front of the `:` that
    /// precedes it.
    fn labeledBlockLabelToken(
        tree: *const std.zig.Ast,
        block_node: std.zig.Ast.Node.Index,
    ) ?std.zig.Ast.TokenIndex {
        const brace_token = tree.nodeMainToken(block_node);
        if (brace_token < 2) return null;
        if (tree.tokenTag(brace_token - 1) != .colon) return null;
        const label_token = brace_token - 2;
        if (tree.tokenTag(label_token) != .identifier) return null;
        return label_token;
    }

    /// The statements of a block body. A two-statement block keeps them in the
    /// node itself instead of the extra data, so they land in the caller's
    /// scratch space rather than in an allocation.
    fn blockStatements(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        block_idx: usize,
        scratch: *[2]u32,
    ) []const u32 {
        switch (tags[block_idx]) {
            .block, .block_semicolon => {
                const range = datas[block_idx].extra_range;
                const start: usize = @intFromEnum(range.start);
                const end: usize = @intFromEnum(range.end);
                return tree.extra_data[start..end];
            },
            .block_two, .block_two_semicolon => {
                const nodes = datas[block_idx].opt_node_and_opt_node;
                var count: usize = 0;
                if (nodes[0].unwrap()) |node| {
                    scratch[count] = @intFromEnum(node);
                    count += 1;
                }
                if (nodes[1].unwrap()) |node| {
                    scratch[count] = @intFromEnum(node);
                    count += 1;
                }
                return scratch[0..count];
            },
            else => return &.{},
        }
    }

    /// Whether a statement leaves the labeled block through its own label,
    /// which is the only ending that gives the label a value. Running off the
    /// end of the body, a `return`, a `break` aimed at an outer label and a
    /// `break` out of a surrounding loop all leave the block with nothing, so a
    /// body that ends any other way yields `void`.
    fn statementExitsBlock(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        statement: std.zig.Ast.Node.Index,
        block_node: std.zig.Ast.Node.Index,
    ) bool {
        const statement_idx = @intFromEnum(statement);
        if (statement_idx >= tags.len) return false;
        return switch (tags[statement_idx]) {
            .@"break" => blk: {
                const label = datas[statement_idx].opt_token_and_opt_node[0].unwrap() orelse break :blk false;
                break :blk breakReachesBlock(tree, tags, tree.nodeMainToken(statement), label, block_node);
            },
            .@"if", .if_simple => blk: {
                const full_if = tree.fullIf(statement) orelse break :blk false;
                const else_expr = full_if.ast.else_expr.unwrap() orelse break :blk false;
                break :blk statementExitsBlock(tree, tags, datas, full_if.ast.then_expr, block_node) and
                    statementExitsBlock(tree, tags, datas, else_expr, block_node);
            },
            .@"switch", .switch_comma => blk: {
                const full_switch = tree.switchFull(statement);
                if (full_switch.ast.cases.len == 0) break :blk false;
                for (full_switch.ast.cases) |case_node| {
                    const full_case = tree.fullSwitchCase(case_node) orelse break :blk false;
                    if (!statementExitsBlock(tree, tags, datas, full_case.ast.target_expr, block_node)) {
                        break :blk false;
                    }
                }
                break :blk true;
            },
            else => false,
        };
    }

    /// The block a `break :label` reaches: the innermost labeled block whose
    /// label names the same identifier. The name alone is not enough, because
    /// an inner `blk: { break :blk ... }` binds its own label before an outer
    /// block of the same name is in reach.
    fn breakReachesBlock(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        break_token: std.zig.Ast.TokenIndex,
        break_label: std.zig.Ast.TokenIndex,
        block_node: std.zig.Ast.Node.Index,
    ) bool {
        var reached: ?usize = null;
        var reached_span: u32 = std.math.maxInt(u32);
        for (tags, 0..) |tag, node_index| {
            switch (tag) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => {},
                else => continue,
            }
            const node: std.zig.Ast.Node.Index = @enumFromInt(node_index);
            const first_token = tree.firstToken(node);
            const last_token = tree.lastToken(node);
            if (first_token > last_token) continue;
            if (break_token < first_token or break_token > last_token) continue;
            const block_label = labeledBlockLabelToken(tree, node) orelse continue;
            if (!labelsMatch(tree, block_label, break_label)) continue;
            if (reached == null or last_token - first_token < reached_span) {
                reached = node_index;
                reached_span = last_token - first_token;
            }
        }
        return reached != null and reached.? == @intFromEnum(block_node);
    }

    /// The innermost function body a token sits in, or null at container level.
    /// A function body opens its own label scope, so a label of an enclosing
    /// block cannot be reached from inside one.
    fn enclosingFunctionScope(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        token: std.zig.Ast.TokenIndex,
    ) ?usize {
        var enclosing: ?usize = null;
        var enclosing_span: u32 = std.math.maxInt(u32);
        for (tags, 0..) |tag, node_index| {
            switch (tag) {
                .fn_decl, .test_decl => {},
                else => continue,
            }
            const node: std.zig.Ast.Node.Index = @enumFromInt(node_index);
            const first_token = tree.firstToken(node);
            const last_token = tree.lastToken(node);
            if (first_token > last_token) continue;
            if (token < first_token or token > last_token) continue;
            if (enclosing == null or last_token - first_token < enclosing_span) {
                enclosing = node_index;
                enclosing_span = last_token - first_token;
            }
        }
        return enclosing;
    }

    /// Whether a block's label and a `break :label` name the same label.
    fn labelsMatch(
        tree: *const std.zig.Ast,
        block_label: std.zig.Ast.TokenIndex,
        break_label: std.zig.Ast.TokenIndex,
    ) bool {
        return std.mem.eql(u8, labelText(tree, block_label), labelText(tree, break_label));
    }

    /// The identifier a label token names. `@"name"` is the same identifier as
    /// `name`, so both spellings normalize before they compare.
    fn labelText(tree: *const std.zig.Ast, token: std.zig.Ast.TokenIndex) []const u8 {
        return import_resolver.normalizeIdentifier(tree.tokenSlice(token));
    }

    /// Prove that the initializer is a member of a namespace declared by
    /// another file, whose members this pass never resolves.
    ///
    /// The resolved type-versus-value result of such a member is unknown, and an
    /// unknown result must not become an asserted convention, so the caller
    /// leaves the alias alone instead of reading the member's capitalization.
    fn isInvisibleNamespaceMember(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
    ) bool {
        const files = singleFileProject(tree);
        const resolver = call_resolver.ProjectTypeResolver{ .files = &files, .file_index = 0 };
        var node = init_idx;
        var hops: usize = 0;
        while (hops < resolved_alias_hops) : (hops += 1) {
            if (node >= tags.len) return false;
            switch (tags[node]) {
                .field_access, .unwrap_optional, .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
                .identifier => {
                    const target = resolver.resolveTypeAliasNode(@intCast(node)) orelse return false;
                    node = target.node_index;
                },
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    const builtin_name = builtinCallName(tree, tags, token_tags, node) orelse return false;
                    if (!std.mem.eql(u8, builtin_name, "@import")) return false;
                    return isUnresolvedImportPath(tree, node);
                },
                else => return false,
            }
        }
        return false;
    }

    /// An import that names declarations the analyzer resolves outside the file
    /// under analysis. The standard-library and builtin packages keep their own
    /// naming conventions, so their members stay diagnosable; every other
    /// import names a namespace whose members this pass never reads.
    fn isUnresolvedImportPath(tree: *const std.zig.Ast, node_idx: usize) bool {
        const import_path = import_resolver.importPathFromBuiltinCall(tree, node_idx) orelse return false;
        return !std.mem.eql(u8, import_path, "std") and
            !std.mem.eql(u8, import_path, "builtin") and
            !std.mem.eql(u8, import_path, import_resolver.root_import_path);
    }

    /// A member of the verified `std` import whose name is PascalCase names a
    /// standard-library type, so calling it instantiates that type.
    ///
    /// Zig keeps type names PascalCase and function names camelCase, so the
    /// member name distinguishes the two, and the import binding is verified
    /// rather than name-matched, so a local `std` shadow gets no exemption.
    fn isVerifiedStdTypeMemberCallee(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        if (node_idx >= tags.len or tags[node_idx] != .field_access) return false;
        const access = datas[node_idx].node_and_token;
        const field_token = access[1];
        if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return false;
        if (!isPascalCase(tree.tokenSlice(field_token))) return false;
        return isStdQualifiedValue(
            tree,
            tags,
            datas,
            token_tags,
            @intFromEnum(access[0]),
        );
    }

    /// Whether the expression reaches the standard-library namespace, either
    /// through a verified `@import("std")` binding or through a direct
    /// `@import("std")` expression. Anything spelled like `std` without that
    /// provenance is a local declaration and is not trusted.
    fn isStdQualifiedValue(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        if (node_idx >= tags.len) return false;
        return switch (tags[node_idx]) {
            .identifier => blk: {
                const files = [_]import_resolver.File{
                    .{ .path = "", .tree = tree },
                };
                const resolver = call_resolver.ProjectTypeResolver{
                    .files = &files,
                    .file_index = 0,
                };
                break :blk resolver.isVerifiedImportBinding(node_idx, "std");
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => blk: {
                const import_path = import_resolver.importPathFromBuiltinCall(tree, node_idx) orelse break :blk false;
                break :blk std.mem.eql(u8, import_path, "std");
            },
            .field_access => isStdQualifiedValue(
                tree,
                tags,
                datas,
                token_tags,
                @intFromEnum(datas[node_idx].node_and_token[0]),
            ),
            .unwrap_optional,
            .grouped_expression,
            => isStdQualifiedValue(
                tree,
                tags,
                datas,
                token_tags,
                @intFromEnum(datas[node_idx].node_and_token[0]),
            ),
            else => false,
        };
    }

    fn isDirectImport(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
    ) bool {
        const builtin_name = builtinCallName(tree, tags, token_tags, init_idx) orelse return false;
        if (!std.mem.eql(u8, builtin_name, "@import")) return false;

        var params_buf: [2]std.zig.Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&params_buf, @enumFromInt(init_idx)) orelse return false;
        if (params.len != 1) return false;

        const import_path_idx = @intFromEnum(params[0]);
        if (import_path_idx >= tags.len) return false;
        return switch (tags[import_path_idx]) {
            .string_literal, .multiline_string_literal => true,
            else => false,
        };
    }

    /// Check if the init expression is likely a type alias (field access on import, or PascalCase identifier)
    ///
    /// The budget is the shared type-value hop budget, so this naming-based walk
    /// spends it exactly like the proof that calls it.
    fn isLikelyTypeAlias(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
        budget: u8,
    ) bool {
        if (budget == 0) return false;
        const init_tag = tags[init_idx];
        if (isTypeDefinitionTag(init_tag)) return true;
        // Pointer, slice, array, optional and error-union expressions name a
        // type whatever they are built from.
        if (isTypeExpressionTag(init_tag)) return true;

        return switch (init_tag) {
            // Direct identifier reference - check if PascalCase (likely type)
            .identifier => isTypeAliasCallee(tree, tags, datas, token_tags, init_idx),
            // Field access: @import("...").Foo or Module.Type
            .field_access => isTypeAliasCallee(tree, tags, datas, token_tags, init_idx),
            .call, .call_comma, .call_one, .call_one_comma => isTypeFactoryCall(tree, tags, datas, main_tokens, token_tags, init_idx, budget - 1),
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => blk: {
                const builtin_name = builtinCallName(tree, tags, token_tags, init_idx) orelse break :blk false;
                break :blk isTypeFactoryBuiltin(builtin_name);
            },
            .@"switch", .switch_comma => isTypeSwitchAlias(tree, tags, datas, main_tokens, token_tags, init_idx, budget - 1),
            .@"if", .if_simple => isTypeIfAlias(tree, tags, datas, main_tokens, token_tags, init_idx, budget - 1),
            .unwrap_optional,
            .grouped_expression,
            => blk: {
                const data = datas[init_idx].node_and_token;
                break :blk isLikelyTypeAlias(tree, tags, datas, main_tokens, token_tags, @intFromEnum(data[0]), budget - 1);
            },
            else => false,
        };
    }

    /// Whether a branch of a conditional or of a switch carries a type value.
    ///
    /// A branch that is `@compileError` produces no value to classify, so it
    /// counts for every alias. Any other branch counts when its spelling names
    /// a type or when the resolver proves the declaration it binds to be one.
    /// That second proof is what a member spelled `SCREAMING_SNAKE_CASE` needs:
    /// a foreign namespace spells its constants that way far more often than its
    /// types, so `isTypeAliasCallee` rejects the name and only the resolved
    /// declaration shows that such a member is, for instance, the `HMODULE`
    /// handle type a platform API exposes.
    ///
    /// The budget is what the caller has left and both walks it starts spend
    /// it, so a conditional that reaches itself through its own members proves
    /// nothing instead of recursing without end.
    fn isTypeValueBranch(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
        budget: u8,
    ) bool {
        if (isCompileErrorExpr(tree, tags, datas, token_tags, node_idx)) return true;
        if (isLikelyTypeAlias(tree, tags, datas, main_tokens, token_tags, node_idx, budget)) return true;
        return isTypeValueInitExpr(tree, tags, datas, main_tokens, token_tags, node_idx, budget);
    }

    fn isTypeSwitchAlias(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
        budget: u8,
    ) bool {
        if (budget == 0) return false;
        const full_switch = tree.switchFull(@enumFromInt(init_idx));
        for (full_switch.ast.cases) |case_node| {
            const full_case = tree.fullSwitchCase(case_node) orelse return false;
            const target_idx = @intFromEnum(full_case.ast.target_expr);
            if (!isTypeValueBranch(tree, tags, datas, main_tokens, token_tags, target_idx, budget - 1)) return false;
        }
        return true;
    }

    fn isTypeIfAlias(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
        budget: u8,
    ) bool {
        if (budget == 0) return false;
        const full_if = tree.fullIf(@enumFromInt(init_idx)) orelse return false;
        const then_idx = @intFromEnum(full_if.ast.then_expr);
        const else_expr = full_if.ast.else_expr.unwrap() orelse return false;
        const else_idx = @intFromEnum(else_expr);

        const then_is_type = isTypeValueBranch(tree, tags, datas, main_tokens, token_tags, then_idx, budget - 1);
        const else_is_type = isTypeValueBranch(tree, tags, datas, main_tokens, token_tags, else_idx, budget - 1);
        return then_is_type and else_is_type;
    }

    fn isExternalConventionAlias(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
    ) bool {
        return switch (tags[init_idx]) {
            .identifier => isScreamingIdentifier(tree, token_tags, init_idx),
            .field_access => blk: {
                const field_token = datas[init_idx].node_and_token[1];
                if (field_token >= token_tags.len or token_tags[field_token] != .identifier) break :blk false;
                const field_name = tree.tokenSlice(field_token);
                break :blk isScreamingSnakeCase(field_name);
            },
            .unwrap_optional,
            .grouped_expression,
            => blk: {
                const data = datas[init_idx].node_and_token;
                break :blk isExternalConventionAlias(tree, tags, datas, token_tags, @intFromEnum(data[0]));
            },
            else => false,
        };
    }

    fn isScreamingIdentifier(
        tree: *const std.zig.Ast,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        const ident_token = tree.nodes.items(.main_token)[node_idx];
        if (ident_token >= token_tags.len or token_tags[ident_token] != .identifier) return false;
        return isScreamingSnakeCase(tree.tokenSlice(ident_token));
    }

    fn isCompileErrorExpr(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        return switch (tags[node_idx]) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => blk: {
                const builtin_name = builtinCallName(tree, tags, token_tags, node_idx) orelse break :blk false;
                break :blk std.mem.eql(u8, builtin_name, "@compileError");
            },
            .unwrap_optional,
            .grouped_expression,
            => blk: {
                const data = datas[node_idx].node_and_token;
                break :blk isCompileErrorExpr(tree, tags, datas, token_tags, @intFromEnum(data[0]));
            },
            else => false,
        };
    }

    fn builtinCallName(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) ?[]const u8 {
        switch (tags[node_idx]) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {},
            else => return null,
        }

        const builtin_token = tree.nodes.items(.main_token)[node_idx];
        if (builtin_token >= token_tags.len) return null;
        if (token_tags[builtin_token] != .builtin) return null;
        return tree.tokenSlice(builtin_token);
    }

    /// Builtins whose result is a type value. `@FieldType` is matched on its
    /// builtin token, so a local function of the same name cannot borrow the
    /// type classification.
    ///
    /// `@typeInfo` is deliberately absent: it evaluates to a `std.builtin.Type`
    /// union *value*, not a type. `@TypeOf(@typeInfo(T))` is a type and is
    /// covered by `@TypeOf`; a `?type` payload reached through a
    /// `@typeInfo(...)` switch is covered by `isTypeInfoTypeFieldAccess`.
    fn isTypeFactoryBuiltin(name: []const u8) bool {
        return std.mem.eql(u8, name, "@TypeOf") or
            std.mem.eql(u8, name, "@Type") or
            std.mem.eql(u8, name, "@FieldType") or
            std.mem.eql(u8, name, "@This") or
            std.mem.eql(u8, name, "@OpaqueType") or
            std.mem.eql(u8, name, "@Vector") or
            std.mem.eql(u8, name, "@Struct") or
            std.mem.eql(u8, name, "@Enum") or
            std.mem.eql(u8, name, "@Union");
    }

    fn isTypeInfoBuiltin(name: []const u8) bool {
        return std.mem.eql(u8, name, "@typeInfo");
    }

    fn isTypeInfoDerivedExpr(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        return switch (tags[node_idx]) {
            .field_access => blk: {
                const data = datas[node_idx].node_and_token;
                const base_idx = @intFromEnum(data[0]);
                const field_token = data[1];
                if (field_token >= token_tags.len or token_tags[field_token] != .identifier) break :blk false;
                const field_name = tree.tokenSlice(field_token);
                if (!isTypeInfoTypeField(field_name)) break :blk false;
                break :blk isTypeInfoBaseExpr(tree, tags, datas, token_tags, base_idx);
            },
            .unwrap_optional,
            .grouped_expression,
            => blk: {
                const data = datas[node_idx].node_and_token;
                break :blk isTypeInfoDerivedExpr(tree, tags, datas, token_tags, @intFromEnum(data[0]));
            },
            else => false,
        };
    }

    /// The `std.builtin.Type` payload fields whose value is a type (`type` or
    /// `?type`): the pointed-to, element, payload, tag, backing and signature
    /// types. Reading one binds a type value even though `@typeInfo` itself
    /// evaluates to a `std.builtin.Type` union value.
    fn isTypeInfoTypeField(name: []const u8) bool {
        return std.mem.eql(u8, name, "child") or
            std.mem.eql(u8, name, "element_type") or
            std.mem.eql(u8, name, "error_set") or
            std.mem.eql(u8, name, "payload") or
            std.mem.eql(u8, name, "tag_type") or
            std.mem.eql(u8, name, "backing_integer") or
            std.mem.eql(u8, name, "return_type") or
            std.mem.eql(u8, name, "type");
    }

    /// Expressions that are a type by construction rather than by their name.
    fn isTypeExpressionTag(tag: std.zig.Ast.Node.Tag) bool {
        return switch (tag) {
            .merge_error_sets,
            .error_union,
            .optional_type,
            .anyframe_type,
            .ptr_type,
            .ptr_type_sentinel,
            .ptr_type_bit_range,
            .ptr_type_aligned,
            .array_type,
            .array_type_sentinel,
            => true,
            else => false,
        };
    }

    fn isTypeInfoBaseExpr(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        return switch (tags[node_idx]) {
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => isTypeInfoBuiltinCall(tree, tags, token_tags, node_idx),
            .field_access => blk: {
                const data = datas[node_idx].node_and_token;
                break :blk isTypeInfoBaseExpr(tree, tags, datas, token_tags, @intFromEnum(data[0]));
            },
            .unwrap_optional,
            .grouped_expression,
            => blk: {
                const data = datas[node_idx].node_and_token;
                break :blk isTypeInfoBaseExpr(tree, tags, datas, token_tags, @intFromEnum(data[0]));
            },
            else => false,
        };
    }

    fn isTypeInfoBuiltinCall(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        const builtin_name = builtinCallName(tree, tags, token_tags, node_idx) orelse return false;
        return isTypeInfoBuiltin(builtin_name);
    }

    fn isTypeAliasCallee(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        const tag = tags[node_idx];
        return switch (tag) {
            .identifier => {
                const ident_token = tree.nodes.items(.main_token)[node_idx];
                if (ident_token >= token_tags.len or token_tags[ident_token] != .identifier) return false;
                const ident_name = tree.tokenSlice(ident_token);
                return isPascalCase(ident_name) or isBuiltinTypeName(ident_name) or isCTypeAliasName(ident_name);
            },
            .field_access => {
                if (isTypeInfoDerivedExpr(tree, tags, datas, token_tags, node_idx)) return true;
                const data = datas[node_idx];
                const field_token = data.node_and_token[1];
                if (field_token < token_tags.len and token_tags[field_token] == .identifier) {
                    const field_name = tree.tokenSlice(field_token);
                    // A SCREAMING_SNAKE_CASE member names a flag, an enum value
                    // or a foreign constant, never a type, and a codec member
                    // of the standard library is a codec instance. Both are
                    // values whatever their capitalization suggests.
                    if (isScreamingSnakeCase(field_name)) return false;
                    if (isStdCodecValueMember(tree, tags, datas, token_tags, node_idx)) return false;
                    return isPascalCase(field_name) or isCTypeAliasName(field_name);
                }
                return false;
            },
            .unwrap_optional,
            .grouped_expression,
            => {
                const data = datas[node_idx].node_and_token;
                return isTypeAliasCallee(tree, tags, datas, token_tags, @intFromEnum(data[0]));
            },
            else => false,
        };
    }

    /// `std.base64.standard` and its siblings are `Codecs` values, so their
    /// `Encoder` and `Decoder` members hold initialized codec instances rather
    /// than types. Binding one of them binds a value, and a value keeps the
    /// snake_case rule even though the member name is PascalCase.
    ///
    /// Only the verified `@import("std")` namespace is trusted for this, and
    /// only the documented codec sets and member names are matched, so a local
    /// declaration spelled the same way keeps the type classification.
    fn isStdCodecValueMember(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
    ) bool {
        if (!isMemberNamed(tree, tags, datas, token_tags, node_idx, "Encoder") and
            !isMemberNamed(tree, tags, datas, token_tags, node_idx, "Decoder")) return false;
        const codec_set_idx = @intFromEnum(datas[node_idx].node_and_token[0]);
        if (!isMemberNamed(tree, tags, datas, token_tags, codec_set_idx, "standard") and
            !isMemberNamed(tree, tags, datas, token_tags, codec_set_idx, "standard_no_pad") and
            !isMemberNamed(tree, tags, datas, token_tags, codec_set_idx, "url_safe")) return false;
        const base64_idx = @intFromEnum(datas[codec_set_idx].node_and_token[0]);
        if (!isMemberNamed(tree, tags, datas, token_tags, base64_idx, "base64")) return false;
        return isStdQualifiedValue(tree, tags, datas, token_tags, @intFromEnum(datas[base64_idx].node_and_token[0]));
    }

    /// Whether `node_idx` is a field access whose member is spelled `name`.
    fn isMemberNamed(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        node_idx: usize,
        name: []const u8,
    ) bool {
        if (node_idx >= tags.len or tags[node_idx] != .field_access) return false;
        const field_token = datas[node_idx].node_and_token[1];
        if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return false;
        return std.mem.eql(u8, tree.tokenSlice(field_token), name);
    }

    fn isCTypeAliasName(name: []const u8) bool {
        if (!isLowerSnakeCase(name)) return false;
        return std.mem.endsWith(u8, name, "_t");
    }

    fn isBuiltinTypeName(name: []const u8) bool {
        if (std.mem.eql(u8, name, "bool") or
            std.mem.eql(u8, name, "void") or
            std.mem.eql(u8, name, "noreturn") or
            std.mem.eql(u8, name, "type") or
            std.mem.eql(u8, name, "anytype") or
            std.mem.eql(u8, name, "anyopaque") or
            std.mem.eql(u8, name, "anyerror") or
            std.mem.eql(u8, name, "usize") or
            std.mem.eql(u8, name, "isize") or
            std.mem.eql(u8, name, "comptime_int") or
            std.mem.eql(u8, name, "comptime_float"))
        {
            return true;
        }

        if (name.len < 2) return false;
        const prefix = name[0];
        if (prefix != 'u' and prefix != 'i' and prefix != 'f') return false;
        for (name[1..]) |c| {
            if (!std.ascii.isDigit(c)) return false;
        }
        return true;
    }

    fn isTypeFactoryCall(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
        budget: u8,
    ) bool {
        if (budget == 0) return false;
        var buf: [1]std.zig.Ast.Node.Index = undefined;
        const call_info = tree.fullCall(&buf, @enumFromInt(init_idx)) orelse return false;
        const callee_idx = @intFromEnum(call_info.ast.fn_expr);
        if (!isTypeAliasCallee(tree, tags, datas, token_tags, callee_idx)) return false;
        const is_verified_std_type = isVerifiedStdTypeMemberCallee(
            tree,
            tags,
            datas,
            token_tags,
            callee_idx,
        );

        var saw_type_arg = false;
        for (call_info.ast.params) |param| {
            const arg_idx = @intFromEnum(param);
            if (isLikelyTypeAlias(tree, tags, datas, main_tokens, token_tags, arg_idx, budget - 1)) {
                saw_type_arg = true;
                continue;
            }
            if (is_verified_std_type and isStdQualifiedValue(tree, tags, datas, token_tags, arg_idx)) {
                continue;
            }
            if (isTypeFactoryLiteral(tags, datas, arg_idx)) {
                continue;
            }
            return false;
        }

        // A type argument is the usual proof, but a standard-library type
        // instantiated from literal arguments only (`std.StaticBitSet(256)`)
        // is just as conclusive once the callee is proved to be a type.
        return saw_type_arg or is_verified_std_type;
    }

    fn isTypeFactoryLiteral(
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        node_idx: usize,
    ) bool {
        return switch (tags[node_idx]) {
            .number_literal,
            .string_literal,
            .multiline_string_literal,
            .char_literal,
            .enum_literal,
            => true,
            .unwrap_optional,
            .grouped_expression,
            => blk: {
                const data = datas[node_idx].node_and_token;
                break :blk isTypeFactoryLiteral(tags, datas, @intFromEnum(data[0]));
            },
            else => false,
        };
    }

    fn isFunctionAlias(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        init_idx: usize,
    ) bool {
        const init_tag = tags[init_idx];

        switch (init_tag) {
            .identifier => {
                const ident_token = tree.nodes.items(.main_token)[init_idx];
                if (ident_token >= token_tags.len or token_tags[ident_token] != .identifier) return false;
                const ident_name = tree.tokenSlice(ident_token);
                return isCamelCase(ident_name);
            },
            .field_access => {
                const data = datas[init_idx];
                const field_token = data.node_and_token[1];
                if (field_token < token_tags.len and token_tags[field_token] == .identifier) {
                    const field_name = tree.tokenSlice(field_token);
                    return isCamelCase(field_name);
                }
                return false;
            },
            else => return false,
        }
    }

    fn emitDiagnostic(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        byte_offset: u32,
        name: []const u8,
        kind: []const u8,
        expected_style: Style,
    ) RuleError!void {
        const loc = try src.byteToLocation(byte_offset);
        const style_name = switch (expected_style) {
            .pascal_case => "PascalCase",
            .camel_case => "camelCase",
            .snake_case => "snake_case",
        };
        const message = try std.fmt.allocPrint(
            allocator,
            "{s} '{s}' should use {s} naming",
            .{ kind, name, style_name },
        );
        defer allocator.free(message);

        const diag = try Diagnostic.initAtLocation(
            allocator,
            src.getFilePath(),
            "identifier-style",
            .warning,
            message,
            loc.line,
            loc.column,
        );
        try diagnostics.append(allocator, diag);
    }

    fn isTypeDefinitionTag(tag: std.zig.Ast.Node.Tag) bool {
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
            .error_set_decl,
            => true,
            else => false,
        };
    }

    fn isStructContainer(
        node_idx: usize,
        main_tokens: []const std.zig.Ast.TokenIndex,
        token_tags: []const std.zig.Token.Tag,
    ) bool {
        if (node_idx >= main_tokens.len) return false;
        const token = main_tokens[node_idx];
        if (token >= token_tags.len) return false;
        return token_tags[token] == .keyword_struct;
    }

    fn containerHasFields(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        node_idx: usize,
    ) bool {
        var buf: [2]std.zig.Ast.Node.Index = undefined;

        const members: []const std.zig.Ast.Node.Index = switch (tags[node_idx]) {
            .container_decl, .container_decl_trailing => tree.containerDecl(@enumFromInt(node_idx)).ast.members,
            .container_decl_two, .container_decl_two_trailing => tree.containerDeclTwo(&buf, @enumFromInt(node_idx)).ast.members,
            .container_decl_arg, .container_decl_arg_trailing => tree.containerDeclArg(@enumFromInt(node_idx)).ast.members,
            .tagged_union, .tagged_union_trailing => tree.taggedUnion(@enumFromInt(node_idx)).ast.members,
            .tagged_union_enum_tag, .tagged_union_enum_tag_trailing => tree.taggedUnionEnumTag(@enumFromInt(node_idx)).ast.members,
            .tagged_union_two, .tagged_union_two_trailing => tree.taggedUnionTwo(&buf, @enumFromInt(node_idx)).ast.members,
            else => return false,
        };

        for (members) |member| {
            if (isContainerField(tags[@intFromEnum(member)])) return true;
        }

        return false;
    }

    fn isContainerField(tag: std.zig.Ast.Node.Tag) bool {
        return switch (tag) {
            .container_field,
            .container_field_init,
            .container_field_align,
            => true,
            else => false,
        };
    }

    fn isNamespaceStructDecl(src: *Source, decl: zir_bridge_mod.DeclInfo) bool {
        const ast_node = decl.ast_node orelse return false;
        const tree = src.ast() catch return false;
        const tags = tree.nodes.items(.tag);
        const main_tokens = tree.nodes.items(.main_token);
        const token_tags = tree.tokens.items(.tag);

        const full = tree.fullVarDecl(@enumFromInt(ast_node)) orelse return false;
        const init_node = full.ast.init_node.unwrap() orelse return false;
        const init_idx = @intFromEnum(init_node);
        if (init_idx >= tags.len) return false;
        if (!isTypeDefinitionTag(tags[init_idx])) return false;
        if (!isStructContainer(init_idx, main_tokens, token_tags)) return false;

        return !containerHasFields(tree, tags, init_idx);
    }

    fn findDeclByAstNode(src: *Source, node_idx: u32) ?zir_bridge_mod.DeclInfo {
        const count = src.getDeclCount();
        for (0..count) |i| {
            if (src.getDecl(i)) |decl| {
                if (decl.ast_node) |decl_node| {
                    if (decl_node == node_idx) return decl;
                }
            }
        }
        return null;
    }

    fn isFunctionTypeTag(tag: std.zig.Ast.Node.Tag) bool {
        return switch (tag) {
            .fn_proto,
            .fn_proto_simple,
            .fn_proto_one,
            .fn_proto_multi,
            => true,
            else => false,
        };
    }

    fn shouldSkipName(name: []const u8) bool {
        if (name.len == 0) return true;
        // Skip names starting with underscore (intentionally ignored)
        if (name[0] == '_') return true;
        // Skip special names
        if (std.mem.eql(u8, name, "main")) return true;
        if (std.mem.eql(u8, name, "panic")) return true;
        // Skip @"quoted" identifiers which may need to break conventions
        if (name.len >= 3 and std.mem.startsWith(u8, name, "@\"")) return true;
        return false;
    }

    /// Check if name follows PascalCase: starts with uppercase, no underscores between words
    fn isPascalCase(name: []const u8) bool {
        if (name.len == 0) return false;
        // Must start with uppercase letter
        if (!std.ascii.isUpper(name[0])) return false;
        // Should not contain underscores (except trailing for disambiguation like Type_)
        for (name[1..], 1..) |c, i| {
            if (c == '_') {
                // Allow trailing underscore for disambiguation
                if (i == name.len - 1) continue;
                return false;
            }
        }
        return true;
    }

    /// Check if name follows camelCase: starts with lowercase, no underscores between words
    fn isCamelCase(name: []const u8) bool {
        if (name.len == 0) return false;
        // Must start with lowercase letter
        if (!std.ascii.isLower(name[0])) return false;
        // Should not contain underscores
        for (name[1..]) |c| {
            if (c == '_') return false;
        }
        return true;
    }

    /// Check if name follows snake_case: all lowercase with underscores
    fn isSnakeCase(name: []const u8) bool {
        return isLowerSnakeCase(name);
    }

    fn isLowerSnakeCase(name: []const u8) bool {
        if (name.len == 0) return false;

        var has_lower = false;
        for (name) |c| {
            if (std.ascii.isLower(c)) {
                has_lower = true;
                continue;
            }
            if (std.ascii.isUpper(c)) return false;
            if (std.ascii.isDigit(c)) continue;
            if (c == '_') continue;
            return false;
        }

        return has_lower;
    }

    fn isScreamingSnakeCase(name: []const u8) bool {
        if (name.len == 0) return false;

        var has_upper = false;
        for (name) |c| {
            if (std.ascii.isUpper(c)) {
                has_upper = true;
                continue;
            }
            if (std.ascii.isLower(c)) return false;
            if (std.ascii.isDigit(c)) continue;
            if (c == '_') continue;
            return false;
        }

        return has_upper;
    }

    /// What a capture binds. A capture of a `?type` field binds a type value,
    /// which follows the PascalCase rule instead of the snake_case value rule.
    const PayloadKind = enum {
        value,
        type_value,
    };

    fn checkSnakeCaseToken(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
        token: u32,
        kind: []const u8,
        capture: PayloadKind,
    ) RuleError!void {
        if (token >= token_tags.len or token_tags[token] != .identifier) return;
        const name = tree.tokenSlice(token);
        if (shouldSkipName(name)) return;
        if (capture == .type_value and isPascalCase(name)) return;
        if (!isLowerSnakeCase(name)) {
            try emitDiagnostic(src, allocator, diagnostics, token_starts[token], name, kind, .snake_case);
        }
    }

    fn checkParamName(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
        token: u32,
        param: std.zig.Ast.full.FnProto.Param,
    ) RuleError!void {
        if (token >= token_tags.len or token_tags[token] != .identifier) return;
        const name = tree.tokenSlice(token);
        if (shouldSkipName(name)) return;
        if (isLowerSnakeCase(name)) return;
        if (isTypeParam(tree, param) and isPascalCase(name)) return;
        try emitDiagnostic(src, allocator, diagnostics, token_starts[token], name, "parameter", .snake_case);
    }

    fn isBuiltinTypeExpr(tree: *const std.zig.Ast, node_idx: u32) bool {
        const tags = tree.nodes.items(.tag);
        if (node_idx >= tags.len) return false;
        if (tags[node_idx] != .identifier) return false;
        const ident_token = tree.nodes.items(.main_token)[node_idx];
        if (tree.tokenTag(ident_token) != .identifier) return false;
        return std.mem.eql(u8, tree.tokenSlice(ident_token), "type");
    }

    fn isTypeParam(tree: *const std.zig.Ast, param: std.zig.Ast.full.FnProto.Param) bool {
        if (param.anytype_ellipsis3 != null) return true;
        const comptime_token = param.comptime_noalias orelse return false;
        if (tree.tokenTag(comptime_token) != .keyword_comptime) return false;
        const type_expr = param.type_expr orelse return false;
        return isBuiltinTypeExpr(tree, @intFromEnum(type_expr));
    }

    fn checkIfPayloads(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
    ) RuleError!void {
        const full_if = tree.fullIf(@enumFromInt(node_idx)) orelse return;
        const capture = conditionCaptureKind(tree, token_tags, @intFromEnum(full_if.ast.cond_expr));
        if (full_if.payload_token) |tok| {
            try checkPayloadToken(src, allocator, diagnostics, tree, token_tags, token_starts, tok, "payload", capture);
        }
        if (full_if.error_token) |tok| {
            try checkPayloadToken(src, allocator, diagnostics, tree, token_tags, token_starts, tok, "payload", .value);
        }
    }

    fn checkWhilePayloads(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
    ) RuleError!void {
        const tags = tree.nodes.items(.tag);
        const full_while = switch (tags[node_idx]) {
            .while_simple => tree.whileSimple(@enumFromInt(node_idx)),
            .while_cont => tree.whileCont(@enumFromInt(node_idx)),
            .@"while" => tree.whileFull(@enumFromInt(node_idx)),
            else => return,
        };

        const capture = conditionCaptureKind(tree, token_tags, @intFromEnum(full_while.ast.cond_expr));
        if (full_while.payload_token) |tok| {
            try checkPayloadToken(src, allocator, diagnostics, tree, token_tags, token_starts, tok, "payload", capture);
        }
        if (full_while.error_token) |tok| {
            try checkPayloadToken(src, allocator, diagnostics, tree, token_tags, token_starts, tok, "payload", .value);
        }
    }

    fn checkForPayloads(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
    ) RuleError!void {
        const tags = tree.nodes.items(.tag);
        const full_for = switch (tags[node_idx]) {
            .@"for" => tree.forFull(@enumFromInt(node_idx)),
            .for_simple => tree.forSimple(@enumFromInt(node_idx)),
            else => return,
        };

        try checkForPayloadTokens(src, allocator, diagnostics, tree, token_tags, token_starts, full_for.payload_token);
    }

    fn checkSwitchPayloads(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
    ) RuleError!void {
        const full_switch = tree.switchFull(@enumFromInt(node_idx));
        for (full_switch.ast.cases) |case_node| {
            const full_case = tree.fullSwitchCase(case_node) orelse continue;
            if (full_case.payload_token) |tok| {
                try checkPayloadToken(src, allocator, diagnostics, tree, token_tags, token_starts, tok, "payload", .value);
            }
        }
    }

    fn checkCatchPayload(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
    ) RuleError!void {
        const main_tokens = tree.nodes.items(.main_token);
        const catch_token = main_tokens[node_idx];
        if (catch_token + 2 >= token_tags.len) return;
        if (token_tags[catch_token + 1] != .pipe) return;
        try checkPayloadToken(src, allocator, diagnostics, tree, token_tags, token_starts, catch_token + 2, "payload", .value);
    }

    fn checkErrdeferPayload(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        node_idx: u32,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
    ) RuleError!void {
        const data = tree.nodes.items(.data)[node_idx].opt_token_and_node;
        const payload_token = data[0].unwrap() orelse return;
        try checkPayloadToken(src, allocator, diagnostics, tree, token_tags, token_starts, payload_token, "payload", .value);
    }

    fn checkPayloadToken(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
        token: u32,
        kind: []const u8,
        capture: PayloadKind,
    ) RuleError!void {
        if (token >= token_tags.len) return;
        var idx = token;
        if (token_tags[idx] == .pipe) idx += 1;
        if (idx < token_tags.len and token_tags[idx] == .asterisk) idx += 1;
        if (idx < token_tags.len and token_tags[idx] == .identifier) {
            try checkSnakeCaseToken(src, allocator, diagnostics, tree, token_tags, token_starts, idx, kind, capture);
        }
    }

    fn checkForPayloadTokens(
        src: *Source,
        allocator: std.mem.Allocator,
        diagnostics: *std.ArrayList(Diagnostic),
        tree: *const std.zig.Ast,
        token_tags: []const std.zig.Token.Tag,
        token_starts: []const u32,
        token: u32,
    ) RuleError!void {
        var idx = token;
        if (idx >= token_tags.len) return;

        if (token_tags[idx] == .pipe) idx += 1;
        while (idx < token_tags.len) : (idx += 1) {
            const tag = token_tags[idx];
            if (tag == .pipe) break;
            if (tag == .asterisk) {
                idx += 1;
                if (idx < token_tags.len and token_tags[idx] == .identifier) {
                    try checkSnakeCaseToken(src, allocator, diagnostics, tree, token_tags, token_starts, idx, "payload", .value);
                }
                continue;
            }
            if (tag == .identifier) {
                try checkSnakeCaseToken(src, allocator, diagnostics, tree, token_tags, token_starts, idx, "payload", .value);
            }
        }
    }

    /// Decide what an `if`/`while` capture binds from the operand expression.
    fn conditionCaptureKind(
        tree: *const std.zig.Ast,
        token_tags: []const std.zig.Token.Tag,
        cond_idx: usize,
    ) PayloadKind {
        if (isTypeInfoTypeFieldAccess(tree, token_tags, cond_idx)) return .type_value;
        return .value;
    }

    /// Prove that the operand is a type-carrying field of a `@typeInfo`
    /// payload.
    ///
    /// `std.builtin.Type` declares exactly these payload fields as `type` or
    /// `?type` (`Struct.backing_integer`, `Enum.tag_type`, `Union.tag_type`,
    /// `ErrorUnion.error_set`, `ErrorUnion.payload`, `Fn.return_type`,
    /// `Fn.Param.type`, `AnyFrame.child`), so reading one binds a type value
    /// rather than a value. The receiver has to be a payload captured from a
    /// `@typeInfo(...)` switch, and both the builtin token and the std payload
    /// names are matched, so a local `typeInfo` function or an unrelated
    /// `tag_type` field gets no exemption.
    fn isTypeInfoTypeFieldAccess(
        tree: *const std.zig.Ast,
        token_tags: []const std.zig.Token.Tag,
        cond_idx: usize,
    ) bool {
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        const main_tokens = tree.nodes.items(.main_token);
        if (cond_idx >= tags.len) return false;

        var node = cond_idx;
        while (tags[node] == .unwrap_optional or tags[node] == .grouped_expression) {
            node = @intFromEnum(datas[node].node_and_token[0]);
            if (node >= tags.len) return false;
        }
        if (tags[node] != .field_access) return false;

        const field_token = datas[node].node_and_token[1];
        if (field_token >= token_tags.len or token_tags[field_token] != .identifier) return false;
        if (!isOptionalTypeInfoFieldName(tree.tokenSlice(field_token))) return false;

        const receiver_idx = @intFromEnum(datas[node].node_and_token[0]);
        if (receiver_idx >= tags.len or tags[receiver_idx] != .identifier) return false;
        const receiver_token = main_tokens[receiver_idx];
        if (receiver_token >= token_tags.len or token_tags[receiver_token] != .identifier) return false;

        return isTypeInfoSwitchCapture(
            tree,
            tags,
            datas,
            token_tags,
            tree.tokenSlice(receiver_token),
            receiver_token,
        );
    }

    fn isOptionalTypeInfoFieldName(name: []const u8) bool {
        return isTypeInfoTypeField(name);
    }

    /// Prove that `name` is a capture of a prong of a `switch (@typeInfo(...))`
    /// that encloses `reference_token`.
    fn isTypeInfoSwitchCapture(
        tree: *const std.zig.Ast,
        tags: []const std.zig.Ast.Node.Tag,
        datas: []const std.zig.Ast.Node.Data,
        token_tags: []const std.zig.Token.Tag,
        name: []const u8,
        reference_token: u32,
    ) bool {
        for (tags, 0..) |tag, node_index| {
            if (tag != .@"switch" and tag != .switch_comma) continue;
            const switch_node: std.zig.Ast.Node.Index = @enumFromInt(node_index);
            if (tree.firstToken(switch_node) > reference_token) continue;
            if (tree.lastToken(switch_node) < reference_token) continue;
            const full_switch = tree.switchFull(switch_node);
            if (!isTypeInfoBaseExpr(tree, tags, datas, token_tags, @intFromEnum(full_switch.ast.condition))) continue;
            for (full_switch.ast.cases) |case_node| {
                const full_case = tree.fullSwitchCase(case_node) orelse continue;
                const payload_token = full_case.payload_token orelse continue;
                if (payload_token >= token_tags.len or token_tags[payload_token] != .identifier) continue;
                if (std.mem.eql(u8, tree.tokenSlice(payload_token), name)) return true;
            }
        }
        return false;
    }
};

test "isPascalCase" {
    const isPascalCase = IdentifierStyleRule.isPascalCase;
    try std.testing.expect(isPascalCase("Foo"));
    try std.testing.expect(isPascalCase("FooBar"));
    try std.testing.expect(isPascalCase("FooBarBaz"));
    try std.testing.expect(isPascalCase("F"));
    try std.testing.expect(isPascalCase("Type_")); // trailing underscore allowed
    try std.testing.expect(!isPascalCase("foo"));
    try std.testing.expect(!isPascalCase("fooBar"));
    try std.testing.expect(!isPascalCase("foo_bar"));
    try std.testing.expect(!isPascalCase("Foo_Bar"));
    try std.testing.expect(!isPascalCase("FOO_BAR"));
}

test "isCamelCase" {
    const isCamelCase = IdentifierStyleRule.isCamelCase;
    try std.testing.expect(isCamelCase("foo"));
    try std.testing.expect(isCamelCase("fooBar"));
    try std.testing.expect(isCamelCase("fooBarBaz"));
    try std.testing.expect(isCamelCase("f"));
    try std.testing.expect(!isCamelCase("Foo"));
    try std.testing.expect(!isCamelCase("FooBar"));
    try std.testing.expect(!isCamelCase("foo_bar"));
    try std.testing.expect(!isCamelCase("foo_Bar"));
}

test "isSnakeCase" {
    const isSnakeCase = IdentifierStyleRule.isSnakeCase;
    try std.testing.expect(isSnakeCase("foo"));
    try std.testing.expect(isSnakeCase("foo_bar"));
    try std.testing.expect(isSnakeCase("foo_bar_baz"));
    try std.testing.expect(!isSnakeCase("fooBar"));
    try std.testing.expect(!isSnakeCase("FooBar"));
    try std.testing.expect(!isSnakeCase("foo_Bar"));
    try std.testing.expect(!isSnakeCase("FOO"));
    try std.testing.expect(!isSnakeCase("FOO_BAR"));
}

test "isLowerSnakeCase" {
    const isLowerSnakeCase = IdentifierStyleRule.isLowerSnakeCase;
    try std.testing.expect(isLowerSnakeCase("foo"));
    try std.testing.expect(isLowerSnakeCase("foo_bar"));
    try std.testing.expect(isLowerSnakeCase("foo2_bar3"));
    try std.testing.expect(!isLowerSnakeCase("FOO"));
    try std.testing.expect(!isLowerSnakeCase("Foo"));
    try std.testing.expect(!isLowerSnakeCase("foo_Bar"));
}

test "isScreamingSnakeCase" {
    const isScreamingSnakeCase = IdentifierStyleRule.isScreamingSnakeCase;
    try std.testing.expect(isScreamingSnakeCase("FOO"));
    try std.testing.expect(isScreamingSnakeCase("FOO_BAR"));
    try std.testing.expect(isScreamingSnakeCase("FOO2_BAR3"));
    try std.testing.expect(isScreamingSnakeCase("MAX_SIZE"));
    try std.testing.expect(!isScreamingSnakeCase("foo"));
    try std.testing.expect(!isScreamingSnakeCase("Foo"));
    try std.testing.expect(!isScreamingSnakeCase("foo_Bar"));
}

test "classifyDeclWithTypeInfo for struct" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "const MyStruct = struct { value: i32 };";
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const root_decls = tree.rootDecls();
    const node_idx = @intFromEnum(root_decls[0]);
    const classification = IdentifierStyleRule.classifyDeclWithTypeInfo(&source, "MyStruct", node_idx);
    try std.testing.expectEqual(IdentifierStyleRule.DeclClassification.type_decl, classification);
}

test "classifyDeclWithTypeInfo for enum" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "const MyEnum = enum { a, b, c };";
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const root_decls = tree.rootDecls();
    const node_idx = @intFromEnum(root_decls[0]);
    const classification = IdentifierStyleRule.classifyDeclWithTypeInfo(&source, "MyEnum", node_idx);
    try std.testing.expectEqual(IdentifierStyleRule.DeclClassification.type_decl, classification);
}

test "classifyDeclWithTypeInfo for constant" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "const my_const: i32 = 42;";
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const root_decls = tree.rootDecls();
    const node_idx = @intFromEnum(root_decls[0]);
    const classification = IdentifierStyleRule.classifyDeclWithTypeInfo(&source, "my_const", node_idx);
    try std.testing.expectEqual(IdentifierStyleRule.DeclClassification.constant, classification);
}

test "classifyDeclWithTypeInfo for variable" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "var my_var: i32 = 0;";
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const root_decls = tree.rootDecls();
    const node_idx = @intFromEnum(root_decls[0]);
    const classification = IdentifierStyleRule.classifyDeclWithTypeInfo(&source, "my_var", node_idx);
    try std.testing.expectEqual(IdentifierStyleRule.DeclClassification.variable, classification);
}

test "classifyDeclWithTypeInfo for function" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "fn myFunc() void {}";
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const root_decls = tree.rootDecls();
    const node_idx = @intFromEnum(root_decls[0]);
    const classification = IdentifierStyleRule.classifyDeclWithTypeInfo(&source, "myFunc", node_idx);
    try std.testing.expectEqual(IdentifierStyleRule.DeclClassification.function, classification);
}

test "classifyDeclWithTypeInfo returns unknown for nonexistent" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 = "const x: i32 = 42;";
    var source = Source.init(allocator, "test.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const root_decls = tree.rootDecls();
    const node_idx = @intFromEnum(root_decls[0]);
    const classification = IdentifierStyleRule.classifyDeclWithTypeInfo(&source, "nonexistent", node_idx);
    try std.testing.expectEqual(IdentifierStyleRule.DeclClassification.unknown, classification);
}

test "skript residual: std.HashMap generated type keeps PascalCase" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const RuntimeMap = std.HashMap(
        \\    MapKey,
        \\    Value,
        \\    MapKey.Context,
        \\    std.hash_map.default_max_load_percentage,
        \\);
        \\const BadValue = std.hash_map.default_max_load_percentage;
    ;
    var source = Source.init(allocator, "skript-regression.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "BadValue") != null);
}

test "skript control: shadowed std binding rejects factory exemption" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const MapKey = struct {};
        \\const Value = struct {};
        \\fn make() void {
        \\    const std = @import("other.zig");
        \\    const RuntimeMap = std.HashMap(
        \\        MapKey,
        \\        Value,
        \\        MapKey.Context,
        \\        std.hash_map.default_max_load_percentage,
        \\    );
        \\}
    ;
    var source = Source.init(allocator, "skript-regression.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "RuntimeMap") != null);
}

test "@FieldType type alias still requires PascalCase" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const FnTableEntry = struct { closure_sites: []const u32 };
        \\const ClosureSites = @FieldType(FnTableEntry, "closure_sites");
        \\const closure_sites = @FieldType(FnTableEntry, "closure_sites");
    ;
    var source = Source.init(allocator, "type-builtin.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 3), diagnostics.items[0].range.start.line);
}

test "@typeInfo result is a value, so a snake_case name is accepted" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const type_info = @typeInfo(u8);
        \\const fn_info = @typeInfo(fn () void).@"fn";
    ;
    var source = Source.init(allocator, "typeinfo-value.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

test "@typeInfo result is a value, so a PascalCase name is reported" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const TypeInfo = @typeInfo(u8);
    ;
    var source = Source.init(allocator, "typeinfo-value.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items[0].range.start.line);
}

test "@TypeOf of a @typeInfo value is a type, so a PascalCase alias is kept" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const TypeOfInfo = @TypeOf(@typeInfo(u8));
        \\const type_of_info = @TypeOf(@typeInfo(u8));
    ;
    var source = Source.init(allocator, "typeof-typeinfo.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items[0].range.start.line);
}

test "standard-library type instantiated from literal arguments only keeps a PascalCase alias" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const FiniteParameters = std.StaticBitSet(256);
        \\const finite_parameters = std.StaticBitSet(256);
    ;
    var source = Source.init(allocator, "std-factory.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 3), diagnostics.items[0].range.start.line);
}

test "conditional type alias requires a type value in every branch" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const builtin = @import("builtin");
        \\const win = struct { pub const HMODULE = void; };
        \\const NativeLibraryHandle = if (builtin.os.tag == .windows)
        \\    win.HMODULE
        \\else if (builtin.link_mode == .static)
        \\    @FieldType(std.DynLib, "inner")
        \\else
        \\    std.DynLib;
        \\const MixedAlias = if (builtin.os.tag == .windows) win.HMODULE else 1;
    ;
    var source = Source.init(allocator, "conditional-type.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 10), diagnostics.items[0].range.start.line);
}

test "control: shadowed std binding rejects a literal-only type instantiation" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn probe() void {
        \\    const std = struct {
        \\        pub const Bits = fn (comptime n: u8) u8;
        \\    };
        \\    const BitCount = std.Bits(3);
        \\    _ = BitCount;
        \\}
    ;
    var source = Source.init(allocator, "shadowed-factory.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);

    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 6), diagnostics.items[0].range.start.line);
}

test "capture of a typeInfo ?type payload binds a type value" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn trace(comptime T: type) void {
        \\    switch (@typeInfo(T)) {
        \\        .@"union" => |info| {
        \\            if (info.tag_type) |Tag| {
        \\                _ = @sizeOf(Tag);
        \\            }
        \\            while (info.tag_type) |Inner| {
        \\                _ = @sizeOf(Inner);
        \\            } else {}
        \\            if (info.fields) |Fields| {
        \\                _ = Fields.len;
        \\            }
        \\        },
        \\        else => {},
        \\    }
        \\}
    ;
    var source = Source.init(allocator, "typeinfo-capture.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 11), diagnostics.items[0].range.start.line);
}

test "control: a local typeInfo function payload is a value capture" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Info = struct { tag_type: ?u8 = null };
        \\fn typeInfo(comptime T: type) Info {
        \\    _ = T;
        \\    return .{};
        \\}
        \\fn probe() void {
        \\    const info = typeInfo(u8);
        \\    if (info.tag_type) |Tag| {
        \\        _ = Tag;
        \\    }
        \\}
    ;
    var source = Source.init(allocator, "fake-typeinfo.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 8), diagnostics.items[0].range.start.line);
}

test "switch mixing a type and a value gains no type authority" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const builtin = @import("builtin");
        \\const TypedChoice = switch (builtin.os.tag) {
        \\    .windows => std.DynLib,
        \\    else => 0,
        \\};
        \\const typed_choice = switch (builtin.os.tag) {
        \\    .windows => std.DynLib,
        \\    else => 0,
        \\};
    ;
    var source = Source.init(allocator, "switch-mixed.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 3), diagnostics.items[0].range.start.line);
}

test "skript residual: real type aliases are kept and a snake_case type alias is reported" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const Ast = @This();
        \\const Budget = @This();
        \\const FiniteParameters = std.StaticBitSet(256);
        \\const RuntimeMap = std.HashMap(MapKey, Value, MapKey.Context, std.hash_map.default_max_load_percentage);
        \\const TypeOf = @TypeOf(0);
        \\const elf_dyn_lib = @FieldType(std.DynLib, "inner");
    ;
    var source = Source.init(allocator, "skript-type-alias.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("identifier-style", diagnostics.items[0].rule_id);
    try std.testing.expectEqual(@as(usize, 7), diagnostics.items[0].range.start.line);
}

test "skript residual: a snake_case @typeInfo value binding is accepted" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\fn intrinsicType(comptime func: anytype) void {
        \\    const func_info = @typeInfo(@TypeOf(func)).@"fn";
        \\    _ = func_info;
        \\}
    ;
    var source = Source.init(allocator, "skript-typeinfo.zig", code);
    defer source.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }

    try IdentifierStyleRule.rule.check(&source, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 0), diagnostics.items.len);
}

/// Initializer node of the first `const` named `name`, at file scope or inside a
/// function body.
fn rootConstInitIndex(tree: *const std.zig.Ast, name: []const u8) !usize {
    const tags = tree.nodes.items(.tag);
    for (tags, 0..) |tag, node_idx| {
        if (!import_resolver.isVarDeclTag(tag)) continue;
        const full = tree.fullVarDecl(@enumFromInt(node_idx)) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(full.ast.mut_token + 1), name)) continue;
        return @intFromEnum(full.ast.init_node.unwrap() orelse return error.DeclarationNotFound);
    }
    return error.DeclarationNotFound;
}

fn expectInitializerVerdict(
    code: [:0]const u8,
    name: []const u8,
    expected_invisible: bool,
) !void {
    const allocator = std.testing.allocator;
    var source = Source.init(allocator, "verdict.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const token_tags = tree.tokens.items(.tag);
    const init_idx = try rootConstInitIndex(tree, name);
    try std.testing.expectEqual(
        expected_invisible,
        IdentifierStyleRule.isInvisibleNamespaceMember(tree, tags, datas, token_tags, init_idx),
    );
}

test "isTypeInfoTypeField names the type-carrying reflection fields" {
    const is_type_info_type_field = IdentifierStyleRule.isTypeInfoTypeField;
    const type_fields = [_][]const u8{
        "child",
        "element_type",
        "error_set",
        "payload",
        "tag_type",
        "backing_integer",
        "return_type",
        "type",
    };
    for (type_fields) |field| {
        try std.testing.expect(is_type_info_type_field(field));
    }
    const value_fields = [_][]const u8{
        "fields",
        "decls",
        "layout",
        "size",
        "align",
        "value",
        "identifier",
        "name",
    };
    for (value_fields) |field| {
        try std.testing.expect(!is_type_info_type_field(field));
    }
}

test "labeledBlockLabelToken names the label a break can target" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Outer = outer: {
        \\    break :outer inner: {
        \\        break :inner error{Missing};
        \\    };
        \\};
        \\const Plain = {
        \\    break 1;
        \\};
    ;
    var source = Source.init(allocator, "blocks.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const outer_idx = try rootConstInitIndex(tree, "Outer");
    const plain_idx = try rootConstInitIndex(tree, "Plain");

    const outer_label = IdentifierStyleRule.labeledBlockLabelToken(tree, @enumFromInt(outer_idx));
    try std.testing.expect(outer_label != null);
    try std.testing.expectEqualStrings("outer", tree.tokenSlice(outer_label.?));
    try std.testing.expect(IdentifierStyleRule.labeledBlockLabelToken(tree, @enumFromInt(plain_idx)) == null);
}

test "isTypeValueLabeledBlock accepts every typed break and no value break" {
    const allocator = std.testing.allocator;
    const typed_code: [:0]const u8 =
        \\const Errors = blk: {
        \\    if (@import("std").builtin.is_test) break :blk error{Skipped};
        \\    break :blk error{Failed};
        \\};
    ;
    var typed_source = Source.init(allocator, "typed_block.zig", typed_code);
    defer typed_source.deinit();
    const typed_tree = try typed_source.ast();
    const typed_tags = typed_tree.nodes.items(.tag);
    const typed_datas = typed_tree.nodes.items(.data);
    const typed_main_tokens = typed_tree.nodes.items(.main_token);
    const typed_token_tags = typed_tree.tokens.items(.tag);
    const typed_init = try rootConstInitIndex(typed_tree, "Errors");
    try std.testing.expect(IdentifierStyleRule.isTypeValueLabeledBlock(
        typed_tree,
        typed_tags,
        typed_datas,
        typed_main_tokens,
        typed_token_tags,
        typed_init,
        IdentifierStyleRule.type_value_hops,
    ));

    const value_code: [:0]const u8 =
        \\const limit = blk: {
        \\    if (true) break :blk 1;
        \\    break :blk 2;
        \\};
    ;
    var value_source = Source.init(allocator, "value_block.zig", value_code);
    defer value_source.deinit();
    const value_tree = try value_source.ast();
    const value_tags = value_tree.nodes.items(.tag);
    const value_datas = value_tree.nodes.items(.data);
    const value_main_tokens = value_tree.nodes.items(.main_token);
    const value_token_tags = value_tree.tokens.items(.tag);
    const value_init = try rootConstInitIndex(value_tree, "limit");
    try std.testing.expect(!IdentifierStyleRule.isTypeValueLabeledBlock(
        value_tree,
        value_tags,
        value_datas,
        value_main_tokens,
        value_token_tags,
        value_init,
        IdentifierStyleRule.type_value_hops,
    ));
}

test "a break names the block it reaches, not every block of that name" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Outer = outer: {
        \\    break :outer u8;
        \\};
        \\const Inner = blk: {
        \\    break :blk blk: {
        \\        break :blk error{Missing};
        \\    };
        \\};
        \\const Mixed = blk: {
        \\    break :blk error{Missing};
        \\    break :blk 1;
        \\};
        \\const Wrong = blk: {
        \\    break :outer u8;
        \\    break :blk 1;
        \\};
        \\const Falls = blk: {
        \\    break :blk u8;
        \\    unreachable;
        \\};
    ;
    var source = Source.init(allocator, "label_scope.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    try std.testing.expect(try resolvedInitIsTypeValueFor(tree, "Outer"));
    try std.testing.expect(try resolvedInitIsTypeValueFor(tree, "Inner"));
    // A block that also yields a plain number is a value, whichever of its
    // breaks a reader would stop at.
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "Mixed")));
    // A break under another name leaves another block, so it proves nothing
    // about this one.
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "Wrong")));
    // A body that can run off its end makes the label `void`.
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "Falls")));
}

test "an alias cycle between labeled blocks proves no type" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const First = blk: {
        \\    break :blk Second;
        \\};
        \\const Second = blk: {
        \\    break :blk First;
        \\};
        \\const Chosen = blk: {
        \\    break :blk First;
        \\};
    ;
    var source = Source.init(allocator, "alias_cycle.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "First")));
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "Second")));
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "Chosen")));
}

test "an alias cycle through a conditional branch proves no type" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const builtin = @import("builtin");
        \\const win = struct {
        \\    pub const HMODULE = if (builtin.os.tag == .windows) win.HMODULE else void;
        \\};
        \\const Cycle = if (builtin.os.tag == .windows) win.HMODULE else u8;
    ;
    var source = Source.init(allocator, "conditional_cycle.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "Cycle")));
}

test "a resolved alias of a fieldless namespace stays a value" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const defaults = struct {
        \\    pub const timeout_ms: u32 = 100;
        \\};
        \\const config = defaults;
        \\const settings = struct {
        \\    timeout_ms: u32,
        \\};
        \\const Config = settings;
    ;
    var source = Source.init(allocator, "namespace_alias.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "config")));
    try std.testing.expect(try resolvedInitIsTypeValueFor(tree, "Config"));
}

test "a member of another file's namespace has no resolved verdict" {
    const code: [:0]const u8 =
        \\const kit = @import("kit.zig").kit;
        \\const Chord = kit.chord;
        \\const Vertex = kit.vertex;
    ;
    try expectInitializerVerdict(code, "Chord", true);
    try expectInitializerVerdict(code, "Vertex", true);
}

test "the standard library keeps a diagnosable member verdict" {
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const fs = std.fs;
        \\const Mem = std.mem;
    ;
    try expectInitializerVerdict(code, "fs", false);
    try expectInitializerVerdict(code, "Mem", false);
}

test "a namespace member resolves to the declaration that defines it" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Posix = struct {
        \\    pub const fd_t = u32;
        \\    pub const limit = 4096;
        \\};
        \\const Fd = Posix.fd_t;
        \\const Limit = Posix.limit;
        \\const Element = @typeInfo([]u8).pointer.child;
        \\const Count = @sizeOf(u32);
    ;
    var source = Source.init(allocator, "members.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    try std.testing.expect(try resolvedInitIsTypeValueFor(tree, "Fd"));
    try std.testing.expect(try resolvedInitIsTypeValueFor(tree, "Element"));
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "Limit")));
    try std.testing.expect(!(try resolvedInitIsTypeValueFor(tree, "Count")));
}

fn resolvedInitIsTypeValueFor(tree: *const std.zig.Ast, name: []const u8) !bool {
    return IdentifierStyleRule.resolvedInitIsTypeValue(
        tree,
        tree.nodes.items(.tag),
        tree.nodes.items(.data),
        tree.nodes.items(.main_token),
        tree.tokens.items(.tag),
        try rootConstInitIndex(tree, name),
        IdentifierStyleRule.type_value_hops,
    );
}

test "an uppercase flag member is a value rather than a type" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const Mode = packed struct {
        \\    NONBLOCK: bool = false,
        \\    RDONLY: bool = true,
        \\};
        \\fn wantsNonBlocking(flags: Mode) bool {
        \\    const nonblocking = flags.NONBLOCK;
        \\    return nonblocking;
        \\}
    ;
    var source = Source.init(allocator, "flags.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const token_tags = tree.tokens.items(.tag);
    var flag_field_access: ?usize = null;
    for (tags, 0..) |tag, node_idx| {
        if (tag != .field_access) continue;
        const field_token = datas[node_idx].node_and_token[1];
        if (field_token >= token_tags.len or token_tags[field_token] != .identifier) continue;
        if (!std.mem.eql(u8, tree.tokenSlice(field_token), "NONBLOCK")) continue;
        flag_field_access = node_idx;
        break;
    }
    try std.testing.expect(flag_field_access != null);
    try std.testing.expect(!IdentifierStyleRule.isTypeAliasCallee(
        tree,
        tags,
        datas,
        token_tags,
        flag_field_access.?,
    ));
}

test "a standard base64 codec member is a value rather than a type" {
    const allocator = std.testing.allocator;
    const code: [:0]const u8 =
        \\const std = @import("std");
        \\const decoder = std.base64.standard.Decoder;
        \\const encoder = std.base64.standard.Encoder;
        \\const shadow = struct {
        \\    pub const standard = struct {
        \\        pub const Decoder = u8;
        \\    };
        \\};
        \\const local = shadow.standard.Decoder;
    ;
    var source = Source.init(allocator, "codec.zig", code);
    defer source.deinit();

    const tree = try source.ast();
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const token_tags = tree.tokens.items(.tag);
    try std.testing.expect(!IdentifierStyleRule.isTypeAliasCallee(
        tree,
        tags,
        datas,
        token_tags,
        try rootConstInitIndex(tree, "decoder"),
    ));
    try std.testing.expect(!IdentifierStyleRule.isTypeAliasCallee(
        tree,
        tags,
        datas,
        token_tags,
        try rootConstInitIndex(tree, "encoder"),
    ));
    // A declaration spelled the same way outside the standard library keeps
    // the type classification.
    try std.testing.expect(IdentifierStyleRule.isTypeAliasCallee(
        tree,
        tags,
        datas,
        token_tags,
        try rootConstInitIndex(tree, "local"),
    ));
}
