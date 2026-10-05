//! Conditional constructor facts for `optional-unwrap`.
//!
//! A field of a struct can be proven non-null at a use without trusting the
//! constructor's *name*: what proves it is the value every construction of
//! that type stores into the field, plus the `comptime` `bool` parameter that
//! decides whether the constructor stored a non-null one at all. The use has
//! to sit where that parameter holds the value the constructor's own guard
//! assumed, so a runtime flag with the same spelling proves nothing, and a
//! constructor whose guard is missing leaves the use unproven.
//!
//! Construction facts apply only to a closed source: no exported declaration
//! that names the container, no address of the container or of anything this
//! file cannot type, and no writes or opaque calls that can change the field.
//! A public factory, whether it builds the container itself or forwards it
//! through a private alias, a public function over the container, or an
//! untracked receiver keeps the unwrap unproven.
const lexical_index = @import("../../analysis/lexical_index.zig");
const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const call_utils = @import("../../analysis/call_utils.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
const assertions = @import("../../assertions.zig");
const TypeContext = @import("../../type_context.zig").TypeContext;
const QueryContext = @import("bindings.zig").QueryContext;
const guards = @import("guards.zig");

const capacity = 8;

/// Truth values of the `comptime` `bool` parameters visible at one point.
/// Nothing else can be decided without running the program, so a condition
/// about anything else contributes no literal — and therefore no proof.
pub const Literals = struct {
    tokens: [capacity]u32 = undefined,
    values: [capacity]bool = undefined,
    len: usize = 0,
    /// Two opposite literals for one parameter: the point cannot be reached,
    /// so no requirement may be discharged against it.
    contradiction: bool = false,

    fn add(self: *Literals, token: u32, value: bool) void {
        for (self.tokens[0..self.len], 0..) |existing, index| {
            if (existing != token) continue;
            if (self.values[index] != value) self.contradiction = true;
            return;
        }
        if (self.len == capacity) {
            self.contradiction = true;
            return;
        }
        self.tokens[self.len] = token;
        self.values[self.len] = value;
        self.len += 1;
    }

    /// Does `known` establish everything `requirement` asks for?
    fn satisfies(self: Literals, requirement: Literals) bool {
        if (self.contradiction or requirement.contradiction) return false;
        for (requirement.tokens[0..requirement.len], 0..) |token, index| {
            const want = requirement.values[index];
            var seen = false;
            for (self.tokens[0..self.len], 0..) |mine, mine_index| {
                if (mine != token) continue;
                if (self.values[mine_index] != want) return false;
                seen = true;
                break;
            }
            if (!seen) return false;
        }
        return true;
    }

    /// Does `self` add at least one literal `outer` does not already hold? A
    /// branch whose condition decides nothing at comptime cannot guard a fact,
    /// because control may equally have arrived from the other arm.
    fn addsNewLiteral(self: Literals, outer: Literals) bool {
        if (self.contradiction) return false;
        for (self.tokens[0..self.len], 0..) |token, index| {
            for (outer.tokens[0..outer.len], 0..) |known, known_index| {
                if (known != token) continue;
                if (outer.values[known_index] == self.values[index]) break;
            } else return true;
        }
        return false;
    }

    fn include(self: *Literals, other: Literals) void {
        if (other.contradiction) self.contradiction = true;
        for (other.tokens[0..other.len], 0..) |token, index| self.add(token, other.values[index]);
    }
};

/// Which parameters a constructor body has proven non-null, and the literals
/// each proof needed to hold.
const ParameterFacts = struct {
    name_tokens: [capacity]u32 = undefined,
    requirements: [capacity]Literals = undefined,
    len: usize = 0,

    fn set(self: *ParameterFacts, name_token: u32, requirement: Literals) void {
        for (self.name_tokens[0..self.len], 0..) |existing, index| {
            if (existing != name_token) continue;
            self.requirements[index] = requirement;
            return;
        }
        if (self.len == capacity) return;
        self.name_tokens[self.len] = name_token;
        self.requirements[self.len] = requirement;
        self.len += 1;
    }

    fn get(self: ParameterFacts, name_token: u32) ?Literals {
        for (self.name_tokens[0..self.len], 0..) |existing, index| {
            if (existing == name_token) return self.requirements[index];
        }
        return null;
    }
};

/// The allocator a container-exposure question may spend on remembering the
/// answers it reaches. This file's query borrows source-owned syntax and
/// builds no index of its own, so it brings no allocator of its own: the type
/// context's is the one the caller already handed this check, and a query that
/// arrived without one has nothing to borrow but the page allocator, which
/// serves a list of node ids and is freed before the question ends.
fn queryAllocator(type_context: ?*TypeContext) std.mem.Allocator {
    return if (type_context) |context| context.allocator else std.heap.page_allocator;
}

pub fn isProvenByConditionalConstruction(
    query: *const QueryContext,
    unwrap_node: u32,
    unwrapped_var: u32,
    type_context: ?*TypeContext,
    assertion_scope: *const assertions.AssertionScope,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (unwrapped_var >= tags.len or tags[unwrapped_var] != .field_access) return false;
    const field_token = tree.nodes.items(.data)[unwrapped_var].node_and_token[1];

    const fn_decl = enclosingFunction(query, unwrap_node) orelse return false;
    const receiver = @intFromEnum(tree.nodes.items(.data)[unwrapped_var].node_and_token[0]);
    if (!isReceiverOfFirstParameter(query, receiver, fn_decl)) return false;
    const container = enclosingContainer(query, fn_decl) orelse return false;

    if (tree.errors.len != 0 or !sourcePreservesField(query, container, field_token, queryAllocator(type_context))) return false;

    var required = Literals{};
    var sites: usize = 0;
    var node: u32 = 1;
    while (node < tags.len) : (node += 1) {
        const init_node = structInitAt(tags, node) orelse continue;
        // Result-location typing also constructs values in array elements,
        // grouped expressions, switch prongs, and aggregate fields. An
        // unclassified literal must not disappear from a lifetime proof.
        if (!isConstructionOf(query, init_node, container)) return false;
        sites += 1;
        const need = storedFieldRequirement(query, init_node, field_token, type_context, assertion_scope) orelse return false;
        required.include(need);
    }
    if (sites == 0 or !everyReturnIsVisible(query, container)) return false;
    return literalsAt(query, unwrap_node).satisfies(required);
}

/// A constructor cannot establish a lifetime invariant for exported or escaped
/// mutable storage. Keep this proof inside one closed source and inspect every
/// write and call, including callers and sibling methods.
fn sourcePreservesField(
    query: *const QueryContext,
    container: u32,
    field_token: u32,
    allocator: std.mem.Allocator,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    // One container, one question: every answer below is a fact about this
    // container, so a helper answered once is answered for the whole walk.
    var answered = Answered.init(allocator);
    defer answered.deinit();
    for (tree.rootDecls()) |decl| {
        const node = @intFromEnum(decl);
        if (tree.fullVarDecl(decl)) |full| {
            if (full.visib_token != null or full.extern_export_token != null) return false;
        } else {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            if (treeFnProto(tree, node, &buffer)) |proto| {
                if (proto.extern_export_inline_token) |token| {
                    if (tree.tokenTag(token) == .keyword_extern or tree.tokenTag(token) == .keyword_export) return false;
                }
                if (proto.visib_token != null) {
                    const name = proto.name_token orelse return false;
                    // `main` is handed no storage this file owns; every
                    // other exported function is a way in only when it names
                    // the container.
                    if (!std.mem.eql(u8, tree.tokenSlice(name), "main")) {
                        if (exportedDeclarationExposesContainer(query, &answered, node, container)) return false;
                        continue;
                    }
                    if (proto.ast.params.len != 0) return false;
                    var result = @intFromEnum(proto.ast.return_type);
                    if (tags[result] == .error_union) result = @intFromEnum(datas[result].node_and_node[1]);
                    if (tags[result] != .identifier or !std.mem.eql(u8, tree.tokenSlice(tree.nodes.items(.main_token)[result]), "void")) return false;
                }
            }
        }
    }
    for (tags, 0..) |tag, index| {
        const node: u32 = @intCast(index);
        switch (tag) {
            .identifier => {
                if (std.mem.eql(u8, tree.tokenSlice(tree.nodes.items(.main_token)[node]), "undefined")) return false;
            },
            .address_of => {
                // A pointer to the container, or to something this file cannot
                // type, puts a field within reach of code that may write it. A
                // pointer to a value it can type -- a function kept alive by
                // its own address -- cannot name this container at all.
                const operand = @intFromEnum(datas[node].node);
                switch (valueKind(query, operand, container, 0)) {
                    .scalar, .namespace => {},
                    .container, .unknown => return false,
                }
            },
            .@"asm", .asm_simple, .assign_destructure => return false,
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
            => {
                const lhs = @intFromEnum(datas[node].node_and_node[0]);
                if (tags[lhs] == .identifier) {
                    const name = tree.tokenSlice(tree.nodes.items(.main_token)[lhs]);
                    if (std.mem.eql(u8, name, "_")) continue;
                    if (valueKind(query, lhs, container, 0) != .scalar) return false;
                } else if (tags[lhs] == .field_access) {
                    const field = datas[lhs].node_and_token;
                    if (std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(field[1])), import_resolver.normalizeIdentifier(tree.tokenSlice(field_token)))) return false;
                    // Only a direct sibling field is disjoint. A nested place
                    // may leave the receiver through a pointer-valued field.
                    if (valueKind(query, @intFromEnum(field[0]), container, 0) != .container) return false;
                } else return false;
            },
            .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                const name = tree.tokenSlice(tree.nodes.items(.main_token)[node]);
                if (std.mem.eql(u8, name, "@import") or std.mem.eql(u8, name, "@This")) continue;
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&buffer, @enumFromInt(node)) orelse return false;
                if (!std.mem.eql(u8, name, "@as") or params.len != 2 or typeValueKind(query, @intFromEnum(params[0]), container, 0) != .scalar) return false;
            },
            .call, .call_comma, .call_one, .call_one_comma => {
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return false;
                const callee = localCallable(query, @intFromEnum(call.ast.fn_expr), container, 0);
                if (tags[@intFromEnum(call.ast.fn_expr)] == .field_access) {
                    const receiver = @intFromEnum(datas[@intFromEnum(call.ast.fn_expr)].node_and_token[0]);
                    const kind = valueKind(query, receiver, container, 0);
                    if ((kind == .container or kind == .unknown) and callee == null) return false;
                }
                for (call.ast.params) |param| {
                    const kind = valueKind(query, @intFromEnum(param), container, 0);
                    if ((kind == .container or kind == .unknown) and callee == null) return false;
                }
            },
            else => {},
        }
    }
    return true;
}

/// An exported function is a way for code outside this file to reach the
/// container only when it names it or hands one back. A public function over
/// unrelated values is handed no container, builds none, and can pass none on,
/// so its presence cannot change a field this file owns.
fn exportedDeclarationExposesContainer(
    query: *const QueryContext,
    answered: *Answered,
    fn_decl: u32,
    container: u32,
) bool {
    // The generic function that returns the container is its own factory.
    if (isFactoryFunction(query, fn_decl, container)) return true;

    const tree = query.tree;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = treeFnProto(tree, fn_decl, &buffer) orelse return true;
    // An unstated return type is taken from the body, which the scan below
    // may not see: this file does not know what such a signature hands out.
    const result_node = proto.ast.return_type.unwrap() orelse return true;
    if (typeValueKind(query, @intFromEnum(result_node), container, 0) == .container) return true;
    for (proto.ast.params) |param| {
        const written = parameterTypeNode(tree, @intFromEnum(param)) orelse return true;
        if (typeValueKind(query, written, container, 0) == .container) return true;
    }
    // What this declaration hands back is exposure on its own, and a name bound
    // to a call is a name as much as the call is: `const Alias = Iterator(true);
    // pub fn makeType() type { return Alias; }` writes the container down where a
    // scan for names that resolve to functions of this file cannot see it. The
    // walk over helpers' own results already follows such a binding, and it
    // answers this exported declaration from its own result for the same
    // reason it answers a helper: what it cannot rule out as a scalar is a way
    // out of this file.
    if (producesContainer(query, answered, fn_decl, container, null)) return true;
    return mentionsContainer(query, answered, fn_decl, container);
}

/// The names from which a value of this container can be written down inside
/// one declaration: the container declaration itself, the factory that returns
/// it, and the private helpers that forward the factory's type -- `fn Alias()
/// type { return Iterator(true); }` hands out the very container one call
/// removed. Every other name there belongs to somebody else's type.
fn mentionsContainer(query: *const QueryContext, answered: *Answered, fn_decl: u32, container: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (fn_decl >= tree.nodes.len or tags[fn_decl] != .fn_decl) return true;
    const first = tree.firstToken(@enumFromInt(fn_decl));
    const last = tree.lastToken(@enumFromInt(fn_decl));

    for (tags, 0..) |tag, index| {
        if (index == 0) continue;
        if (tag != .identifier and !call_resolver.isContainerTag(tag)) continue;
        const node: u32 = @intCast(index);
        const start = tree.firstToken(@enumFromInt(node));
        if (start < first or start > last) continue;
        if (node == container) return true;
        if (tag != .identifier) continue;
        const token = main_tokens[node];
        if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) continue;
        const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));
        const function = query.lexical.findFunction(name, token) orelse continue;
        if (producesContainer(query, answered, function, container, null)) return true;
    }
    return false;
}

/// One step of the route the walk is following right now. The record lives in
/// the frame that took the step and points at the step below it, so a route
/// extends itself without allocating anything and without being copied: each
/// function and each expression records itself in the frame it is asked
/// about. Meeting a node this same route already walked means the walk has
/// stopped describing helpers that forward a type and started describing a
/// cycle, which is not evidence about any container. Every branch records its
/// own path, so a helper reached twice by different branches is a route seen
/// twice, not a cycle.
const Route = struct {
    const Kind = enum { function, expression };

    kind: Kind,
    node: u32,
    parent: ?*const Route,
};

fn routeRepeats(outer: ?*const Route, kind: Route.Kind, node: u32) bool {
    var step = outer;
    while (step) |current| : (step = current.parent) {
        if (current.kind == kind and current.node == node) return true;
    }
    return false;
}

/// The helpers one container-exposure question has already finished at
/// `false`, so that a helper reached along many paths is walked once.
///
/// A helper's answer does not depend on the arguments it was called with: this
/// walk reads the helper's own signature and its own return expressions and
/// resolves callees by name inside the file. The route a helper is reached by
/// changes only where a cycle stops the walk, and a stopped walk answers `true`
/// rather than `false`, so an answer kept here is the same on every path. Only
/// `false` is kept: a `true` either is evidence or is the walk declining to
/// answer, and both end the question that asked, so neither is reusable.
///
/// The inline table covers every source in practice without allocating. Past it
/// the same list continues in memory the question's allocator owns; a list
/// that cannot grow is not a smaller answer, only a longer walk, so a failed
/// growth keeps what fits and grants nothing.
const Answered = struct {
    const inline_capacity = 16;

    allocator: std.mem.Allocator,
    fixed: [inline_capacity]u32 = undefined,
    len: usize = 0,
    /// The inline table continued, kept ascending so a lookup halves.
    spilled: std.ArrayList(u32) = .empty,

    fn init(allocator: std.mem.Allocator) Answered {
        return .{ .allocator = allocator };
    }

    fn deinit(self: *Answered) void {
        self.spilled.deinit(self.allocator);
    }

    /// Has `function` already been walked all the way to `false`?
    fn holds(self: *const Answered, function: u32) bool {
        for (self.fixed[0..self.len]) |answered| {
            if (answered == function) return true;
        }
        const at = insertion(self.spilled.items, function);
        return at < self.spilled.items.len and self.spilled.items[at] == function;
    }

    fn record(self: *Answered, function: u32) void {
        if (self.len < inline_capacity) {
            self.fixed[self.len] = function;
            self.len += 1;
            return;
        }
        const at = insertion(self.spilled.items, function);
        if (at < self.spilled.items.len and self.spilled.items[at] == function) return;
        self.spilled.insert(self.allocator, at, function) catch return;
    }
};

/// Where `function` sits in an ascending list of answered helpers, or where it
/// would sit.
fn insertion(sorted: []const u32, function: u32) usize {
    var low: usize = 0;
    var high = sorted.len;
    while (low < high) {
        const middle = low + (high - low) / 2;
        if (sorted[middle] < function) low = middle + 1 else high = middle;
    }
    return low;
}

/// Can calling `function` hand a value of the container back to whoever called
/// it? The generic factory that builds the container is one such route, and so
/// is a helper of this file that declares the container as its result or
/// forwards a call to another such helper. Only functions this file declares
/// are followed, and only for as long as the route stays a route: a function
/// this route has already walked is a cycle, and a cycle -- like any other
/// unanswerable question about an exported declaration -- is a way out of this
/// file.
///
/// `answered` is what makes this a walk rather than a reenumeration of paths:
/// a helper already finished at `false` answers `false` again for every later
/// path to it, and a helper that hands the container back ends the question
/// before any of that matters.
fn producesContainer(
    query: *const QueryContext,
    answered: *Answered,
    function: u32,
    container: u32,
    outer: ?*const Route,
) bool {
    // A helper this question already walked all the way to `false` answers
    // `false` for every later path to it. Such an answer is the same on every
    // path: the walk read the helper's own signature and its own return
    // expressions and never its arguments, and it resolved nothing as
    // unknown, or it would have answered `true` and never been recorded. A
    // factory answers `true` before it can be recorded at all, so this can
    // stand ahead of the factory check without hiding one.
    if (answered.holds(function)) return false;
    if (isFactoryFunction(query, function, container)) return true;
    const tree = query.tree;
    if (function >= tree.nodes.len) return true;

    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = treeFnProto(tree, function, &buffer) orelse return true;
    const declared: ValueKind = if (proto.ast.return_type.unwrap()) |written|
        typeValueKind(query, @intFromEnum(written), container, 0)
    else
        .scalar;
    if (declared == .container) return true;
    if (declared == .scalar) return false;

    if (routeRepeats(outer, .function, function)) return true;
    const route = Route{ .kind = .function, .node = function, .parent = outer };

    // A resolved callee is a prototype, and a prototype's own tokens stop at
    // the end of its signature. What the function hands back is written in
    // the declaration that owns it, so the walk reads that declaration: read
    // the prototype instead, it finds no `return` at all, every helper answers
    // `false`, and the answer this question remembers is that a factory
    // reached through a private alias cannot be reached at all.
    const declaration = declaringFunction(query, function) orelse return true;
    const tags = tree.nodes.items(.tag);
    const first = tree.firstToken(@enumFromInt(declaration));
    const last = tree.lastToken(@enumFromInt(declaration));
    for (tags, 0..) |tag, index| {
        if (tag != .@"return") continue;
        const node: u32 = @intCast(index);
        const start = tree.firstToken(@enumFromInt(node));
        if (start < first or start > last) continue;
        const value = tree.nodes.items(.data)[node].opt_node.unwrap() orelse continue;
        if (returnedValueIsContainer(query, answered, @intFromEnum(value), container, &route)) return true;
    }
    answered.record(function);
    return false;
}

/// Does `expression` evaluate to the container? Only helpers whose own
/// signature this file has not already ruled out as a scalar reach here, so
/// no shape below has to be closed again by that signature and every shape
/// this walk cannot name a type for stays open. The shapes that do name a type
/// are followed: a call to a function of this file, a name bound to such a
/// call, a branch, an unwrapped optional, and `@TypeOf` of anything of those.
fn returnedValueIsContainer(
    query: *const QueryContext,
    answered: *Answered,
    expression: u32,
    container: u32,
    outer: ?*const Route,
) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (expression == 0 or expression >= tree.nodes.len) return true;
    if (routeRepeats(outer, .expression, expression)) return true;
    const route = Route{ .kind = .expression, .node = expression, .parent = outer };

    switch (tags[expression]) {
        .number_literal,
        .char_literal,
        .string_literal,
        .multiline_string_literal,
        .enum_literal,
        .equal_equal,
        .bang_equal,
        .less_than,
        .less_or_equal,
        .greater_than,
        .greater_or_equal,
        .bool_and,
        .bool_or,
        .bool_not,
        .struct_init,
        .struct_init_comma,
        .struct_init_one,
        .struct_init_one_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        .array_init,
        .array_init_comma,
        .array_init_one,
        .array_init_one_comma,
        .array_init_dot,
        .array_init_dot_comma,
        .array_init_dot_two,
        .array_init_dot_two_comma,
        => return false,

        .grouped_expression => return returnedValueIsContainer(
            query,
            answered,
            @intFromEnum(datas[expression].node_and_token[0]),
            container,
            &route,
        ),
        .@"comptime", .@"try" => return returnedValueIsContainer(
            query,
            answered,
            @intFromEnum(datas[expression].node),
            container,
            &route,
        ),

        .unwrap_optional => {
            // `?T` unwraps to `T`, so an optional of the container hands back
            // a container and its operand decides.
            return returnedValueIsContainer(
                query,
                answered,
                @intFromEnum(datas[expression].node_and_token[0]),
                container,
                &route,
            );
        },

        .@"orelse", .@"catch" => {
            inline for (datas[expression].node_and_node) |operand| {
                if (returnedValueIsContainer(query, answered, @intFromEnum(operand), container, &route)) return true;
            }
            return false;
        },

        .@"if", .if_simple => {
            const full = tree.fullIf(@enumFromInt(expression)) orelse return true;
            const then_expr = branchValue(tree, @intFromEnum(full.ast.then_expr)) orelse return true;
            if (returnedValueIsContainer(query, answered, then_expr, container, &route)) return true;
            const else_node = full.ast.else_expr.unwrap() orelse return true;
            const else_expr = branchValue(tree, @intFromEnum(else_node)) orelse return true;
            return returnedValueIsContainer(query, answered, else_expr, container, &route);
        },

        .call, .call_comma, .call_one, .call_one_comma => {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, @enumFromInt(expression)) orelse return true;
            // A callee this file cannot resolve hands back whatever that callee
            // returns, which is a type this file cannot type.
            const callee = localCallable(query, @intFromEnum(call.ast.fn_expr), container, 0) orelse return true;
            return producesContainer(query, answered, callee, container, &route);
        },

        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            const name = tree.tokenSlice(tree.nodes.items(.main_token)[expression]);
            if (!std.mem.eql(u8, name, "@TypeOf")) return true;
            var buffer: [2]std.zig.Ast.Node.Index = undefined;
            const params = tree.builtinCallParams(&buffer, @enumFromInt(expression)) orelse return true;
            if (params.len != 1) return true;
            return returnedValueIsContainer(query, answered, @intFromEnum(params[0]), container, &route);
        },

        .field_access => {
            // A member of a namespace names a declaration and a member of a
            // value is one, but which member it is cannot be read from the
            // shape, and this walk is only reached by a helper whose own
            // result it has not already ruled out as a scalar. So there is no
            // helper signature left to close this shape with and it stays
            // open, exactly as it did when the signature was consulted here.
            return true;
        },

        .identifier => {
            const token = tree.nodes.items(.main_token)[expression];
            if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return true;
            const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));
            if (query.lexical.findFunction(name, token)) |function| {
                return producesContainer(query, answered, function, container, &route);
            }
            const candidate = bindingOf(query, expression) orelse return true;
            if (candidate.kind != .variable) return true;
            const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return true;
            // A written type settles the binding in only two ways: naming the
            // container is the container, and a proven scalar can never become
            // one. Every other spelling -- `type`, `?Container`, a name this
            // file cannot resolve -- leaves the initializer in charge, so
            // `const Alias: type = makeType();` still follows `makeType()`,
            // and a written type this walk cannot follow at all stays open.
            if (full.ast.type_node.unwrap()) |written| {
                const written_kind = typeValueKind(query, @intFromEnum(written), container, 0);
                if (written_kind == .container) return true;
                if (written_kind == .scalar) return false;
            }
            const init = full.ast.init_node.unwrap() orelse return true;
            return returnedValueIsContainer(query, answered, @intFromEnum(init), container, &route);
        },

        else => return true,
    }
}

/// The value an `if` arm produces when the `if` is used as an expression: the
/// parser wraps a bare arm in a block, and the wrapper is not part of the value.
fn branchValue(tree: *const std.zig.Ast, node: u32) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (node == 0 or node >= tree.nodes.len) return null;
    switch (tags[node]) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => {
            var buffer: [2]u32 = undefined;
            const statements = ast_walk.getBlockStatements(tree, node, &buffer) orelse return null;
            if (statements.len != 1) return null;
            return statements[0];
        },
        else => return node,
    }
}

const ValueKind = enum { scalar, container, namespace, unknown };

fn scalarTypeName(name: []const u8) bool {
    for ([_][]const u8{ "bool", "void", "noreturn", "usize", "isize", "comptime_int", "comptime_float", "f16", "f32", "f64", "f80", "f128" }) |scalar| {
        if (std.mem.eql(u8, name, scalar)) return true;
    }
    if (name.len < 2 or (name[0] != 'i' and name[0] != 'u')) return false;
    for (name[1..]) |digit| if (digit < '0' or digit > '9') return false;
    return true;
}

fn typeValueKind(query: *const QueryContext, node: u32, container: u32, depth: u32) ValueKind {
    const tree = query.tree;
    if (node == 0 or node >= tree.nodes.len or depth >= 64) return .unknown;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (denotesContainer(query, node, container)) return .container;
    switch (tags[node]) {
        .identifier => {
            const name = tree.tokenSlice(tree.nodes.items(.main_token)[node]);
            return if (scalarTypeName(name)) .scalar else .unknown;
        },
        .optional_type => return typeValueKind(query, @intFromEnum(datas[node].node), container, depth + 1),
        .error_union => return typeValueKind(query, @intFromEnum(datas[node].node_and_node[1]), container, depth + 1),
        .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
            const pointer = tree.fullPtrType(@enumFromInt(node)) orelse return .unknown;
            return typeValueKind(query, @intFromEnum(pointer.ast.child_type), container, depth + 1);
        },
        else => return .unknown,
    }
}

fn valueKind(query: *const QueryContext, node: u32, container: u32, depth: u32) ValueKind {
    const tree = query.tree;
    if (node == 0 or node >= tree.nodes.len or depth >= 64) return .unknown;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    switch (tags[node]) {
        .number_literal,
        .char_literal,
        .string_literal,
        .multiline_string_literal,
        .enum_literal,
        .equal_equal,
        .bang_equal,
        .less_than,
        .less_or_equal,
        .greater_than,
        .greater_or_equal,
        .bool_and,
        .bool_or,
        .bool_not,
        => return .scalar,
        .identifier => {
            const token = tree.nodes.items(.main_token)[node];
            const name = tree.tokenSlice(token);
            if (scalarTypeName(name) or std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false") or std.mem.eql(u8, name, "null")) return .scalar;
            if (denotesContainer(query, node, container)) return .container;
            if (query.lexical.findFunction(import_resolver.normalizeIdentifier(name), token)) |function| {
                if (isFactoryFunction(query, function, container)) return .container;
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const proto = treeFnProto(tree, function, &buffer) orelse return .unknown;
                if (typeValueKind(query, @intFromEnum(proto.ast.return_type), container, depth + 1) != .scalar) return .unknown;
                for (proto.ast.params) |param| {
                    const written = parameterTypeNode(tree, @intFromEnum(param)) orelse return .unknown;
                    if (typeValueKind(query, written, container, depth + 1) != .scalar) return .unknown;
                }
                return .scalar;
            }
            const candidate = bindingOf(query, node) orelse return .unknown;
            if (candidate.kind == .parameter) {
                const param_type = parameterTypeNode(tree, candidate.node) orelse return .unknown;
                return typeValueKind(query, param_type, container, depth + 1);
            }
            const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return .unknown;
            if (full.ast.type_node.unwrap()) |written| return typeValueKind(query, @intFromEnum(written), container, depth + 1);
            const init = full.ast.init_node.unwrap() orelse return .unknown;
            return valueKind(query, @intFromEnum(init), container, depth + 1);
        },
        .field_access => {
            const field = datas[node].node_and_token;
            const base = valueKind(query, @intFromEnum(field[0]), container, depth + 1);
            return if (base == .namespace) .namespace else .unknown;
        },
        .array_access => {
            // An element read out of an array is a value of that array's
            // element type, so the container is only in reach through an
            // array of containers. This file reads the element type through
            // the same analysis it reads every other type reference with, and
            // a base whose type it cannot name proves nothing either way.
            const element = arrayElementType(query, @intFromEnum(datas[node].node_and_node[0]), container, depth + 1) orelse return .unknown;
            return typeValueKind(query, element, container, depth + 1);
        },
        .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
            const name = tree.tokenSlice(tree.nodes.items(.main_token)[node]);
            if (std.mem.eql(u8, name, "@import")) return .namespace;
            if (std.mem.eql(u8, name, "@This")) return .container;
            if (std.mem.eql(u8, name, "@as")) {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&buffer, @enumFromInt(node)) orelse return .unknown;
                if (params.len != 2) return .unknown;
                return typeValueKind(query, @intFromEnum(params[0]), container, depth + 1);
            }
            return .unknown;
        },
        .call, .call_comma, .call_one, .call_one_comma => {
            var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return .unknown;
            const function = localCallable(query, @intFromEnum(call.ast.fn_expr), container, depth + 1) orelse return .unknown;
            if (isFactoryFunction(query, function, container)) return .container;
            var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
            const proto = treeFnProto(tree, function, &proto_buffer) orelse return .unknown;
            return typeValueKind(query, @intFromEnum(proto.ast.return_type), container, depth + 1);
        },
        .grouped_expression => return valueKind(query, @intFromEnum(datas[node].node_and_token[0]), container, depth + 1),
        .@"comptime", .@"try" => return valueKind(query, @intFromEnum(datas[node].node), container, depth + 1),
        .unwrap_optional => return valueKind(query, @intFromEnum(datas[node].node_and_token[0]), container, depth + 1),
        else => return .unknown,
    }
}

/// The element type of the array a value is a value of, when this file can
/// name that type: the written type of the binding it is read through, or the
/// result type of the call that binding is initialized from. Null when the
/// value is not an array, or when the type it has cannot be read here.
fn arrayElementType(query: *const QueryContext, node: u32, container: u32, depth: u32) ?u32 {
    const tree = query.tree;
    if (node == 0 or node >= tree.nodes.len or depth >= 64) return null;
    const tags = tree.nodes.items(.tag);
    switch (tags[node]) {
        .identifier => {
            const candidate = bindingOf(query, node) orelse return null;
            if (candidate.kind != .variable) return null;
            const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return null;
            if (full.ast.type_node.unwrap()) |written| return arrayElementTypeNode(tree, @intFromEnum(written));
            const init = full.ast.init_node.unwrap() orelse return null;
            return arrayElementType(query, @intFromEnum(init), container, depth + 1);
        },
        .call, .call_comma, .call_one, .call_one_comma => {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return null;
            const function = localCallable(query, @intFromEnum(call.ast.fn_expr), container, depth + 1) orelse return null;
            var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
            const proto = treeFnProto(tree, function, &proto_buffer) orelse return null;
            const result = proto.ast.return_type.unwrap() orelse return null;
            return arrayElementTypeNode(tree, @intFromEnum(result));
        },
        else => return null,
    }
}

/// The element type expression of an array type.
fn arrayElementTypeNode(tree: *const std.zig.Ast, type_node: u32) ?u32 {
    if (type_node >= tree.nodes.len) return null;
    const tags = tree.nodes.items(.tag);
    switch (tags[type_node]) {
        .array_type, .array_type_sentinel => {},
        else => return null,
    }
    const array = tree.fullArrayType(@enumFromInt(type_node)) orelse return null;
    const element = @intFromEnum(array.ast.elem_type);
    return if (element >= tree.nodes.len) null else element;
}

pub fn localCallable(query: *const QueryContext, expr: u32, container: u32, depth: u32) ?u32 {
    const tree = query.tree;
    if (expr == 0 or expr >= tree.nodes.len or depth >= 64) return null;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (tags[expr] == .identifier) {
        const token = tree.nodes.items(.main_token)[expr];
        return query.lexical.findFunction(import_resolver.normalizeIdentifier(tree.tokenSlice(token)), token);
    }
    if (tags[expr] != .field_access) return null;
    const field = datas[expr].node_and_token;
    if (valueKind(query, @intFromEnum(field[0]), container, depth + 1) != .container) return null;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(field[1]));
    for (query.lexical.namedCandidates(name)) |candidate| {
        if (candidate.kind == .function and enclosingContainer(query, candidate.node) == container) return candidate.node;
    }
    return null;
}

fn isFactoryFunction(query: *const QueryContext, function: u32, container: u32) bool {
    const factory = enclosingFunction(query, container) orelse return false;
    var left_buffer: [1]std.zig.Ast.Node.Index = undefined;
    var right_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const left = treeFnProto(query.tree, function, &left_buffer) orelse return false;
    const right = treeFnProto(query.tree, factory, &right_buffer) orelse return false;
    return left.ast.fn_token == right.ast.fn_token;
}

// ---------------------------------------------------------------------------
// Construction sites
// ---------------------------------------------------------------------------

pub fn structInitAt(tags: []const std.zig.Ast.Node.Tag, node: u32) ?u32 {
    return switch (tags[node]) {
        .struct_init,
        .struct_init_comma,
        .struct_init_one,
        .struct_init_one_comma,
        .struct_init_dot_two,
        .struct_init_dot_two_comma,
        .struct_init_dot,
        .struct_init_dot_comma,
        => node,
        else => null,
    };
}

/// Is this struct literal a value of `container`? It is one when it is written
/// with the container's type, when it is what a constructor-shaped function
/// returns, or when it initializes a binding of that type.
fn isConstructionOf(query: *const QueryContext, init_node: u32, container: u32) bool {
    const tree = query.tree;
    var buffer: [2]std.zig.Ast.Node.Index = undefined;
    const init = tree.fullStructInit(&buffer, @enumFromInt(init_node)) orelse return false;
    if (init.ast.type_expr.unwrap()) |type_node| {
        return denotesContainer(query, @intFromEnum(type_node), container);
    }
    const parent = query.lexical.parent(init_node) orelse return false;
    const tags = tree.nodes.items(.tag);
    if (parent >= tags.len) return false;
    switch (tags[parent]) {
        .@"return" => {
            const owner = enclosingFunction(query, parent) orelse return false;
            return functionReturnsContainer(query, owner, container);
        },
        .simple_var_decl, .local_var_decl, .aligned_var_decl, .global_var_decl => {
            const full = tree.fullVarDecl(@enumFromInt(parent)) orelse return false;
            const type_node = full.ast.type_node.unwrap() orelse return false;
            return denotesContainer(query, @intFromEnum(type_node), container);
        },
        else => return false,
    }
}

fn functionReturnsContainer(query: *const QueryContext, fn_decl: u32, container: u32) bool {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = treeFnProto(query.tree, fn_decl, &buffer) orelse return false;
    const return_type = proto.ast.return_type.unwrap() orelse return false;
    return denotesContainer(query, @intFromEnum(return_type), container);
}

/// Every `return` of a constructor-shaped function must hand back one of the
/// struct literals this file contains; otherwise the value's origin is
/// unaccounted for and nothing downstream may be proven from it.
fn everyReturnIsVisible(query: *const QueryContext, container: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    var node: u32 = 1;
    while (node < tags.len) : (node += 1) {
        if (tags[node] != .@"return") continue;
        const owner = enclosingFunction(query, node) orelse continue;
        if (!functionReturnsContainer(query, owner, container)) continue;
        const value = tree.nodes.items(.data)[node].opt_node.unwrap() orelse continue;
        const init_node = structInitAt(tags, @intFromEnum(value)) orelse return false;
        if (!isConstructionOf(query, init_node, container)) return false;
    }
    return true;
}

/// The literals under which `init_node` stores a non-null value in
/// `field_token`.
fn storedFieldRequirement(
    query: *const QueryContext,
    init_node: u32,
    field_token: u32,
    type_context: ?*TypeContext,
    assertion_scope: *const assertions.AssertionScope,
) ?Literals {
    const tree = query.tree;
    var buffer: [2]std.zig.Ast.Node.Index = undefined;
    const init = tree.fullStructInit(&buffer, @enumFromInt(init_node)) orelse return null;

    // The initializer's field name and the access's field name are different
    // tokens in different places, so they are matched by spelling; which
    // field of which type is decided by `container`, never by the name alone.
    const wanted = tree.tokenSlice(field_token);
    for (init.ast.fields) |value_node| {
        const name_token = structInitFieldNameToken(tree, value_node) orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), wanted)) continue;
        return valueRequirement(query, @intFromEnum(value_node), type_context, assertion_scope);
    }
    // The field is not stored here. Whether the declaration carries a default
    // is deliberately not read here, so an omitted field proves nothing.
    return null;
}

fn valueRequirement(
    query: *const QueryContext,
    value_node: u32,
    type_context: ?*TypeContext,
    assertion_scope: *const assertions.AssertionScope,
) ?Literals {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (value_node >= tags.len) return null;
    if (guards.isDefinitelyNonNullExpression(
        tree,
        value_node,
        type_context,
        tags,
        tree.nodes.items(.data),
    )) return Literals{};

    // Only a parameter carries a fact forward: a `var` local can be written
    // between the constructor's guard and the field it stores, a parameter
    // cannot.
    const name_token = parameterNameToken(query, value_node) orelse return null;
    const owner = enclosingFunction(query, value_node) orelse return null;
    var facts = ParameterFacts{};
    scanParameterFacts(query, owner, assertion_scope, Literals{}, &facts);
    return facts.get(name_token);
}

// ---------------------------------------------------------------------------
// Conditional parameter facts inside a constructor
// ---------------------------------------------------------------------------

fn scanParameterFacts(
    query: *const QueryContext,
    fn_decl: u32,
    assertion_scope: *const assertions.AssertionScope,
    outer: Literals,
    facts: *ParameterFacts,
) void {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (fn_decl >= tags.len or tags[fn_decl] != .fn_decl) return;
    const body = @intFromEnum(tree.nodes.items(.data)[fn_decl].node_and_node[1]);
    if (body == 0 or body >= tree.nodes.len) return;
    scanStatementList(query, body, assertion_scope, outer, facts);
}

fn scanStatementList(
    query: *const QueryContext,
    block: u32,
    assertion_scope: *const assertions.AssertionScope,
    outer: Literals,
    facts: *ParameterFacts,
) void {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    var inline_statements: [2]u32 = undefined;
    const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse return;

    for (statements) |statement| {
        if (statement >= tags.len) continue;
        switch (tags[statement]) {
            // The value this function hands back is what the caller stores;
            // nothing after it can describe that value.
            .@"return" => return,
            .@"if", .if_simple => {
                const full = tree.fullIf(@enumFromInt(statement)) orelse continue;
                const cond = @intFromEnum(full.ast.cond_expr);

                var then_literals = outer;
                collectLiterals(&then_literals, query, cond, true);
                if (then_literals.addsNewLiteral(outer)) {
                    scanBranch(
                        query,
                        @intFromEnum(full.ast.then_expr),
                        assertion_scope,
                        then_literals,
                        facts,
                    );
                }

                const else_node = full.ast.else_expr.unwrap() orelse continue;
                var else_literals = outer;
                collectLiterals(&else_literals, query, cond, false);
                if (else_literals.addsNewLiteral(outer)) {
                    scanBranch(
                        query,
                        @intFromEnum(else_node),
                        assertion_scope,
                        else_literals,
                        facts,
                    );
                }
            },
            // A loop body may run zero times and a `defer` body runs when its
            // scope leaves, so neither can establish a fact about the value
            // this function returns.
            else => {},
        }
        recordAssertion(query, statement, assertion_scope, outer, facts);
    }
}

fn scanBranch(
    query: *const QueryContext,
    branch: u32,
    assertion_scope: *const assertions.AssertionScope,
    literals: Literals,
    facts: *ParameterFacts,
) void {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (branch >= tags.len) return;
    switch (tags[branch]) {
        .block, .block_semicolon, .block_two, .block_two_semicolon => {
            scanStatementList(query, branch, assertion_scope, literals, facts);
        },
        else => recordAssertion(query, branch, assertion_scope, literals, facts),
    }
}

fn recordAssertion(
    query: *const QueryContext,
    statement: u32,
    assertion_scope: *const assertions.AssertionScope,
    literals: Literals,
    facts: *ParameterFacts,
) void {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (statement >= tags.len) return;

    const is_try = tags[statement] == .@"try";
    const call_node = if (is_try) @intFromEnum(datas[statement].node) else statement;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&buffer, @enumFromInt(call_node)) orelse return;
    if (call.ast.params.len != 1) return;

    // The callee is resolved to the very declaration the alias registered, so
    // a user function named `assert` cannot carry the proof.
    const name = assertions.resolveDebugAssertionName(
        tree,
        call.ast.fn_expr,
        assertion_scope,
        query.lexical,
    ) orelse (if (is_try)
        assertions.resolveAssertionName(tree, call.ast.fn_expr, assertion_scope) orelse return
    else
        return);
    if (assertions.constraintKindForName(name) != .boolean) return;

    const condition = @intFromEnum(call.ast.params[0]);
    const proven = conditionProvesParameterNonNull(query, condition) orelse return;
    facts.set(proven, literals);
}

/// The parameter a `x != null` style assertion names, resolved by declaration
/// rather than by spelling.
fn conditionProvesParameterNonNull(query: *const QueryContext, condition: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    if (condition >= tags.len) return null;

    switch (tags[condition]) {
        .grouped_expression => return conditionProvesParameterNonNull(
            query,
            @intFromEnum(datas[condition].node_and_token[0]),
        ),
        .bool_and => {
            const lhs = conditionProvesParameterNonNull(
                query,
                @intFromEnum(datas[condition].node_and_node[0]),
            ) orelse return null;
            const rhs = conditionProvesParameterNonNull(
                query,
                @intFromEnum(datas[condition].node_and_node[1]),
            ) orelse return null;
            return if (lhs == rhs) lhs else null;
        },
        .bang_equal => {
            const lhs = @intFromEnum(datas[condition].node_and_node[0]);
            const rhs = @intFromEnum(datas[condition].node_and_node[1]);
            if (!isNullLiteral(tree, rhs)) return null;
            if (lhs >= tree.nodes.len or tags[lhs] != .identifier) return null;
            return parameterNameToken(query, lhs);
        },
        else => return null,
    }
}

/// The declaration token of the `comptime` `bool` parameter this reference
/// names, or null when the reference is a runtime value spelled the same way.
fn comptimeBoolParameterToken(query: *const QueryContext, ident_node: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    const candidate = bindingOf(query, ident_node) orelse return null;
    if (candidate.kind != .parameter) return null;
    // `comptime` sits directly before the parameter's declared name.
    if (candidate.name_token == 0) return null;
    if (tree.tokenTag(candidate.name_token - 1) != .keyword_comptime) return null;

    // The declared type must be exactly `bool`: a runtime flag spelled the
    // same way decides nothing before the program runs.
    const type_node = parameterTypeNode(tree, candidate.node) orelse return null;
    if (type_node >= tags.len or tags[type_node] != .identifier) return null;
    const type_token = main_tokens[type_node];
    if (type_token >= tree.tokens.len or tree.tokenTag(type_token) != .identifier) return null;
    if (!std.mem.eql(u8, tree.tokenSlice(type_token), "bool")) return null;
    return candidate.name_token;
}

// ---------------------------------------------------------------------------
// comptime bool literals
// ---------------------------------------------------------------------------

/// The literals that hold at `at_node`: the branch conditions the point sits
/// in, plus the guards of earlier `if`s whose arm already left the scope.
fn literalsAt(query: *const QueryContext, at_node: u32) Literals {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);
    var result = Literals{};

    var node = at_node;
    var depth: u32 = 0;
    while (depth < 64) : (depth += 1) {
        const parent = query.lexical.parent(node) orelse break;
        if (parent == 0 or parent >= tags.len) break;
        switch (tags[parent]) {
            .@"if", .if_simple => {
                const full = tree.fullIf(@enumFromInt(parent)) orelse break;
                const cond = @intFromEnum(full.ast.cond_expr);
                const then_expr = @intFromEnum(full.ast.then_expr);
                if (containsNode(tree, then_expr, at_node)) {
                    collectLiterals(&result, query, cond, true);
                } else if (full.ast.else_expr.unwrap()) |else_node| {
                    if (containsNode(tree, @intFromEnum(else_node), at_node)) {
                        collectLiterals(&result, query, cond, false);
                    }
                }
            },
            else => {},
        }
        node = parent;
    }

    var boundary = at_node;
    var current = at_node;
    depth = 0;
    while (depth < 64) : (depth += 1) {
        const block = containingBlock(query, current) orelse break;
        if (boundary >= main_tokens.len) break;
        var inline_statements: [2]u32 = undefined;
        const statements = ast_walk.getBlockStatements(tree, block, &inline_statements) orelse break;
        const limit = token_starts[main_tokens[boundary]];
        for (statements) |statement| {
            if (statement >= main_tokens.len) continue;
            if (token_starts[main_tokens[statement]] >= limit) break;
            if (tags[statement] != .@"if" and tags[statement] != .if_simple) continue;
            const full = tree.fullIf(@enumFromInt(statement)) orelse continue;
            const cond = @intFromEnum(full.ast.cond_expr);
            const then_expr = @intFromEnum(full.ast.then_expr);
            if (containsNode(tree, then_expr, at_node)) continue;
            if (full.ast.else_expr.unwrap()) |else_node| {
                if (containsNode(tree, @intFromEnum(else_node), at_node)) {
                    collectLiterals(&result, query, cond, false);
                }
                continue;
            }
            if (guards.handlerPreventsCompletion(tree, then_expr, tags, datas)) {
                collectLiterals(&result, query, cond, false);
            }
        }
        boundary = block;
        current = block;
    }
    return result;
}

/// Adds the literals `condition` contributes when it is assumed `assumed`.
fn collectLiterals(out: *Literals, query: *const QueryContext, condition: u32, assumed: bool) void {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);
    const main_tokens = tree.nodes.items(.main_token);
    if (condition >= tags.len) return;

    switch (tags[condition]) {
        .grouped_expression => collectLiterals(
            out,
            query,
            @intFromEnum(datas[condition].node_and_token[0]),
            assumed,
        ),
        .@"comptime" => collectLiterals(
            out,
            query,
            @intFromEnum(datas[condition].node),
            assumed,
        ),
        .bool_not => collectLiterals(out, query, @intFromEnum(datas[condition].node), !assumed),
        // A conjunction proves each of its parts; a disjunction only denies
        // each of its parts, so the polarity decides which side is usable.
        .bool_and => {
            if (!assumed) return;
            collectLiterals(out, query, @intFromEnum(datas[condition].node_and_node[0]), true);
            collectLiterals(out, query, @intFromEnum(datas[condition].node_and_node[1]), true);
        },
        .bool_or => {
            if (assumed) return;
            collectLiterals(out, query, @intFromEnum(datas[condition].node_and_node[0]), false);
            collectLiterals(out, query, @intFromEnum(datas[condition].node_and_node[1]), false);
        },
        .identifier => {
            const token = main_tokens[condition];
            if (token >= tree.tokens.len) return;
            if (tree.tokenTag(token) != .identifier) return;
            const name = tree.tokenSlice(token);
            if (std.mem.eql(u8, name, "true") or std.mem.eql(u8, name, "false")) {
                if (std.mem.eql(u8, name, "true") != assumed) out.contradiction = true;
            } else {
                const name_token = comptimeBoolParameterToken(query, condition) orelse return;
                out.add(name_token, assumed);
            }
        },
        else => {},
    }
}

fn bindingOf(query: *const QueryContext, ident_node: u32) ?lexical_index.Candidate {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (ident_node >= tags.len or tags[ident_node] != .identifier) return null;
    const token = main_tokens[ident_node];
    if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return null;
    const name = import_resolver.normalizeIdentifier(tree.tokenSlice(token));
    var best: ?*const lexical_index.Candidate = null;
    for (query.lexical.namedCandidates(name)) |*candidate| {
        if (candidate.kind == .function) continue;
        if (!candidate.is_root and candidate.name_token > token) continue;
        if (!candidate.is_root and !candidate.scope.contains(token)) continue;
        if (best) |previous| {
            if (candidate.scope.span() > previous.scope.span()) continue;
            if (candidate.scope.span() == previous.scope.span() and candidate.name_token <= previous.name_token) continue;
        }
        best = candidate;
    }
    return if (best) |candidate| candidate.* else null;
}

fn parameterNameToken(query: *const QueryContext, ident_node: u32) ?u32 {
    const candidate = bindingOf(query, ident_node) orelse return null;
    if (candidate.kind != .parameter) return null;
    return candidate.name_token;
}

/// The declared type of a parameter, whether the AST spells it as a var decl
/// (`name: T = default`) or leaves only the type expression in place.
pub fn parameterTypeNode(tree: *const std.zig.Ast, param: u32) ?u32 {
    if (param >= tree.nodes.len) return null;
    if (tree.fullVarDecl(@enumFromInt(param))) |full| {
        const type_node = full.ast.type_node.unwrap() orelse return null;
        return @intFromEnum(type_node);
    }
    return param;
}

// ---------------------------------------------------------------------------
// Structure helpers
// ---------------------------------------------------------------------------

pub fn treeFnProto(
    tree: *const std.zig.Ast,
    node: u32,
    buffer: *[1]std.zig.Ast.Node.Index,
) ?std.zig.Ast.full.FnProto {
    if (node >= tree.nodes.len) return null;
    const tags = tree.nodes.items(.tag);
    return switch (tags[node]) {
        .fn_proto => tree.fnProto(@enumFromInt(node)),
        .fn_proto_simple => tree.fnProtoSimple(buffer, @enumFromInt(node)),
        .fn_proto_one => tree.fnProtoOne(buffer, @enumFromInt(node)),
        .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(node)),
        .fn_decl => blk: {
            const proto = @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]);
            if (proto >= tree.nodes.len) break :blk null;
            break :blk treeFnProto(tree, proto, buffer);
        },
        else => null,
    };
}

/// The `fn_decl` that lexically holds `node`.
pub fn enclosingFunction(query: *const QueryContext, node: u32) ?u32 {
    if (node >= query.tree.nodes.len) return null;
    return query.lexical.enclosingFunction(query.firstToken(node));
}

/// The declaration that owns the body `function` describes. Project
/// declaration resolution answers with the prototype node, whose tokens stop
/// at the signature, so every read of what a function hands back has to climb
/// to the declaration first. Null when no declaration owns it, which is a body
/// this file cannot read rather than a body that returns nothing.
fn declaringFunction(query: *const QueryContext, function: u32) ?u32 {
    const tree = query.tree;
    if (function >= tree.nodes.len) return null;
    if (tree.nodes.items(.tag)[function] == .fn_decl) return function;
    return query.lexical.enclosingFunction(query.firstToken(function));
}

pub fn enclosingContainer(query: *const QueryContext, node: u32) ?u32 {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    const first_token = query.firstToken(node);
    if (first_token >= query.lexical.scopes_by_token.len) return null;
    var current = query.lexical.scopes_by_token[first_token];
    while (current != 0) {
        if (current >= tree.nodes.len) return null;
        if (call_resolver.isContainerTag(tags[current])) return current;
        current = query.lexical.parent(current) orelse return null;
    }
    return null;
}

/// Does `type_node` name `container`? The container's own `Self`/`@This()`
/// alias resolves to it directly, and every other spelling goes through the
/// project's declaration resolution, so a same-named type elsewhere does not
/// match.
pub fn denotesContainer(query: *const QueryContext, type_node: u32, container: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (type_node >= tree.nodes.len) return false;

    if (tags[type_node] == .identifier and isContainerSelfAlias(query, type_node)) {
        return enclosingContainer(query, type_node) == container;
    }
    switch (tags[type_node]) {
        .call, .call_comma, .call_one, .call_one_comma => {
            var buffer: [1]std.zig.Ast.Node.Index = undefined;
            const call = tree.fullCall(&buffer, @enumFromInt(type_node)) orelse return false;
            const expr = @intFromEnum(call.ast.fn_expr);
            if (tags[expr] != .identifier) return false;
            const token = tree.nodes.items(.main_token)[expr];
            const function = query.lexical.findFunction(import_resolver.normalizeIdentifier(tree.tokenSlice(token)), token) orelse return false;
            return isFactoryFunction(query, function, container);
        },
        else => {},
    }
    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    const resolved = resolver.resolveTypeNode(type_node) orelse return false;
    return resolved.file_index == 0 and resolved.container_node == container;
}

/// Is this reference the container's `Self` alias, i.e. `const Self = @This();`?
fn isContainerSelfAlias(query: *const QueryContext, ident_node: u32) bool {
    const tree = query.tree;
    const candidate = bindingOf(query, ident_node) orelse return false;
    if (candidate.kind != .variable) return false;
    const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return false;
    const init = full.ast.init_node.unwrap() orelse return false;
    return isThisBuiltin(tree, @intFromEnum(init));
}

fn isThisBuiltin(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= tree.nodes.len) return false;
    switch (tags[node]) {
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => {
            const token = main_tokens[node];
            if (token >= tree.tokens.len or tree.tokenTag(token) != .builtin) return false;
            return std.mem.eql(u8, tree.tokenSlice(token), "@This");
        },
        else => return false,
    }
}

fn containingBlock(query: *const QueryContext, node: u32) ?u32 {
    const tree = query.tree;
    if (node >= tree.nodes.len) return null;
    const tags = tree.nodes.items(.tag);
    var current = node;
    while (current != 0) {
        const parent = query.lexical.parent(current) orelse return null;
        if (parent == 0 or parent >= tree.nodes.len) return null;
        switch (tags[parent]) {
            .block, .block_semicolon, .block_two, .block_two_semicolon => return parent,
            else => {},
        }
        current = parent;
    }
    return null;
}

fn containsNode(tree: *const std.zig.Ast, node: u32, target: u32) bool {
    if (node == 0 or node >= tree.nodes.len or target >= tree.nodes.len) return false;
    return tree.firstToken(@enumFromInt(node)) <= tree.firstToken(@enumFromInt(target)) and
        tree.lastToken(@enumFromInt(target)) <= tree.lastToken(@enumFromInt(node));
}

fn isNullLiteral(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= tree.nodes.len or tags[node] != .identifier) return false;
    const token = main_tokens[node];
    if (token >= tree.tokens.len or tree.tokenTag(token) != .identifier) return false;
    return std.mem.eql(u8, tree.tokenSlice(token), "null");
}

fn structInitFieldNameToken(tree: *const std.zig.Ast, value_node: std.zig.Ast.Node.Index) ?u32 {
    const first = tree.firstToken(value_node);
    if (first < 3 or first >= tree.tokens.len) return null;
    if (tree.tokenTag(first - 1) != .equal) return null;
    if (tree.tokenTag(first - 2) != .identifier) return null;
    if (tree.tokenTag(first - 3) != .period) return null;
    return first - 2;
}

fn isReceiverOfFirstParameter(query: *const QueryContext, receiver: u32, fn_decl: u32) bool {
    const tree = query.tree;
    const tags = tree.nodes.items(.tag);
    if (receiver >= tree.nodes.len or tags[receiver] != .identifier) return false;

    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = treeFnProto(tree, fn_decl, &buffer) orelse return false;
    if (proto.ast.params.len == 0) return false;
    const first = @intFromEnum(proto.ast.params[0]);
    const type_node = parameterTypeNode(tree, first) orelse return false;
    // `*Self` only: an optional or double pointer receiver is not the
    // non-null pointer the field facts assume.
    if (type_node >= tree.nodes.len or tags[type_node] != .ptr_type_aligned) return false;
    const pointer_token = tree.nodes.items(.main_token)[type_node];
    if (pointer_token >= tree.tokens.len or tree.tokenTag(pointer_token) != .asterisk) return false;

    const files = [_]import_resolver.File{.{ .path = "", .tree = tree, .lexical_index = query.lexical }};
    const resolver = call_utils.ProjectTypeResolver{ .files = &files, .file_index = 0 };
    const declared = resolver.resolveDeclarationNode(receiver) orelse return false;
    return declared == first;
}

test "constructor field proof requires closed storage throughout its lifetime" {
    const Source = @import("../../source.zig").Source;
    const Diagnostic = @import("../../diagnostic.zig").Diagnostic;
    const Checker = @import("../optional_unwrap_engine.zig").OptionalUnwrapEngineChecker;
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "sibling field write", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "self.index += 1;", "", "", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "local readonly borrow", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "observe(self);", "fn observe(self: *Self) void { _ = self.index; }", "", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "caller field reset", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "", "var it = Iterator(true).init(1); it.fill = null; _ = it.next();"), .warnings = 1 },
        .{ .name = "address alias reset", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "", "var it = Iterator(true).init(1); const alias = &it; alias.fill = null; _ = it.next();"), .warnings = 1 },
        .{ .name = "whole receiver replacement", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "", "var it = Iterator(true).init(1); it = .{ .fill = null }; _ = it.next();"), .warnings = 1 },
        .{ .name = "callee field reset", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "self.fill = null;", "", "", "var it = Iterator(true).init(1); _ = it.next();"), .warnings = 1 },
        .{ .name = "opaque receiver borrow", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "other.clear(self);", "", "const other = @import(\"other.zig\");", "var it = Iterator(true).init(1); _ = it.next();"), .warnings = 1 },
        .{ .name = "public type factory", .input = constructorFixture("pub ", "std.debug.assert", "if (!pad) return null;", "", "", "", "var it = Iterator(true).init(1); _ = it.next();"), .warnings = 1 },
        .{ .name = "unrelated exported function", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "pub fn peek(value: ?u8) u8 { return value orelse 0; }", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "unrelated function address", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "fn peek() void {}", "var it = Iterator(true).init(1); _ = &peek; std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "exported container factory", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "pub fn blank() Iterator(true) { return .{ .fill = 1 }; }", "var it = Iterator(true).init(1); _ = it.next();"), .warnings = 1 },
        .{ .name = "exported factory through a private alias", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "fn Alias() type { return Iterator(true); }\npub fn makeType() type { return Alias(); }", "const T = makeType(); _ = T;"), .warnings = 1 },
        .{ .name = "exported factory through a parenthesized alias", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "fn Alias() type { return (Iterator(true)); }\npub fn makeType() type { return Alias(); }", "const T = makeType(); _ = T;"), .warnings = 1 },
        .{ .name = "exported factory through a conditional alias", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "fn Alias() type { return if (comptime false) Iterator(true) else Iterator(true); }\npub fn makeType() type { return Alias(); }", "const T = makeType(); _ = T;"), .warnings = 1 },
        .{ .name = "exported factory through a typed local alias", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "fn Alias() type { const T: type = Iterator(true); return T; }\npub fn makeType() type { return Alias(); }", "const T = makeType(); _ = T;"), .warnings = 1 },
        .{ .name = "exported factory through an optional alias", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "fn Alias() type { return ?Iterator(true); }\npub fn makeType() type { return Alias(); }", "const T = makeType(); _ = T;"), .warnings = 1 },
        .{ .name = "exported factory through an alias into another module", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "const other = @import(\"other.zig\");\nfn Alias() type { return other.container(); }\npub fn makeType() type { return Alias(); }", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 1 },
        .{ .name = "exported factory through a value binding", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "const Alias = Iterator(true);\npub fn makeType() type { return Alias; }", "const T = makeType(); _ = T;"), .warnings = 1 },
        .{ .name = "unrelated exported function forwarding a private helper", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "fn scale(value: u8) u8 { return std.math.clamp(value, 0, 100); }\npub fn peek(value: u8) u8 { return scale(value); }", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "unrelated scalar route longer than any walk budget", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "fn hop1(value: u8) u8 { return value; }\nfn hop2(value: u8) u8 { return hop1(value); }\nfn hop3(value: u8) u8 { return hop2(value); }\nfn hop4(value: u8) u8 { return hop3(value); }\nfn hop5(value: u8) u8 { return hop4(value); }\nfn hop6(value: u8) u8 { return hop5(value); }\nfn hop7(value: u8) u8 { return hop6(value); }\nfn hop8(value: u8) u8 { return hop7(value); }\nfn hop9(value: u8) u8 { return hop8(value); }\nfn hop10(value: u8) u8 { return hop9(value); }\npub fn peek(value: u8) u8 { return hop10(value); }", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "unrelated shared helper graph past the inline answer table", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", sharedHelperChain(20) ++ "pub fn peek(value: u8) [1]u8 { return hop20(value); }", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "shared aggregate helper read by a consumer of its element", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", sharedHelperChain(20) ++ "pub fn aggregate(value: u8) [1]u8 { return hop20(value); }\n" ++ "test \"shared aggregate helper preserves the input byte\" { const result = aggregate(7); try std.testing.expectEqual(@as(u8, 7), result[0]); }", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "unrelated exported function forwarding a bound value", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "const Defaults = makeDefaults();\nfn makeDefaults() [1]u8 { return [_]u8{7}; }\npub fn defaults() [1]u8 { return Defaults; }", "var it = Iterator(true).init(1); std.debug.assert(it.next() == 1);"), .warnings = 0 },
        .{ .name = "missing comptime guard", .input = constructorFixture("", "std.debug.assert", "", "", "", "", "var it = Iterator(false).init(null); _ = it.next();"), .warnings = 1 },
        .{ .name = "fake assertion", .input = constructorFixture("", "fakeAssert", "if (!pad) return null;", "", "", "fn fakeAssert(condition: bool) void { _ = condition; }", "var it = Iterator(true).init(null); _ = it.next();"), .warnings = 1 },
        .{ .name = "nullable alternative constructor", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "pub fn blank() Self { return .{ .fill = null }; }", "", "var it = Iterator(true).blank(); _ = it.next();"), .warnings = 1 },
        .{ .name = "constructor callback escape", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "const other = @import(\"other.zig\"); fn make() Iterator(true) { return .{ .fill = 1 }; }", "var it = Iterator(true).init(1); other.take(make); _ = it.next();"), .warnings = 1 },
        .{ .name = "undefined receiver", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "", "var it: Iterator(true) = undefined; _ = it.next();"), .warnings = 1 },
        .{ .name = "array element construction", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "", "const table = [_]Iterator(true){.{ .fill = null }}; var it: Iterator(true) = table[0]; _ = it.next();"), .warnings = 1 },
        .{ .name = "grouped construction", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "", "var it: Iterator(true) = (.{ .fill = null }); _ = it.next();"), .warnings = 1 },
        .{ .name = "switch result construction", .input = constructorFixture("", "std.debug.assert", "if (!pad) return null;", "", "", "", "var it: Iterator(true) = switch (@as(u8, 0)) { else => .{ .fill = null } }; _ = it.next();"), .warnings = 1 },
    };
    for (cases) |case| {
        var source = Source.init(std.testing.allocator, case.name, case.input);
        defer source.deinit();
        try std.testing.expectEqual(@as(usize, 0), (try source.ast()).errors.len);
        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer diagnostics.deinit(std.testing.allocator);
        defer for (diagnostics.items) |*diagnostic| diagnostic.deinit(std.testing.allocator);
        try Checker.checker.checkAst(&source, std.testing.allocator, &diagnostics, .{ .build_metadata = null });
        std.testing.expectEqual(case.warnings, diagnostics.items.len) catch |err| {
            std.debug.print("constructor scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
}

/// Helpers that hand back an unrelated `[1]u8` -- a type this file cannot
/// read as scalar and cannot read as the container either -- with every one of
/// them naming the previous helper from *both* arms of one branch. Every path
/// through the chain therefore reaches the same helper, so a walk that reads a
/// helper once per path grows as the number of paths, while a walk that
/// remembers a finished `false` reads each helper once however many paths
/// arrive at it. The chain is longer than the inline answer table, so the
/// answers past it live in the spill.
fn sharedHelperChain(comptime last: usize) []const u8 {
    comptime var text: []const u8 = "fn hop0(value: u8) [1]u8 { return .{value}; }\n";
    comptime var index: usize = 1;
    inline while (index <= last) : (index += 1) {
        text = text ++ std.fmt.comptimePrint(
            "fn hop{d}(value: u8) [1]u8 {{ return if (value > {d}) hop{d}(value) else hop{d}(value); }}\n",
            .{ index, index, index - 1, index - 1 },
        );
    }
    return text;
}

fn constructorFixture(
    comptime visibility: []const u8,
    comptime assertion: []const u8,
    comptime guard: []const u8,
    comptime before: []const u8,
    comptime extra_method: []const u8,
    comptime extra_top: []const u8,
    comptime main_body: []const u8,
) [:0]const u8 {
    return "const std = @import(\"std\");\n" ++ visibility ++
        "fn Iterator(comptime pad: bool) type {\n" ++
        "return struct {\n" ++
        "const Self = @This();\n" ++
        "fill: ?u8,\nindex: usize = 0,\n" ++
        "pub fn init(fill: ?u8) Self {\nif (pad) " ++ assertion ++ "(fill != null);\nreturn .{ .fill = fill };\n}\n" ++
        "pub fn next(self: *Self) ?u8 {\n" ++ guard ++ "\n" ++ before ++ "\nreturn self.fill.?;\n}\n" ++
        extra_method ++ "\n};\n}\n" ++ extra_top ++ "\n" ++
        "pub fn main() void {\n" ++ main_body ++ "\n}\n";
}
