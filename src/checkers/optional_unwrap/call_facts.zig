//! Call-context facts for `optional-unwrap`.
//!
//! A private method that unwraps `self.field.?` is decided by the calls that
//! actually reach it, never by its name, by the spelling of its receiver, or by
//! an assumption that a method receiver is initialized. Every reachable direct
//! caller has to establish that exact field on that exact object before the
//! call, and nothing on the way may invalidate it. One unguarded caller, one
//! caller that guards a different field, one caller that clears the field
//! first, and a method reference that escapes the file all defeat the proof.
//!
//! "On the way" reaches inside the callee as well as back to its callers. The
//! receiver is a pointer the caller fills, and a global is the one object in a
//! file a callee reaches without being handed it: `session.read(sink)` hands
//! `read` the address of the module-level `session`, so a call inside that
//! body which stores `null` into `session.field` destroys what every caller
//! proved — while a method on a parameter of another type writes only the
//! bytes that parameter owns.
//!
//! The same machinery reads the two other ways a field becomes non-null,
//! because both establish exactly one kind of fact — which fields of one object
//! are non-null at one program point:
//!
//! * a lifecycle installer: `try app.start(...)` writes the field
//!   unconditionally on the success path, so the code after the call runs only
//!   once that write happened. An `errdefer` rollback runs on the error path,
//!   which a `try`ed call has already left behind.
//! * a successfully constructed owner: `var s = try setupSession(...)` is a
//!   value whose optional fields the constructor installed on every one of its
//!   return paths. The facts survive nesting, so a driver built from a
//!   constructed session carries `session.region` with it.
//!
//! Everything here is closed-world on purpose. An unresolved callee, an
//! escaping reference, an aliasing argument, a recovered error, a nested owner
//! whose origin is unaccounted for and a write the scan cannot read all answer
//! "not proven", so the caller keeps the warning.
const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const import_resolver = @import("../../analysis/import_resolver.zig");
const lexical_index = @import("../../analysis/lexical_index.zig");
const TypeContext = @import("../../type_context.zig").TypeContext;
const QueryContext = @import("bindings.zig").QueryContext;
const constructor_facts = @import("constructor_facts.zig");
const guards = @import("guards.zig");
const Source = @import("../../source.zig").Source;
const Diagnostic = @import("../../diagnostic.zig").Diagnostic;
const Checker = @import("../optional_unwrap_engine.zig").OptionalUnwrapEngineChecker;

/// Longest place a fact may name. A receiver's own field chain is short, and a
/// bounded chain keeps every table in this file allocation-free.
const max_depth = 4;

/// How deep a chain of constructors may nest before the scan stops reading it.
///
/// A path is capped at `max_depth`, but reaching one through plain factories
/// costs three levels per hop — the call, the value it returns and the field
/// that holds it — so the bound has to leave room for the chains a caller can
/// write. It is also what keeps two factories that return each other from
/// recursing without end.
const max_nesting = 16;

/// How many private-call contexts one unwrap may be proved through.
///
/// A caller-context walk hops from a method to the method that calls it, and a
/// generic receiver adds a second hop for the parameter the prototype leaves
/// untyped. The chain a caller can actually write is short, and a chain that
/// outgrows this bound is a chain this scan can no longer vouch for, so it
/// answers "not proven" rather than following a cycle.
const max_context_depth = 6;

/// The entry point the scanner calls once per unwrap.
///
/// `target` is the expression under the `?` and `unwrap_node` the
/// `unwrap_optional` node itself.
pub fn isProvenByCallContext(
    query: *const QueryContext,
    unwrap_node: u32,
    target: u32,
    type_context: ?*TypeContext,
) bool {
    const tree = query.tree;
    if (target >= tree.nodes.len or unwrap_node >= tree.nodes.len) return false;
    if (tree.nodeTag(@enumFromInt(target)) != .field_access) return false;

    const solver = Solver{ .query = query, .type_context = type_context };
    if (solver.provenForPrivateMethod(unwrap_node, target)) return true;
    return solver.provenForConstructedOwner(unwrap_node, target);
}

/// What a callee, a nested call, or a statement can do to one place.
const Effect = enum {
    /// Nothing in the analysed code reaches the place.
    untouched,
    /// Every path that reaches the end of the scope stores a non-null value.
    installs,
    /// A path leaves the scope with the place not installed there. Such a path
    /// does not put a null back, so the place is neither installed nor lost: a
    /// caller cannot count on the installation, while a field an earlier
    /// statement installed keeps it.
    not_installed,
    /// Some path stores null, stores an unknown value, or leaves the analysis.
    invalidated,
};

/// A dotted storage path: the declaration it starts at plus the field names
/// walked from there.
const Path = struct {
    root: u32 = 0,
    names: [max_depth][]const u8 = undefined,
    len: usize = 0,

    fn slice(self: *const Path) []const []const u8 {
        return self.names[0..self.len];
    }
};

fn samePath(left: Path, right: Path) bool {
    if (left.root != right.root or left.len != right.len) return false;
    for (left.slice(), right.slice()) |a, b| {
        if (!std.mem.eql(u8, a, b)) return false;
    }
    return true;
}

/// Is `candidate` a prefix of `whole`, so a write there also writes `whole`?
fn isPrefixOf(candidate: []const []const u8, whole: []const []const u8) bool {
    if (candidate.len > whole.len) return false;
    for (candidate, 0..) |name, index| {
        if (!std.mem.eql(u8, whole[index], name)) return false;
    }
    return true;
}

/// Which fields a successfully constructed owner carries as non-null.
///
/// The set is deliberately closed: an owner whose facts overflow it loses every
/// fact, because a truncated table would silently answer "not installed" for a
/// field that is.
const OwnerFacts = struct {
    known: bool = false,
    len: usize = 0,
    depths: [8]u8 = undefined,
    paths: [8][max_depth][]const u8 = undefined,

    fn holds(self: OwnerFacts, path: []const []const u8) bool {
        if (!self.known or path.len == 0 or path.len > max_depth) return false;
        for (self.paths[0..self.len], self.depths[0..self.len]) |candidate, depth| {
            if (depth != path.len) continue;
            if (sameNames(candidate[0..depth], path)) return true;
        }
        return false;
    }

    fn insert(self: *OwnerFacts, path: []const []const u8) void {
        if (!self.known or path.len == 0 or path.len > max_depth) return;
        if (self.holds(path)) return;
        if (self.len == self.paths.len) {
            self.known = false;
            return;
        }
        for (path, 0..) |name, index| self.paths[self.len][index] = name;
        self.depths[self.len] = @intCast(path.len);
        self.len += 1;
    }

    /// Keeps only what `other` also carries, which is what intersecting the
    /// constructor's return paths requires: a field one path installs and
    /// another does not is not a field the owner always carries.
    fn intersect(self: *OwnerFacts, other: OwnerFacts) void {
        if (!other.known) {
            self.known = false;
            return;
        }
        var kept: usize = 0;
        for (self.paths[0..self.len], self.depths[0..self.len]) |candidate, depth| {
            if (!other.holds(candidate[0..depth])) continue;
            self.paths[kept] = candidate;
            self.depths[kept] = depth;
            kept += 1;
        }
        self.len = kept;
    }
};

fn sameNames(left: []const []const u8, right: []const []const u8) bool {
    if (left.len != right.len) return false;
    for (left, right) |a, b| {
        if (!std.mem.eql(u8, a, b)) return false;
    }
    return true;
}

/// The verdict of one lexical level; `decided` stays false while nothing the
/// level passes says anything about the place.
const LevelVerdict = struct {
    decided: bool = false,
    safe: bool = false,
};

/// The declarations a caller-context proof has already read.
///
/// A name can be reached from itself: a method that hands its own receiver to
/// the generic function around it puts the same declaration back on the chain,
/// and a pair of methods that call each other does the same thing one hop
/// later. Re-entering one of these means the walk has stopped describing
/// callers and started describing a cycle, which is not evidence about any
/// object.
const ContextChain = struct {
    methods: [max_context_depth]u32 = undefined,
    len: usize = 0,

    fn contains(self: ContextChain, method: u32) bool {
        for (self.methods[0..self.len]) |seen| {
            if (seen == method) return true;
        }
        return false;
    }

    /// The chain with one more declaration on it. Every caller bounds the walk
    /// against `max_context_depth` before it pushes, so this never writes past
    /// the table.
    fn push(self: ContextChain, method: u32) ContextChain {
        var next = self;
        next.methods[next.len] = method;
        next.len += 1;
        return next;
    }
};

const Solver = struct {
    query: *const QueryContext,
    type_context: ?*TypeContext,

    // -----------------------------------------------------------------
    // The two entry proofs
    // -----------------------------------------------------------------

    /// The unwrap sits on a private method's own receiver, so the calls that
    /// reach that method decide it.
    fn provenForPrivateMethod(self: Solver, unwrap_node: u32, target: u32) bool {
        const tree = self.query.tree;
        const method = constructor_facts.enclosingFunction(self.query, target) orelse return false;
        if (constructor_facts.enclosingFunction(self.query, unwrap_node) != method) return false;
        const receiver_token = receiverNameToken(tree, method) orelse return false;
        if (!receiverIsSinglePointer(tree, method)) return false;
        if (!self.declarationIsFilePrivate(method)) return false;
        if (self.methodEscapes(method)) return false;
        if (!self.otherParametersCannotAlias(method)) return false;

        const place = self.storagePlace(target) orelse return false;
        if (place.root != receiver_token or place.len == 0) return false;

        // A guard, an assignment or an early exit inside the callee settles the
        // use on its own, so no caller has to be consulted.
        const inside = self.provesAtPoint(unwrap_node, place);
        if (inside) return true;

        // What the callers establish is the state this method is entered with,
        // not the state it is left in: every caller proves the field before the
        // call, so a body that runs a call which puts the null back has undone
        // all of them.
        if (!self.preservedFromEntry(unwrap_node, place, true, false)) return false;

        // Otherwise every reachable caller must establish the field, and a
        // method nobody calls here has no evidence at all.
        const callers = self.callersProvePlace(method, place.slice(), .{});
        return callers;
    }

    /// The object under the `?` is a local whose value came from a constructor
    /// that installs the field on every success path.
    fn provenForConstructedOwner(self: Solver, unwrap_node: u32, target: u32) bool {
        const place = self.storagePlace(target) orelse return false;
        if (place.len == 0 or place.len > max_depth) return false;
        return self.provesAtPoint(unwrap_node, place);
    }

    // -----------------------------------------------------------------
    // Caller contexts
    // -----------------------------------------------------------------

    /// Does every way this file reaches `method` establish `names` on the very
    /// object that call passes?
    ///
    /// A name is only a filter over the candidates. Which declaration a
    /// same-named call reaches is read from the receiver's own type, so a call
    /// that reaches another container's method reaches that method and not this
    /// one, and a call nothing here can attribute judges nothing.
    ///
    /// A receiver the prototype leaves untyped has no type at the use, so what
    /// that name reaches is decided by the object each visible call of the
    /// generic function around it passes. Those objects are the contexts the
    /// proof is read in: a caller hands the generic function storage, and the
    /// generic function's own body has to keep the field on it until it calls.
    fn callersProvePlace(self: Solver, method: u32, names: []const []const u8, chain: ContextChain) bool {
        if (chain.len >= max_context_depth or chain.contains(method)) return false;
        if (names.len == 0 or names.len > max_depth) return false;
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const name = self.fieldName(methodNameToken(tree, method) orelse return false);
        const extended = chain.push(method);

        var callers: usize = 0;
        var node: u32 = 1;
        while (node < tags.len) : (node += 1) {
            const access = calleeFieldAccess(tree, node) orelse continue;
            if (!std.mem.eql(u8, self.fieldName(access[1]), name)) continue;
            if (self.calleeAtCall(node)) |resolved| {
                if (resolved != method) continue;
                const established = self.callerEstablishesPlace(@intFromEnum(access[0]), names, extended);
                if (!established) return false;
                callers += 1;
                continue;
            }
            var walk = UntypedCallerWalk{ .method = method, .names = names, .chain = extended };
            // A call nothing here can attribute judges nothing at all, which is
            // what an unknown callee has always answered.
            if (self.untypedCallersProvePlace(node, &walk)) |attributed| {
                if (!attributed) return false;
                callers += walk.callers;
                continue;
            }
            return false;
        }
        return callers != 0;
    }

    /// Is the place a caller passes non-null where it calls, going through the
    /// objects that declaration's own callers hand it?
    ///
    /// A place spelled on a local is settled by the point query alone. A place
    /// spelled on the declaration's own receiver is storage this file hands
    /// out, so its callers decide it — but only while the declaration is
    /// private, is never handed around as a value, and takes no parameter that
    /// could rewrite the field. A place spelled through a field of a structure
    /// this file builds is the same place spelled from whatever that field was
    /// given, which is how a context field is carried back to the owner. Every
    /// point query below is the question asked at the entry of the call, so the
    /// arguments that call passes are read as running ahead of it.
    fn placeProvenInContext(self: Solver, use_node: u32, place: Path, chain: ContextChain) bool {
        if (chain.len >= max_context_depth) return false;
        const at_entry = self.provesAtCalleeEntry(use_node, place);
        if (at_entry) return true;
        if (self.rewrittenThroughInitializer(place)) |rewritten| {
            const rewritten_entry = self.provesAtCalleeEntry(use_node, rewritten);
            if (rewritten_entry) return true;
        }
        const method = constructor_facts.enclosingFunction(self.query, use_node) orelse return false;
        const receiver = receiverNameToken(self.query.tree, method) orelse return false;
        if (place.root != receiver) return false;
        if (!self.declarationIsFilePrivate(method)) return false;
        if (self.methodEscapes(method)) return false;
        if (!self.otherParametersCannotAlias(method)) return false;
        return self.callersProvePlace(method, place.slice(), chain);
    }

    /// Does the object this call passes carry `names` as a non-null field?
    fn callerEstablishesPlace(self: Solver, receiver_expr: u32, names: []const []const u8, chain: ContextChain) bool {
        const place = self.appendedPlace(receiver_expr, names) orelse return false;
        return self.placeProvenInContext(receiver_expr, place, chain);
    }

    /// The object this expression names with `names` appended to it, when that
    /// expression names storage this scan can read.
    fn appendedPlace(self: Solver, expr: u32, names: []const []const u8) ?Path {
        const receiver = self.storagePlace(expr) orelse return null;
        if (receiver.len + names.len > max_depth) return null;
        var place = receiver;
        for (names, 0..) |field, index| place.names[receiver.len + index] = field;
        place.len = receiver.len + names.len;
        return place;
    }

    /// The same place spelled from the object a field of a structure this file
    /// builds was given.
    ///
    /// `var sink: Sink = .{ .owner = self };` makes `sink.owner` a name for
    /// whatever `self` was when the literal ran, so a place reaching through
    /// that field is the place spelled from the owner. A binding this file does
    /// not build here, a literal that does not store the field, a value the
    /// place builder cannot name, a binding written to again later in the
    /// same function, and a binding whose address is handed to a call all
    /// answer nothing: what the literal established is not a
    /// fact about every later use of that name.
    fn rewrittenThroughInitializer(self: Solver, place: Path) ?Path {
        if (place.len == 0) return null;
        const stored = self.initializerFieldPlace(place.root, place.names[0]) orelse return null;
        const tail = place.slice()[1..];
        if (stored.len + tail.len > max_depth) return null;
        var result = stored;
        for (tail, 0..) |field, index| result.names[stored.len + index] = field;
        result.len = stored.len + tail.len;
        if (samePath(result, place)) return null;
        return result;
    }

    fn initializerFieldPlace(self: Solver, root: u32, field: []const u8) ?Path {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const candidate = self.bindingForToken(root) orelse return null;
        if (candidate.kind != .variable) return null;
        const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return null;
        const init = @intFromEnum(full.ast.init_node.unwrap() orelse return null);
        if (init >= tags.len or constructor_facts.structInitAt(tags, init) == null) return null;
        if (self.bindingIsRewritten(root)) return null;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        const literal = tree.fullStructInit(&buffer, @enumFromInt(init)) orelse return null;
        for (literal.ast.fields) |value_node| {
            const value = @intFromEnum(value_node);
            const name_token = structInitFieldNameToken(tree, value_node) orelse continue;
            if (!std.mem.eql(u8, self.fieldName(name_token), field)) continue;
            return self.storagePlace(value);
        }
        return null;
    }

    /// Is this binding written to anywhere in the function that declares it, or
    /// handed to a call that may write it?
    ///
    /// The name in `root` is a token, and `enclosingFunction` answers about a
    /// node: a token handed to it names the first token of whatever node
    /// happens to sit at that index, so the declaration the binding belongs to
    /// is read back out of the index that name resolved through and compared as
    /// the declaration that owns it. A binding no declaration answers for is
    /// treated as rewritten, which is the direction that keeps the warning.
    ///
    /// An initializer that stores an object in one of its fields established a
    /// fact about that object, so a write to the binding loses it — and so does
    /// handing the binding to a call, because a pointer carries the object and
    /// everything stored inside it.
    fn bindingIsRewritten(self: Solver, root: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const function = self.declaringFunction(root) orelse return true;
        var node: u32 = 1;
        while (node < tags.len) : (node += 1) {
            if (isAssignTag(tags[node])) {
                if (constructor_facts.enclosingFunction(self.query, node) != function) continue;
                const lhs = @intFromEnum(tree.nodes.items(.data)[node].node_and_node[0]);
                const written = self.storagePlace(lhs) orelse continue;
                if (self.aliasRoot(written.root, 0) == self.aliasRoot(root, 0)) return true;
                continue;
            }
            switch (tags[node]) {
                .call, .call_comma, .call_one, .call_one_comma => {
                    if (constructor_facts.enclosingFunction(self.query, node) != function) continue;
                    if (self.callHandsOverTo(node, root, Path{ .root = root }, 0)) return true;
                },
                .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                    if (constructor_facts.enclosingFunction(self.query, node) != function) continue;
                    if (self.builtinWritesThrough(node, root, Path{ .root = root })) return true;
                },
                else => {},
            }
        }
        return false;
    }

    /// The declaration that owns the binding a name token introduces.
    fn declaringFunction(self: Solver, root: u32) ?u32 {
        const candidate = self.bindingForToken(root) orelse return null;
        return constructor_facts.enclosingFunction(self.query, candidate.node);
    }

    /// Does this call hand the storage `root` names to a callee that may write
    /// it?
    ///
    /// A pointer names the object and every field chain below it, so the callee
    /// is followed into its own body rather than judged by the spelling of its
    /// name: only a declaration this file holds whose body writes nothing
    /// through the parameter it was handed keeps the initializer's fact. A call
    /// this scan cannot attribute answers the same way, because a write it
    /// hides is a write all the same.
    ///
    /// A method call hands the storage over as its receiver rather than as an
    /// argument, and it has an empty argument list, so the receiver is read
    /// here as well: `drive(&sink)` reaches the owner's field through
    /// `target.owner.reset()` and that write is one the arguments alone never
    /// see.
    fn callHandsOverTo(self: Solver, call_node: u32, root: u32, place: Path, depth: u32) bool {
        const tree = self.query.tree;
        const call = fullCall(tree, call_node) orelse return true;
        for (call.ast.params, 0..) |param, index| {
            if (!self.mentionsObject(@intFromEnum(param), root)) continue;
            if (self.calleeWritesArgument(call_node, index, place, depth)) return true;
        }
        return self.receiverWritesThroughPlace(call_node, root, place, depth);
    }

    /// May the declaration this call reaches write through the storage its own
    /// receiver names?
    ///
    /// A receiver spelled as a field of the handed-over object is storage only
    /// the callee reaches, so its body is followed with that field standing
    /// for the receiver: `target.owner.reset()` writes through `target`, and
    /// the declaration it reaches answers that exactly as a callee reached
    /// through an argument answers. A receiver spelled as the object itself is
    /// the storage the caller already accounted for, so it is not followed
    /// again — that is the call this scan reads as `sink.append(value)`, whose
    /// body only reads the field it is about.
    fn receiverWritesThroughPlace(self: Solver, call_node: u32, root: u32, place: Path, depth: u32) bool {
        if (depth >= 4) return true;
        const tree = self.query.tree;
        const access = calleeFieldAccess(tree, call_node) orelse return false;
        const receiver = self.storagePlace(@intFromEnum(access[0])) orelse return false;
        if (self.aliasRoot(receiver.root, 0) != self.aliasRoot(root, 0)) return false;
        if (receiver.len == 0) return false;
        const callee = self.calleeAtCall(call_node) orelse return true;
        const body = functionBody(tree, callee) orelse return true;
        const parameter = receiverNameToken(tree, callee) orelse return true;
        return self.bodyWritesThrough(body, parameter, place, depth + 1);
    }

    /// May the declaration this call reaches write through the storage handed to
    /// the parameter at `index`?
    ///
    /// A parameter the prototype leaves untyped is not missing evidence: its
    /// body is in this file like any other, so the storage the caller handed it
    /// is followed through that name exactly as a typed parameter's is. The
    /// body may still do something this scan cannot spell as a write through
    /// it, and `bodyWritesThrough` answers that the same way it does for a
    /// typed one, so a call this scan cannot read still keeps the warning.
    fn calleeWritesArgument(self: Solver, call_node: u32, index: usize, place: Path, depth: u32) bool {
        if (depth >= 4) return true;
        const tree = self.query.tree;
        // An instance method is reached without its receiver written at the call
        // site, so the prototype holds back as many leading parameters as the
        // caller never passes: the one argument of `sink.append(value)` reaches
        // the prototype's second parameter, not its receiver. A bare name holds
        // none back, which is the answer a plain callee gives.
        const reached = self.callableAtCall(call_node);
        const implicit = if (reached) |info| info.implicit_self_count else 0;
        const resolved: ?u32 = if (reached) |info| self.declarationOfPrototype(info.proto_node) else null;
        const callee = resolved orelse (self.plainCallee(call_node) orelse return true);
        const body = functionBody(tree, callee) orelse return true;
        // A prototype that does not hold the parameter this argument reaches is
        // one this scan cannot read, and a write it hides is a write all the same.
        const parameter = self.parameterNameTokenAt(callee, implicit + index) orelse return true;
        return self.bodyWritesThrough(body, parameter, place, depth + 1);
    }

    /// The token that names the parameter the argument at `index` is handed.
    ///
    /// Zig keeps an `anytype` or `...` parameter out of the prototype's own
    /// parameter list, because it is a bare token rather than a type
    /// expression, so a position in that list and a position in a call's
    /// argument list stop agreeing as soon as one of those parameters is
    /// written first. The prototype's own iteration is in the order the
    /// parameters are written, which is the order a call passes them in: the
    /// second argument of `scan(value: u8, sink: anytype)` is `sink`, and the
    /// second argument of `relay(tag: anytype, target: *Sink, mode: anytype)`
    /// is the typed parameter the list itself records first.
    fn parameterNameTokenAt(self: Solver, function: u32, index: usize) ?u32 {
        const tree = self.query.tree;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = constructor_facts.treeFnProto(tree, function, &buffer) orelse return null;
        var written: usize = 0;
        var params = proto.iterate(tree);
        while (params.next()) |param| : (written += 1) {
            if (written != index) continue;
            const name_token = param.name_token orelse return null;
            if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
            return @intCast(name_token);
        }
        return null;
    }

    /// The declaration a call reaches, read from the spelling of a plain name
    /// when the receiver's own types cannot attribute it.
    fn plainCallee(self: Solver, call_node: u32) ?u32 {
        const tree = self.query.tree;
        const call = fullCall(tree, call_node) orelse return null;
        const expr = @intFromEnum(call.ast.fn_expr);
        if (expr >= tree.nodes.len or tree.nodeTag(@enumFromInt(expr)) != .identifier) return null;
        const resolved = self.resolvePlainFunction(expr) orelse return null;
        return self.declarationOfPrototype(resolved);
    }

    /// Does anything in this body write through the storage `root` names, which
    /// the caller handed over as `place`?
    ///
    /// The parameter stands for `place` for the whole body, so a write spelled
    /// on it lands in the object the caller still owns, and a call handed the
    /// same storage is followed the same way. A name this scan cannot place,
    /// and a name of some other object, both answer conservatively.
    fn bodyWritesThrough(self: Solver, body: u32, root: u32, place: Path, depth: u32) bool {
        if (depth >= 4) return true;
        const scan_tree = self.query.tree;
        const Visitor = struct {
            solver: Solver,
            root: u32,
            place: Path,
            depth: u32,
            found: bool = false,
            stop: bool = false,

            fn raise(visitor: *@This()) void {
                visitor.found = true;
                visitor.stop = true;
            }

            pub fn visit(visitor: *@This(), _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
                if (visitor.found) return;
                const tree = visitor.solver.query.tree;
                const datas = tree.nodes.items(.data);
                switch (tag) {
                    .@"asm", .asm_simple => visitor.raise(),
                    .address_of => {
                        if (visitor.solver.writeReachesThrough(@intFromEnum(datas[node].node), visitor.root, visitor.place)) {
                            visitor.raise();
                        }
                    },
                    .assign_destructure => {
                        const full = tree.assignDestructure(@enumFromInt(node));
                        for (full.ast.variables) |variable| {
                            if (visitor.solver.writeReachesThrough(@intFromEnum(variable), visitor.root, visitor.place)) {
                                visitor.raise();
                                return;
                            }
                        }
                    },
                    .call, .call_comma, .call_one, .call_one_comma => {
                        if (visitor.solver.callHandsOverTo(node, visitor.root, visitor.place, visitor.depth)) {
                            visitor.raise();
                        }
                    },
                    .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                        if (visitor.solver.builtinWritesThrough(node, visitor.root, visitor.place)) visitor.raise();
                    },
                    else => {
                        if (!isAssignTag(tag)) return;
                        if (visitor.solver.writeReachesThrough(@intFromEnum(datas[node].node_and_node[0]), visitor.root, visitor.place)) {
                            visitor.raise();
                        }
                    },
                }
            }
        };
        var visitor = Visitor{ .solver = self, .root = root, .place = place, .depth = depth };
        ast_walk.walk(Visitor, scan_tree, body, &visitor) catch return true;
        return visitor.found;
    }

    /// Does this builtin write into storage stored inside the object `root`
    /// names?
    ///
    /// Nothing here can read what a builtin does with an address, so an
    /// argument that names that storage answers yes.
    fn builtinWritesThrough(self: Solver, node: u32, root: u32, place: Path) bool {
        const tree = self.query.tree;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        const params = tree.builtinCallParams(&buffer, @enumFromInt(node)) orelse {
            return self.mentionsObject(node, root);
        };
        for (params) |param| {
            if (self.writeReachesThrough(@intFromEnum(param), root, place)) return true;
        }
        return false;
    }

    /// May a write spelled through `expr` reach storage stored inside the object
    /// `root` names, which the caller handed over as `place`?
    ///
    /// The mirror of `writeMayReach`: a pointer carries everything below it, so
    /// a write inside the object is a write to it, and a write of the object
    /// itself replaces what the caller holds. A name this scan cannot place
    /// answers conservatively, the way it does everywhere else.
    fn writeReachesThrough(self: Solver, expr: u32, root: u32, place: Path) bool {
        const written = self.storagePlace(expr) orelse return self.mentionsObject(expr, root);
        if (self.aliasRoot(written.root, 0) != self.aliasRoot(root, 0)) {
            return self.foreignWriteReaches(written, place.root, place.slice());
        }
        return isPrefixOf(place.slice(), written.slice()) or isPrefixOf(written.slice(), place.slice());
    }

    /// The instantiations one call through an untyped receiver is read under.
    const UntypedCallerWalk = struct {
        method: u32,
        names: []const []const u8,
        chain: ContextChain,
        callers: usize = 0,
    };

    /// What the declarations a call through an untyped receiver reaches have to
    /// establish, and how many of them are this one.
    ///
    /// `null` is the "cannot attribute" answer: the receiver is not a parameter
    /// the prototype leaves bare, the generic function may be called from
    /// outside this file or handed around instead of called, or one of its
    /// calls passes something this scan cannot read. A call that reaches a
    /// declaration of another container is that method's caller and not this
    /// one's, so it is not a failure here.
    fn untypedCallersProvePlace(self: Solver, call_node: u32, walk: *UntypedCallerWalk) ?bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const access = calleeFieldAccess(tree, call_node) orelse return null;
        const name = self.fieldName(access[1]);
        const receiver_expr = @intFromEnum(access[0]);
        const untyped = self.untypedParameterOf(receiver_expr) orelse return null;
        const generic = untyped.function;
        if (walk.chain.contains(generic)) return null;
        if (!self.declarationIsFilePrivate(generic)) return null;
        if (!self.everyReferenceIsACall(generic)) return null;
        if (!self.otherParametersCannotNameReceiver(generic, untyped.index, walk.method)) return null;

        var sites: usize = 0;
        var reached = false;
        var node: u32 = 1;
        while (node < tags.len) : (node += 1) {
            if (!isCallTag(tags[node])) continue;
            if (!self.callReachesFunction(node, generic)) continue;
            const call = fullCall(tree, node) orelse return null;
            const index = untyped.index;
            if (index >= call.ast.params.len) return null;
            const passed = self.addressedOperand(@intFromEnum(call.ast.params[index])) orelse return null;
            const declaration = self.memberDeclaration(passed, name) orelse return null;
            sites += 1;
            if (declaration != walk.method) continue;
            reached = true;
            if (!self.passedObjectCarriesPlace(passed, walk.names)) return false;
        }
        if (sites == 0) return null;
        if (!reached) return true;
        if (!self.parameterPlaceProven(receiver_expr, walk.names)) return false;
        walk.callers += 1;
        return true;
    }

    /// Does the object a caller hands the generic function still carry `names`
    /// where it calls?
    ///
    /// The question is the state the callee is *entered* with, not the state
    /// the argument itself was read in: Zig reaches a call's body only after
    /// every operand, so a field that an argument written after the handed-over
    /// object puts back is null by the time the body reads it. `scan(&sink,
    /// value, self.clear())` hands over an owner the clear has not run on yet,
    /// and crediting it with the `try self.ensure()` that preceded the call is
    /// exactly the borrow the callee entry does not get. This is the
    /// callee-entry reading `parameterPlaceProven` takes for the body itself.
    fn passedObjectCarriesPlace(self: Solver, passed: u32, names: []const []const u8) bool {
        const place = self.appendedPlace(passed, names) orelse return false;
        if (self.provesAtCalleeEntry(passed, place)) return true;
        if (self.rewrittenThroughInitializer(place)) |rewritten| {
            if (self.provesAtCalleeEntry(passed, rewritten)) return true;
        }
        return false;
    }

    /// Is `names` still non-null on the object the untyped parameter names at
    /// the use, given that it was non-null when the caller called?
    ///
    /// The caller establishes the place on the object it passes, so the generic
    /// body only has to keep it: anything between its entry and the use either
    /// leaves the place alone or destroys it, and only the second one stops the
    /// proof.
    fn parameterPlaceProven(self: Solver, receiver_expr: u32, names: []const []const u8) bool {
        const place = self.appendedPlace(receiver_expr, names) orelse return false;
        if (self.provesAtCalleeEntry(receiver_expr, place)) return true;
        if (self.rewrittenThroughInitializer(place)) |rewritten| {
            if (self.provesAtCalleeEntry(receiver_expr, rewritten)) return true;
        }
        return self.preservedFromEntry(receiver_expr, place, true, true);
    }

    /// Can nothing that runs between the entry of the declaration that owns
    /// `use_node` and the use itself invalidate `place`?
    ///
    /// This is the point query with the establishment switched off: a statement
    /// that installs the place is not news here, because whatever the caller
    /// passed in already carried it, while a statement that clears it or a call
    /// this scan cannot read destroys what the caller established. Reaching the
    /// declaration's own scope unharmed is the answer that matters, because
    /// that scope is the state the caller handed over. `at_callee_entry` says
    /// the use is a call's receiver, so that call's own arguments fall inside
    /// the span this walk reads.
    fn preservedFromEntry(
        self: Solver,
        use_node: u32,
        place: Path,
        credit_calls: bool,
        at_callee_entry: bool,
    ) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        var current = use_node;
        var boundary = use_node;
        var depth: u32 = 0;
        while (depth < 64) : (depth += 1) {
            var level = LevelVerdict{};
            const block = self.containingBlock(current) orelse return true;
            self.readLevel(block, boundary, place, credit_calls, false, at_callee_entry, &level);
            if (level.decided) return level.safe;
            const parent = self.query.lexical.parent(current) orelse return true;
            if (parent == 0 or parent >= tags.len) return true;
            // An enclosing condition only adds to what the body already holds,
            // so the declaration boundary is where this walk answers.
            if (tags[parent] == .fn_decl or tags[parent] == .test_decl) return true;
            boundary = block;
            current = block;
        }
        return false;
    }

    /// The bare `anytype` parameter an expression reads: the declaration that
    /// owns it, the token that names it, and the position the prototype writes
    /// it at.
    ///
    /// Zig records an `anytype` parameter as a token rather than a node, so the
    /// lexical index registers nothing for it: the parameter has to be read out
    /// of the prototype that owns the use, and the prototype's own iteration is
    /// in the order the parameters are written, which is the order a call passes
    /// them in. `scan(value: u8, sink: anytype)` hands its second argument to
    /// `sink`, and `relay(tag: anytype, target: *Sink, mode: anytype)` hands its
    /// second argument to the typed parameter its own list records first.
    const UntypedParameter = struct { function: u32, index: usize, name_token: u32 };

    /// The bare parameter this expression names, or null for every other object
    /// a receiver may be.
    ///
    /// A receiver is the object a call reads a field of, so only a name the
    /// declaration around it leaves untyped can be one.
    fn untypedParameterOf(self: Solver, expr: u32) ?UntypedParameter {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        var node = expr;
        var depth: u32 = 0;
        while (depth < 8) : (depth += 1) {
            if (node == 0 or node >= tags.len) return null;
            switch (tags[node]) {
                .identifier => return self.bareParameterNamed(node, tree.nodes.items(.main_token)[node]),
                .grouped_expression => node = @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]),
                .@"comptime" => node = @intFromEnum(tree.nodes.items(.data)[node].node),
                else => return null,
            }
        }
        return null;
    }

    /// The parameter the prototype around `use_node` leaves bare and spells as
    /// `name`, which is the name `use_node` itself is written with.
    ///
    /// A name the index resolves to a declaration of its own is that
    /// declaration: a local that shadows the parameter and a typed parameter are
    /// both read from the prototype's own iteration here, and neither of them is
    /// left bare. A bare parameter is the one name whose use resolves to nothing
    /// at all, which is what makes the prototype the only place it can be read.
    fn bareParameterNamed(self: Solver, use_node: u32, name: u32) ?UntypedParameter {
        const tree = self.query.tree;
        if (name >= tree.tokens.len or tree.tokenTag(name) != .identifier) return null;
        if (self.query.resolveIdentifierBinding(use_node) != null) return null;
        const function = constructor_facts.enclosingFunction(self.query, use_node) orelse return null;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = constructor_facts.treeFnProto(tree, function, &buffer) orelse return null;
        const spelling = import_resolver.normalizeIdentifier(tree.tokenSlice(name));
        var index: usize = 0;
        var params = proto.iterate(tree);
        while (params.next()) |param| : (index += 1) {
            // A typed parameter takes an argument of its own type, and `...`
            // takes the rest of them: neither is an object a receiver names.
            if (param.type_expr != null) continue;
            const declared = param.name_token orelse continue;
            if (declared >= tree.tokens.len or tree.tokenTag(declared) != .identifier) continue;
            if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(declared)), spelling)) continue;
            return .{ .function = function, .index = index, .name_token = @intCast(declared) };
        }
        return null;
    }

    /// Is every reference to this function the callee of a call?
    ///
    /// A generic function is instantiated by the calls that reach it, so the
    /// contexts this file reads are all of them only while the name is never
    /// handed around. A reference that is not a call — a value stored, a name
    /// passed as an argument — leaves instantiations this file never sees, and
    /// those reach the same untyped receiver.
    fn everyReferenceIsACall(self: Solver, function: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const name = self.fieldName(methodNameToken(tree, function) orelse return false);
        var node: u32 = 1;
        while (node < tags.len) : (node += 1) {
            if (tags[node] != .identifier) continue;
            if (!std.mem.eql(u8, self.fieldName(tree.nodes.items(.main_token)[node]), name)) continue;
            if (self.isCalleeOfACall(node)) continue;
            return false;
        }
        return true;
    }

    fn isCalleeOfACall(self: Solver, node: u32) bool {
        const tree = self.query.tree;
        const parent = self.query.lexical.parent(node) orelse return false;
        if (!isCallTag(tree.nodeTag(@enumFromInt(parent)))) return false;
        const call = fullCall(tree, parent) orelse return false;
        return @intFromEnum(call.ast.fn_expr) == node;
    }

    /// Can any parameter but the one being mapped name the receiver this proof
    /// is about?
    ///
    /// A generic function is handed whatever its instantiation passes, so a
    /// second bare parameter could be handed the object itself and a typed one
    /// could be a pointer to it. Only a prototype whose every other parameter is
    /// spelled with a type that cannot reach the receiver keeps the mapping
    /// honest, and one this scan cannot read does not.
    fn otherParametersCannotNameReceiver(self: Solver, function: u32, receiver: usize, method: u32) bool {
        const tree = self.query.tree;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = constructor_facts.treeFnProto(tree, function, &buffer) orelse return false;
        var index: usize = 0;
        var params = proto.iterate(tree);
        while (params.next()) |param| : (index += 1) {
            if (index == receiver) continue;
            // A parameter left bare carries whatever the instantiation passes,
            // and one written without a name is one no body can even see:
            // neither is a type this walk can rule out.
            const type_expr = param.type_expr orelse return false;
            if (param.name_token == null) return false;
            const written = constructor_facts.parameterTypeNode(tree, @intFromEnum(type_expr)) orelse return false;
            if (written == 0 or written >= tree.nodes.len) return false;
            if (self.typeMayNameReceiver(written, method, 0)) return false;
        }
        return true;
    }

    /// Does this call reach exactly this declaration?
    fn callReachesFunction(self: Solver, call_node: u32, function: u32) bool {
        if (self.calleeAtCall(call_node)) |resolved| return resolved == function;
        const tree = self.query.tree;
        const call = fullCall(tree, call_node) orelse return false;
        const fn_expr = @intFromEnum(call.ast.fn_expr);
        if (fn_expr >= tree.nodes.len or tree.nodeTag(@enumFromInt(fn_expr)) != .identifier) return false;
        const candidate = self.resolvePlainFunction(fn_expr) orelse return false;
        return self.declarationOfPrototype(candidate) == self.declarationOfPrototype(function);
    }

    /// The object an argument hands over, or null for anything else.
    ///
    /// `&sink` and `sink` both name the storage the callee receives, while a
    /// value read out of one is a copy that carries nothing.
    fn addressedOperand(self: Solver, expr: u32) ?u32 {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var node = expr;
        var depth: u32 = 0;
        while (depth < 8) : (depth += 1) {
            if (node == 0 or node >= tags.len) return null;
            switch (tags[node]) {
                .address_of => node = @intFromEnum(datas[node].node),
                .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
                .@"comptime" => node = @intFromEnum(datas[node].node),
                else => return node,
            }
        }
        return null;
    }

    /// The declaration a name reaches through the object `expr` names, read
    /// from that object's own declared type rather than from the spelling.
    fn memberDeclaration(self: Solver, expr: u32, name: []const u8) ?u32 {
        const tree = self.query.tree;
        const resolved = self.resolvedExprType(expr) orelse return null;
        const container = resolved.container_node orelse return null;
        if (container >= tree.nodes.len) return null;
        var container_buffer: [2]std.zig.Ast.Node.Index = undefined;
        const full = tree.fullContainerDecl(&container_buffer, @enumFromInt(container)) orelse return null;
        for (full.ast.members) |member| {
            const decl = @intFromEnum(member);
            var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
            const proto = constructor_facts.treeFnProto(tree, decl, &proto_buffer) orelse continue;
            const proto_name = proto.name_token orelse continue;
            if (!std.mem.eql(u8, self.fieldName(proto_name), name)) continue;
            return self.declarationOfPrototype(decl);
        }
        return null;
    }

    // -----------------------------------------------------------------
    // The point query both proofs are built from
    // -----------------------------------------------------------------

    /// Walks outward from `use_node` and reports whether `place` is non-null
    /// there.
    ///
    /// One traversal answers the whole question because the items it passes are
    /// exactly the ones that run after the innermost guard and before the use:
    /// each level contributes its enclosing condition first and then its own
    /// preceding statements, an inner level overrides every outer one because
    /// it runs later, and within a level the last decisive statement wins. A
    /// teardown followed by a replacement installation is therefore safe, while
    /// the reverse order is not.
    fn provesAtPoint(self: Solver, use_node: u32, place: Path) bool {
        return self.provesAtPointFrom(use_node, place, true, false);
    }

    /// The same question asked at the entry of the call the boundary names.
    ///
    /// A caller establishes a field for the callee, not for the receiver it
    /// wrote the call with: Zig evaluates the receiver, then every argument,
    /// and only then enters the body. So the arguments run ahead of the point
    /// the proof is about even though the receiver runs ahead of them, and
    /// `self.readAfter(self.clear())` hands the callee the null `clear` put
    /// back rather than what the caller's own guard proved. A use written
    /// inside the callee expression is the opposite question and keeps the
    /// ordinary reading, where those arguments have not run yet.
    fn provesAtCalleeEntry(self: Solver, use_node: u32, place: Path) bool {
        return self.provesAtPointFrom(use_node, place, true, true);
    }

    /// The same question with the answers a call carries switched off.
    ///
    /// Judging where a callee leaves a field asks what the statements before
    /// its own `return` prove, and such a statement can be a call. Following
    /// that call would re-enter the callee whose exit is under judgement, so
    /// this form reads only the conditions and the writes naming the place.
    fn provesPlaceWithoutCalls(self: Solver, use_node: u32, place: Path) bool {
        return self.provesAtPointFrom(use_node, place, false, false);
    }

    fn provesAtPointFrom(
        self: Solver,
        use_node: u32,
        place: Path,
        credit_calls: bool,
        at_callee_entry: bool,
    ) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        var current = use_node;
        var boundary = use_node;
        var depth: u32 = 0;
        while (depth < 64) : (depth += 1) {
            var level = LevelVerdict{};

            if (self.query.lexical.parent(current)) |parent| {
                if (parent == 0 or parent >= tags.len) return false;
                if (tags[parent] == .fn_decl or tags[parent] == .test_decl) return false;
                if (self.conditionProvesPlaceNonNull(parent, use_node, place)) {
                    level = .{ .decided = true, .safe = true };
                }
            }
            const block = self.containingBlock(current) orelse return level.safe;
            self.readLevel(block, boundary, place, credit_calls, true, at_callee_entry, &level);
            if (level.decided) return level.safe;

            boundary = block;
            current = block;
        }
        return false;
    }

    /// The statements of `block` that have run by the time its boundary does,
    /// read into the level's verdict.
    ///
    /// `decide_installs` switches the establishment answer off, which is what a
    /// generic parameter needs: whatever the caller handed over is already
    /// installed, so only a statement that destroys the place is news there.
    fn readLevel(
        self: Solver,
        block: u32,
        boundary: u32,
        place: Path,
        credit_calls: bool,
        decide_installs: bool,
        at_callee_entry: bool,
        level: *LevelVerdict,
    ) void {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        if (boundary >= tags.len) return;

        var block_buffer: [2]u32 = undefined;
        const statements = ast_walk.getBlockStatements(tree, block, &block_buffer) orelse return;
        // A statement's place in a block is where it opens, not where its own
        // keyword sits. A call's main token is its `(`, and the main token of
        // `a.b = c` is its `=`, so a boundary written in the receiver or on the
        // left of an assignment runs ahead of the token the old comparison
        // measured against — and a statement holding one is then stepped over
        // whole, taking every operand that statement evaluates first with it.
        const limit = tree.firstToken(@enumFromInt(boundary));
        for (statements) |statement| {
            if (statement >= tags.len) continue;
            // A statement that opens at the boundary's own first token is a
            // statement the boundary sits inside, and it has to be read for
            // the operands ahead of it — that is the receiver of
            // `self.add(self.wipe())`, where the argument is what the callee
            // is entered with. Only a statement that starts after the
            // boundary cannot hold it, so the walk stops there.
            if (tree.firstToken(@enumFromInt(statement)) > limit) break;
            // A body registered by a `defer` or `errdefer` of this very scope
            // has not run yet: the scope is still open at the guarded point.
            if (tags[statement] == .@"defer" or tags[statement] == .@"errdefer") continue;
            // A statement the boundary sits inside has not finished running:
            // whatever follows the boundary in it happens later. What runs
            // before it has already run, though, and no other level reads it:
            // the level the boundary is in starts from the statement the
            // boundary belongs to and never looks inside an operand that is
            // evaluated ahead of it, so a mutation there outruns a guard this
            // level read a statement earlier. At the entry of the call the
            // boundary names, its arguments belong to that earlier set.
            if (containsNode(tree, statement, boundary)) {
                self.readPrecedingOperands(statement, boundary, place, credit_calls, decide_installs, at_callee_entry, level);
                continue;
            }
            if (decide_installs and self.statementInstallsPlace(statement, place, credit_calls)) {
                level.decided = true;
                level.safe = true;
                continue;
            }
            if (self.statementMayInvalidatePlace(statement, place, credit_calls)) {
                level.decided = true;
                level.safe = false;
            }
        }
    }

    /// The operands the statement holding `boundary` runs before it, read into
    /// the level's verdict in the order they run.
    ///
    /// Zig evaluates the operands of an expression left to right and reaches a
    /// call only after the last of them, so an argument a call passes and an
    /// element a tuple literal holds have both run by the time the expression
    /// around them does. Reading the statement whole would credit a teardown
    /// written after the boundary as well, and that one runs too late to
    /// matter, so only the operands ahead of it are read here.
    fn readPrecedingOperands(
        self: Solver,
        statement: u32,
        boundary: u32,
        place: Path,
        credit_calls: bool,
        decide_installs: bool,
        at_callee_entry: bool,
        level: *LevelVerdict,
    ) void {
        var operands = PrecedingOperands{ .tree = self.query.tree, .boundary = boundary };
        self.collectPrecedingOperands(statement, boundary, at_callee_entry, &operands);
        // An operand list this scan cannot hold is one it cannot read, and what
        // it cannot read is a mutation it cannot rule out.
        if (operands.truncated) {
            level.decided = true;
            level.safe = false;
            return;
        }
        for (operands.items[0..operands.len]) |operand| {
            if (decide_installs and self.statementInstallsPlace(operand, place, credit_calls)) {
                level.decided = true;
                level.safe = true;
                continue;
            }
            if (self.statementMayInvalidatePlace(operand, place, credit_calls)) {
                level.decided = true;
                level.safe = false;
            }
        }
    }

    /// The operands ahead of the boundary, listed from the outside in so that
    /// the list is in the order the language evaluates them.
    ///
    /// A nested block ends the walk: its statements are the ones the level the
    /// boundary is in already reads, and reading them a second time here would
    /// let a guard one of them established outrank the teardown that follows it
    /// inside the block.
    fn collectPrecedingOperands(
        self: Solver,
        statement: u32,
        boundary: u32,
        at_callee_entry: bool,
        operands: *PrecedingOperands,
    ) void {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        var path: [16]u32 = undefined;
        var len: usize = 0;
        var current = boundary;
        while (current != statement and current != 0 and len < path.len) {
            const parent = self.query.lexical.parent(current) orelse return;
            if (parent == 0 or parent >= tags.len) return;
            path[len] = parent;
            len += 1;
            current = parent;
        }
        if (current != statement) return;

        var index = len;
        while (index > 0) {
            index -= 1;
            const parent = path[index];
            switch (tags[parent]) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => return,
                else => {},
            }
            // A call the boundary is written inside has already run all of its
            // operands by the time it reaches its own body, so at that entry
            // every one of them is in the past: the receiver it was written on,
            // and the arguments evaluated after it alike. Anywhere else in the
            // expression the boundary is a use that happens while those
            // arguments are still to come, and only the ones ahead of it have
            // run.
            operands.callee = at_callee_entry and isCallTag(tags[parent]);
            operands.passed = false;
            ast_walk.walkChildren(PrecedingOperands, tree, parent, operands, PrecedingOperands.visit) catch return;
        }
    }

    /// The operands of one node, kept only while they still run ahead of the
    /// boundary.
    const PrecedingOperands = struct {
        tree: *const std.zig.Ast,
        boundary: u32,
        /// Set once an operand holding the boundary has been passed, which is
        /// where evaluation overtakes it.
        passed: bool = false,
        /// Whether the node being read is a call the boundary is written
        /// inside, so every operand it holds has run by the time its body
        /// starts.
        callee: bool = false,
        items: [12]u32 = undefined,
        len: usize = 0,
        /// Set when an operand was dropped for want of room, which leaves the
        /// list incomplete and the order it claims unverifiable.
        truncated: bool = false,

        fn visit(_: *const std.zig.Ast, operand: u32, self: *PrecedingOperands) !void {
            if (!self.callee and self.passed) return;
            if (operand == 0 or operand >= self.tree.nodes.len) return;
            if (containsNode(self.tree, operand, self.boundary)) {
                self.passed = true;
                return;
            }
            if (self.len == self.items.len) {
                self.truncated = true;
                return;
            }
            self.items[self.len] = operand;
            self.len += 1;
        }
    };

    /// Does the construct directly holding `use_node` enter this branch only
    /// while `place` is non-null?
    fn conditionProvesPlaceNonNull(self: Solver, parent: u32, use_node: u32, place: Path) bool {
        const tree = self.query.tree;
        switch (tree.nodeTag(@enumFromInt(parent))) {
            .@"if", .if_simple => {
                const full = tree.fullIf(@enumFromInt(parent)) orelse return false;
                const condition = @intFromEnum(full.ast.cond_expr);
                if (containsNode(tree, @intFromEnum(full.ast.then_expr), use_node)) {
                    return self.conditionProvesPlace(condition, true, place);
                }
                const else_node = full.ast.else_expr.unwrap() orelse return false;
                if (!containsNode(tree, @intFromEnum(else_node), use_node)) return false;
                return self.conditionProvesPlace(condition, false, place);
            },
            .@"while", .while_simple, .while_cont => {
                const full = tree.fullWhile(@enumFromInt(parent)) orelse return false;
                if (!containsNode(tree, @intFromEnum(full.ast.then_expr), use_node)) return false;
                return self.conditionProvesPlace(@intFromEnum(full.ast.cond_expr), true, place);
            },
            else => return false,
        }
    }

    // -----------------------------------------------------------------
    // Statements
    // -----------------------------------------------------------------

    /// A statement can only install `place` by naming it — through a binding
    /// that constructs the object, an assignment of a value that cannot be
    /// null, or a call that only succeeds after the write.
    fn statementInstallsPlace(self: Solver, statement: u32, place: Path, credit_calls: bool) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (statement >= tags.len) return false;
        switch (tags[statement]) {
            .simple_var_decl, .local_var_decl, .aligned_var_decl, .global_var_decl => {
                const full = tree.fullVarDecl(@enumFromInt(statement)) orelse return false;
                // The facts describe the value this declaration holds, so they
                // answer for the place only when this is the binding the place
                // is measured from: a constructor call that initialised some
                // other local says nothing about an object it never saw.
                if (full.ast.mut_token + 1 != place.root) return false;
                const init = full.ast.init_node.unwrap() orelse return false;
                return self.ownerFacts(@intFromEnum(init), 0).holds(place.slice());
            },
            .@"if", .if_simple => {
                // `if (place == null) return;` leaves the scope only while the
                // field is null, so the code after it sees a non-null one.
                const full = tree.fullIf(@enumFromInt(statement)) orelse return false;
                if (full.ast.else_expr.unwrap() != null) return false;
                if (full.payload_token != null) return false;
                if (!self.conditionProvesNull(@intFromEnum(full.ast.cond_expr), place)) return false;
                return guards.handlerPreventsCompletion(tree, @intFromEnum(full.ast.then_expr), tags, datas);
            },
            .@"try" => {
                const inner = @intFromEnum(datas[statement].node);
                return self.statementInstallsPlace(inner, place, credit_calls) or
                    (credit_calls and self.callInstallsPlace(inner, place));
            },
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
                const lhs = @intFromEnum(datas[statement].node_and_node[0]);
                const rhs = @intFromEnum(datas[statement].node_and_node[1]);
                return self.assignmentInstalls(lhs, rhs, place);
            },
            .call, .call_comma, .call_one, .call_one_comma => return credit_calls and self.callInstallsPlace(statement, place),
            else => return false,
        }
    }

    /// Does writing `lhs = rhs` leave `place` non-null?
    ///
    /// Two names for one object install the same field, so the write is
    /// compared after following the file's aliases. A write to a different
    /// object installs nothing here; the invalidation scan is what has to
    /// judge that one.
    fn assignmentInstalls(self: Solver, lhs: u32, rhs: u32, place: Path) bool {
        const target = self.storagePlace(lhs) orelse return false;
        if (self.aliasRoot(target.root, 0) != self.aliasRoot(place.root, 0)) return false;
        if (!isPrefixOf(target.slice(), place.slice())) return false;
        if (target.len == place.len) return self.storesNonNull(rhs, 0);
        // A containing object: the field below it has to come from the new
        // value, so only the new value's own facts decide.
        const tail = place.slice()[target.len..];
        return self.ownerFacts(rhs, 0).holds(tail);
    }

    fn callInstallsPlace(self: Solver, call_node: u32, place: Path) bool {
        if (self.callEffectOnPlace(call_node, place, 0) != .installs) return false;
        // A `try` leaves the enclosing scope when the call fails, so the code
        // after it only ever runs on the success path the effect describes.
        if (self.query.lexical.parent(call_node)) |parent| {
            if (parent != 0 and self.query.tree.nodeTag(@enumFromInt(parent)) == .@"try") return true;
        }
        // An installer that cannot fail always reaches the end of its scope.
        return !self.calleeIsFallible(call_node);
    }

    /// Can the call fail?
    ///
    /// The answer is a property of the declaration the call reaches, so it is
    /// read from the receiver's own type: a call this scan cannot attribute to
    /// one declaration of this file may fail in any way, and says so.
    fn calleeIsFallible(self: Solver, call_node: u32) bool {
        const tree = self.query.tree;
        const resolved = self.calleeAtCall(call_node) orelse return true;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = constructor_facts.treeFnProto(tree, resolved, &buffer) orelse return true;
        const return_type = proto.ast.return_type.unwrap() orelse return true;
        return tree.nodeTag(return_type) == .error_union;
    }

    fn statementMayInvalidatePlace(self: Solver, statement: u32, place: Path, credit_calls: bool) bool {
        return self.statementInvalidatesPlace(statement, place, credit_calls, 0);
    }

    /// The same question asked from inside a body this file reaches through a
    /// call, where `depth` says how many such hops already ran.
    ///
    /// Two methods that call each other are a cycle rather than a chain of
    /// facts, so the depth the caller reads is handed to every call the body
    /// makes rather than restarted; the bound `callEffectOnPlace` applies is
    /// the one that ends the walk.
    fn statementInvalidatesPlace(self: Solver, statement: u32, place: Path, credit_calls: bool, depth: u32) bool {
        const tree = self.query.tree;
        const Visitor = struct {
            query: *const QueryContext,
            solver: Solver,
            place: Path,
            credit_calls: bool,
            depth: u32,
            found: bool = false,
            stop: bool = false,

            pub fn visit(visitor: *@This(), _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
                if (visitor.found) return;
                const datas = visitor.query.tree.nodes.items(.data);
                switch (tag) {
                    .@"asm", .asm_simple => {
                        visitor.found = true;
                        visitor.stop = true;
                    },
                    .address_of => {
                        if (visitor.solver.writeMayReach(@intFromEnum(datas[node].node), visitor.place.root, visitor.place.slice())) {
                            visitor.found = true;
                            visitor.stop = true;
                        }
                    },
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
                        if (visitor.solver.writeMayReach(@intFromEnum(datas[node].node_and_node[0]), visitor.place.root, visitor.place.slice())) {
                            visitor.found = true;
                            visitor.stop = true;
                        }
                    },
                    .assign_destructure => {
                        const full = visitor.solver.query.tree.assignDestructure(@enumFromInt(node));
                        for (full.ast.variables) |variable| {
                            if (visitor.solver.writeMayReach(@intFromEnum(variable), visitor.place.root, visitor.place.slice())) {
                                visitor.found = true;
                                visitor.stop = true;
                                return;
                            }
                        }
                    },
                    .call, .call_comma, .call_one, .call_one_comma => {
                        if (!visitor.credit_calls) return;
                        if (visitor.solver.callEffectOnPlace(node, visitor.place, visitor.depth) == .invalidated) {
                            visitor.found = true;
                            visitor.stop = true;
                        }
                    },
                    .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                        var buffer: [2]std.zig.Ast.Node.Index = undefined;
                        const params = visitor.query.tree.builtinCallParams(&buffer, @enumFromInt(node)) orelse {
                            if (visitor.solver.mentionsObject(node, visitor.place.root)) {
                                visitor.found = true;
                                visitor.stop = true;
                            }
                            return;
                        };
                        for (params) |param| {
                            if (visitor.solver.writeMayReach(@intFromEnum(param), visitor.place.root, visitor.place.slice())) {
                                visitor.found = true;
                                visitor.stop = true;
                                return;
                            }
                        }
                    },
                    else => {},
                }
            }
        };

        var visitor = Visitor{ .query = self.query, .solver = self, .place = place, .credit_calls = credit_calls, .depth = depth };
        ast_walk.walk(Visitor, tree, statement, &visitor) catch return true;
        return visitor.found;
    }

    // -----------------------------------------------------------------
    // Conditions
    // -----------------------------------------------------------------

    /// Does `condition` holding `assumed` prove `place` non-null?
    fn conditionProvesPlace(self: Solver, condition: u32, assumed: bool, place: Path) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (condition >= tags.len) return false;
        switch (tags[condition]) {
            .grouped_expression => return self.conditionProvesPlace(
                @intFromEnum(datas[condition].node_and_token[0]),
                assumed,
                place,
            ),
            .@"comptime" => return self.conditionProvesPlace(
                @intFromEnum(datas[condition].node),
                assumed,
                place,
            ),
            .bool_not => return self.conditionProvesPlace(@intFromEnum(datas[condition].node), !assumed, place),
            // A conjunction holds both of its parts, so either one is enough; a
            // disjunction proves neither, because either arm may be the one
            // that was taken.
            .bool_and => {
                if (!assumed) return false;
                return self.conditionProvesPlace(@intFromEnum(datas[condition].node_and_node[0]), true, place) or
                    self.conditionProvesPlace(@intFromEnum(datas[condition].node_and_node[1]), true, place);
            },
            .bool_or => return false,
            else => {},
        }
        const check = self.nullCheck(condition, assumed) orelse return false;
        return check.positive and self.placeMatches(check.expr, place);
    }

    /// Does `condition` holding prove `place` null?
    fn conditionProvesNull(self: Solver, condition: u32, place: Path) bool {
        const check = self.nullCheck(condition, true) orelse return false;
        return !check.positive and self.placeMatches(check.expr, place);
    }

    const NullCheck = struct { expr: u32, positive: bool };

    /// The plain null-test shapes only: `e`, `e == null`, `e != null` and their
    /// negations. Anything else decides nothing at this point.
    fn nullCheck(self: Solver, condition: u32, truth: bool) ?NullCheck {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (condition >= tags.len) return null;
        switch (tags[condition]) {
            .identifier, .field_access => return .{ .expr = condition, .positive = truth },
            .equal_equal, .bang_equal => {
                const lhs = @intFromEnum(datas[condition].node_and_node[0]);
                const rhs = @intFromEnum(datas[condition].node_and_node[1]);
                const negated = tags[condition] == .equal_equal;
                if (isNullLiteral(tree, rhs)) return .{ .expr = lhs, .positive = truth != negated };
                if (isNullLiteral(tree, lhs)) return .{ .expr = rhs, .positive = truth != negated };
                return null;
            },
            .bool_not => return self.nullCheck(@intFromEnum(datas[condition].node), !truth),
            else => return null,
        }
    }

    // -----------------------------------------------------------------
    // Places
    // -----------------------------------------------------------------

    fn storagePlace(self: Solver, expr: u32) ?Path {
        var result = Path{};
        if (!self.buildPlace(expr, &result)) return null;
        return result;
    }

    fn buildPlace(self: Solver, expr: u32, out: *Path) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (expr == 0 or expr >= tags.len or out.len >= max_depth) return false;
        switch (tags[expr]) {
            .identifier => {
                // A parameter the prototype leaves bare is a token rather than a
                // node, so the lexical index registers nothing for it and a use
                // of its name resolves to no declaration at all. The prototype
                // that owns the use is what names it, and that name is the root
                // every write the body spells on it lands on — which is what
                // makes the object a caller handed the generic function the one
                // this walk has to keep the field on.
                const root = self.query.resolveIdentifierBinding(expr) orelse blk: {
                    const bare = self.bareParameterNamed(expr, tree.nodes.items(.main_token)[expr]) orelse return false;
                    break :blk bare.name_token;
                };
                if (root == 0 or out.len != 0) return false;
                out.root = root;
                return true;
            },
            .field_access => {
                if (!self.buildPlace(@intFromEnum(datas[expr].node_and_token[0]), out)) return false;
                out.names[out.len] = self.fieldName(datas[expr].node_and_token[1]);
                out.len += 1;
                return true;
            },
            else => return false,
        }
    }

    fn fieldName(self: Solver, token: u32) []const u8 {
        return import_resolver.normalizeIdentifier(self.query.tree.tokenSlice(token));
    }

    fn placeMatches(self: Solver, expr: u32, place: Path) bool {
        const candidate = self.storagePlace(expr) orelse return false;
        return samePath(candidate, place);
    }

    /// Does `expr` design `place`, or an object that contains it?
    ///
    /// This is the question for an expression the callee only reads: a value
    /// handed to a call is a copy, so it cannot put a null back into the slot
    /// it was read from, and the place it names is the whole of the answer.
    fn placeReaches(self: Solver, expr: u32, place: Path) bool {
        return self.writeReaches(expr, place.root, place.slice());
    }

    /// May a write spelled through `expr` reach the place named by `root` and
    /// `names`?
    ///
    /// Two names for one object are compared after following the file's own
    /// aliases, so `var me = self; me.field = null` is recognised as a write to
    /// `self.field` rather than as an unrelated local. A name that holds an
    /// alias of *some* field of another object could reach any of its fields,
    /// so the answer stays conservative.
    ///
    /// A second pointer parameter is the other name for an object this file
    /// cannot rule out: the caller may have passed the receiver in twice. Once
    /// that is settled the write is compared against the guarded path the same
    /// way a write on the receiver's own name is, which is
    /// `foreignWriteReaches`.
    ///
    /// A write this scan cannot spell as a place — `me.*.field`,
    /// `slots[0].field`, `self.slots[0]` — is still a write, and answering "no"
    /// for one would clear a warning on a path that does reach the field. What
    /// is left to decide about such an expression is whether it names the
    /// object at all, which is what `mentionsObject` answers.
    fn writeMayReach(self: Solver, expr: u32, root: u32, names: []const []const u8) bool {
        const written = self.storagePlace(expr) orelse return self.mentionsObject(expr, root);
        return self.reachedPlaceReaches(written, root, names);
    }

    fn writeReaches(self: Solver, expr: u32, root: u32, names: []const []const u8) bool {
        const written = self.storagePlace(expr) orelse return false;
        return self.reachedPlaceReaches(written, root, names);
    }

    fn reachedPlaceReaches(self: Solver, written: Path, root: u32, names: []const []const u8) bool {
        if (self.aliasRoot(written.root, 0) == self.aliasRoot(root, 0)) {
            const spelled = self.writtenThroughAlias(written);
            if (isPrefixOf(spelled.slice(), names)) return true;
            // Two fields of one `struct` hold bytes of their own, so a write
            // to one says nothing about the other. A `union` lays every
            // member over the same bytes, so a write to one member is a write
            // to every member and the guarded one is among them.
            return self.siblingFieldsShareStorage(spelled.slice(), names, root);
        }
        return self.foreignWriteReaches(written, root, names);
    }

    /// The place a write spelled under a by-value copy of one of the guarded
    /// object's own members really designates.
    ///
    /// `const copy = box.flags;` makes `copy.cell.value` the storage
    /// `box.flags.cell.value` names. `aliasRoot` already follows the copy to
    /// `box`, so the two roots compare equal — but the member the initializer
    /// walked (`flags`) is the one name the write does not spell, and the two
    /// paths compared as written call themselves apart. Putting the alias
    /// chain's own members in front of the written ones is what makes them the
    /// same path again. A copy whose initializer names no member contributes
    /// nothing, so `var me = self; me.field = null` keeps the path it has.
    ///
    /// A chain longer than one place can hold keeps the path it was given,
    /// which is the reading the comparison had before.
    fn writtenThroughAlias(self: Solver, written: Path) Path {
        var hop_names: [max_depth][max_depth][]const u8 = undefined;
        var hop_lens: [max_depth]usize = undefined;
        var hops: usize = 0;
        var complete = true;
        var current = written.root;
        var depth: u32 = 0;
        while (depth < 8) : (depth += 1) {
            if (hops == max_depth) {
                complete = false;
                break;
            }
            const init = self.aliasInitializer(current) orelse break;
            if (self.query.lexical.enclosingFunction(self.query.firstToken(init)) !=
                self.query.lexical.enclosingFunction(current)) break;
            const aliased = self.placeOfAliasInitializer(init) orelse break;
            if (aliased.root == current) break;
            current = aliased.root;
            if (aliased.len == 0) continue;
            @memcpy(hop_names[hops][0..aliased.len], aliased.slice());
            hop_lens[hops] = aliased.len;
            hops += 1;
        }

        var total: usize = 0;
        for (hop_lens[0..hops]) |hop| total += hop;
        if (!complete or total == 0 or written.len + total > max_depth) return written;

        var names: [max_depth][]const u8 = undefined;
        var at: usize = 0;
        var hop = hops;
        while (hop > 0) {
            hop -= 1;
            const end = at + hop_lens[hop];
            @memcpy(names[at..end], hop_names[hop][0..hop_lens[hop]]);
            at = end;
        }
        const written_end = at + written.len;
        @memcpy(names[at..written_end], written.slice());
        var result = written;
        result.names = names;
        result.len = written_end;
        return result;
    }

    /// Does a write to `written` land on the bytes `names` names because the
    /// object those are fields of is a `union`?
    ///
    /// Only the first name is compared, because the members a `union` lays
    /// over one another are the ones its own declaration lists: two different
    /// names at that top level are two views of the same bytes, while a
    /// difference further down says nothing about the storage this scan
    /// describes. An object whose declared type this file cannot read is not a
    /// `union` it can prove, so the fields of an ordinary `struct` stay
    /// disjoint exactly as they were.
    fn siblingFieldsShareStorage(self: Solver, written: []const []const u8, names: []const []const u8, root: u32) bool {
        if (written.len == 0 or names.len == 0) return false;
        if (std.mem.eql(u8, written[0], names[0])) return false;
        return self.bindingIsUnion(root);
    }

    /// May a write spelled on a name that is not the receiver's own land on the
    /// place `names` names inside the object `root`?
    ///
    /// Three different objects can be spelled by a write that is not spelled on
    /// the receiver, and they are asked about in that order: an alias of some
    /// other object's field could reach any of that object's fields, a second
    /// pointer parameter may be the receiver itself, and a global is the one
    /// object in a file a caller may have filled the receiver pointer with.
    /// Each says nothing about which bytes of the object the write lands on,
    /// so the two that name the object outright hand the write to the same
    /// path comparison the receiver's own name would have asked.
    fn foreignWriteReaches(self: Solver, written: Path, root: u32, names: []const []const u8) bool {
        if (self.aliasesAnotherField(written.root)) return true;
        if (self.parameterWriteReachesPlace(written, root, names)) return true;
        return self.globalWriteReachesPlace(written, root, names);
    }

    /// May a write spelled on storage this file holds at file or container scope
    /// land on the place `names` names inside the object `root`?
    ///
    /// A local owns bytes of its own and is read through `aliasRoot`, which
    /// follows what this file writes into it. A global is different in kind: it
    /// has an address a caller can take, and `session.read(sink)` takes it —
    /// filling the receiver pointer with `&session` while nothing in either
    /// body says so. A global whose declared type is the container that pointer
    /// names may therefore be the very object the receiver stands for, and the
    /// two paths are then compared the way `parameterWriteReachesPlace`
    /// compares the two names of one object.
    ///
    /// Both ends have to be types this file writes down. A receiver whose type
    /// it cannot read is not evidence that any global of any shape can be the
    /// object behind it: that answer would fire on every call in the file,
    /// which is the blanket this file does not give anywhere else.
    fn globalWriteReachesPlace(self: Solver, written: Path, receiver_root: u32, names: []const []const u8) bool {
        if (!self.bindingIsGlobalStorage(written.root)) return false;
        const written_container = self.bindingContainerNode(written.root) orelse return false;
        const receiver_container = self.receiverPointeeContainer(receiver_root) orelse return false;
        if (written_container != receiver_container) return false;
        return self.pathsMayShareStorage(written.slice(), names, written.root);
    }

    /// Is this name a declaration at file or container scope, whose address a
    /// caller may have handed to a pointer parameter?
    ///
    /// The lexical index records the function a declaration sits in, and a
    /// declaration no function sits in has no caller to fill it in one
    /// statement at a time.
    fn bindingIsGlobalStorage(self: Solver, root: u32) bool {
        const candidate = self.bindingForToken(root) orelse return false;
        return candidate.kind == .variable and candidate.function == null;
    }

    /// The container a pointer parameter points at, when this file declares
    /// both the parameter and what its pointer names.
    ///
    /// A receiver this file does not declare as a pointer has storage of its
    /// own, which no caller can hand out; a receiver whose type it cannot read
    /// is not one whose pointee any global can be.
    fn receiverPointeeContainer(self: Solver, root: u32) ?u32 {
        const candidate = self.bindingForToken(root) orelse return null;
        if (candidate.kind != .parameter) return null;
        const written = self.bindingTypeNode(root) orelse return null;
        const tree = self.query.tree;
        if (written >= tree.nodes.len) return null;
        switch (tree.nodeTag(@enumFromInt(written))) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                const pointer = tree.fullPtrType(@enumFromInt(written)) orelse return null;
                return self.typeNodeContainerNode(@intFromEnum(pointer.ast.child_type), 0);
            },
            else => return null,
        }
    }

    /// Do two field paths that may name one object reach the same bytes?
    ///
    /// A path that is a prefix of the other names the object the other one
    /// names, so writing through it writes the guarded field with it. Two
    /// fields of one `struct` hold bytes of their own, so two paths that part
    /// company at the top level reach none of each other, while a `union` lays
    /// every member over the same bytes. A path longer than one name walks
    /// through storage this scan does not read — a pointer stored in the object
    /// leads somewhere else entirely — and keeps the conservative answer, the
    /// way `parameterWriteReachesPlace` keeps it for the same shape.
    fn pathsMayShareStorage(self: Solver, written: []const []const u8, names: []const []const u8, root: u32) bool {
        if (written.len == 0) return true;
        if (isPrefixOf(written, names) or isPrefixOf(names, written)) return true;
        if (written.len > 1) return true;
        return !self.bindingIsStruct(root);
    }

    /// May a write spelled on a second pointer parameter land on the bytes the
    /// receiver holds at `names`, because the caller may have passed the
    /// receiver in twice?
    ///
    /// `parameterMayNameReceiver` settles which object the write is on, and
    /// says nothing about which bytes of it. Once two names may be one object,
    /// the write is a write to the receiver's own field path, and the question
    /// is the one a write spelled on the receiver's own name already asks: do
    /// the two paths name the same storage?
    ///
    /// Only one shape is answered from the paths, because it is the only one
    /// where both of them describe the same object: a single field spelled
    /// directly on the parameter. Two fields of a `struct` hold bytes of their
    /// own, so in `fn read(self: *Packet, alias: *Packet)` a body that guards
    /// `self.tag` and then writes `alias.seen` proves nothing either way about
    /// `tag` however alike the two parameters look — while a `union` lays
    /// every member over the same bytes, so a receiver whose container is one
    /// keeps the warning.
    ///
    /// Everything else keeps the conservative answer, because nothing about it
    /// compares two field paths:
    ///
    ///   * a write with no field path at all — `alias = other` — replaces
    ///     whatever the receiver holds, so it reaches whatever the receiver
    ///     holds;
    ///   * a path deeper than one name walks through a field this scan does
    ///     not read, and a pointer stored in the receiver's own object leads
    ///     somewhere else entirely: `alias.p.tag = null` clears the receiver's
    ///     tag whenever the caller hands in a holder whose `p` points at it,
    ///     whatever the two paths read like;
    ///   * a container this file cannot follow the receiver's type to is not a
    ///     `struct` this scan can prove, and not being able to disprove the
    ///     `union` that shares its members' bytes either.
    fn parameterWriteReachesPlace(self: Solver, written: Path, receiver_root: u32, names: []const []const u8) bool {
        if (!self.parameterMayNameReceiver(written.root, receiver_root)) return false;
        if (written.len != 1) return true;
        if (isPrefixOf(written.slice(), names) or isPrefixOf(names, written.slice())) return true;
        return !self.bindingIsStruct(receiver_root);
    }

    /// Is the object `root` names a `struct` whose layout keyword this file
    /// reads?
    ///
    /// A container that cannot be found this way — one declared in another
    /// file, one a bare `anytype` hides, one reached through an `opaque` —
    /// answers false, which is the direction that leaves the warning in place.
    fn bindingIsStruct(self: Solver, root: u32) bool {
        const container = self.bindingContainerNode(root) orelse return false;
        const tree = self.query.tree;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        const full = tree.fullContainerDecl(&buffer, @enumFromInt(container)) orelse return false;
        return std.mem.eql(u8, tree.tokenSlice(full.ast.main_token), "struct");
    }

    /// The container the binding `root` names, when this file declares both the
    /// binding and the type written in front of it.
    fn bindingContainerNode(self: Solver, root: u32) ?u32 {
        return self.typeNodeContainerNode(self.bindingTypeNode(root) orelse return null, 0);
    }

    /// Follows the shapes a pointer may be written behind to the container it
    /// names. A name written inside the container it denotes is matched
    /// against that container the same way `namedTypeMayNameReceiver` matches
    /// it, which is the only way a prototype's `*Packet` reaches the `Packet`
    /// it is declared in.
    ///
    /// The container a name denotes is a property of the name, not of where
    /// the name is written, so a name no container encloses — the type of a
    /// module-level `var session: Session = .{};` — is resolved through the
    /// declaration it names instead. That is the walk `typeNodeIsUnion` already
    /// takes from a name to the container behind it, so an alias and an
    /// unannotated declaration are followed the one way.
    fn typeNodeContainerNode(self: Solver, type_node: u32, depth: u32) ?u32 {
        if (depth >= 8 or type_node == 0 or type_node >= self.query.tree.nodes.len) return null;
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (call_resolver.isContainerTag(tags[type_node])) return type_node;
        switch (tags[type_node]) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                const pointer = tree.fullPtrType(@enumFromInt(type_node)) orelse return null;
                return self.typeNodeContainerNode(@intFromEnum(pointer.ast.child_type), depth + 1);
            },
            .optional_type => return self.typeNodeContainerNode(@intFromEnum(datas[type_node].node), depth + 1),
            .grouped_expression => return self.typeNodeContainerNode(@intFromEnum(datas[type_node].node_and_token[0]), depth + 1),
            .@"try", .@"comptime" => return self.typeNodeContainerNode(@intFromEnum(datas[type_node].node), depth + 1),
            // A binding with no annotation names its type through the literal
            // it was given, which is the whole of `var session = Session{};`.
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
                const literal = tree.fullStructInit(&buffer, @enumFromInt(type_node)) orelse return null;
                const written = literal.ast.type_expr.unwrap() orelse return null;
                return self.typeNodeContainerNode(@intFromEnum(written), depth + 1);
            },
            .identifier => {
                // The container that lexically encloses the name decides only
                // when it encloses it at all: `Self` resolves through the
                // container it is written in, while a module-level declaration
                // sits where no container does and the name's own declaration
                // is the whole of what it resolves to.
                const container = constructor_facts.enclosingContainer(self.query, type_node) orelse
                    return self.typeNodeContainerNode(self.declaredTypeNode(type_node) orelse return null, depth + 1);
                if (!constructor_facts.denotesContainer(self.query, type_node, container)) return null;
                return container;
            },
            else => return null,
        }
    }

    /// The type the binding `root` was written with, when this file declares it.
    ///
    /// A parameter the prototype records is the type it was written with:
    /// `state: *Overlap` gives the `*Overlap` node itself, which is not a
    /// declaration `fullVarDecl` can ever read. A local with no annotation is
    /// read through the initializer it was given, which is the only place
    /// `var session = Session{};` names the type it has.
    fn bindingTypeNode(self: Solver, root: u32) ?u32 {
        const tree = self.query.tree;
        const candidate = self.bindingForToken(root) orelse return null;
        return switch (candidate.kind) {
            .parameter => constructor_facts.parameterTypeNode(tree, candidate.node),
            .variable => blk: {
                const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return null;
                break :blk @intFromEnum(full.ast.type_node.unwrap() orelse
                    full.ast.init_node.unwrap() orelse return null);
            },
            .function => null,
        };
    }

    /// Is the object `root` names a `union`?
    ///
    /// The declaration the binding was written with is followed through the
    /// pointers, optionals and containers in front of it, and the container it
    /// reaches is read for its own layout keyword. A binding this file does
    /// not declare, or one whose type it cannot read, is not a `union` it can
    /// prove either way.
    fn bindingIsUnion(self: Solver, root: u32) bool {
        const written = self.bindingTypeNode(root) orelse return false;
        return self.typeNodeIsUnion(written, 0);
    }

    fn typeNodeIsUnion(self: Solver, type_node: u32, depth: u32) bool {
        if (depth >= 8 or type_node == 0 or type_node >= self.query.tree.nodes.len) return false;
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        switch (tags[type_node]) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                const pointer = tree.fullPtrType(@enumFromInt(type_node)) orelse return false;
                return self.typeNodeIsUnion(@intFromEnum(pointer.ast.child_type), depth + 1);
            },
            .optional_type => return self.typeNodeIsUnion(@intFromEnum(datas[type_node].node), depth + 1),
            .array_type => return self.typeNodeIsUnion(
                @intFromEnum(tree.arrayType(@enumFromInt(type_node)).ast.elem_type),
                depth + 1,
            ),
            .grouped_expression => return self.typeNodeIsUnion(
                @intFromEnum(datas[type_node].node_and_token[0]),
                depth + 1,
            ),
            .@"try", .@"comptime" => return self.typeNodeIsUnion(
                @intFromEnum(datas[type_node].node),
                depth + 1,
            ),
            .identifier => {
                const declared = self.declaredTypeNode(type_node) orelse return false;
                return self.typeNodeIsUnion(declared, depth + 1);
            },
            else => {
                if (!call_resolver.isContainerTag(tags[type_node])) return false;
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                const full = tree.fullContainerDecl(&buffer, @enumFromInt(type_node)) orelse return false;
                return std.mem.eql(u8, tree.tokenSlice(full.ast.main_token), "union");
            },
        }
    }

    /// The object a local binding names, following `var me = self;` and
    /// `const me = &self;` until the chain reaches a name this scan cannot read
    /// further. A binding that does not start from a place in its own function
    /// is its own object.
    fn aliasRoot(self: Solver, root: u32, depth: u32) u32 {
        if (depth >= 8 or root == 0) return root;
        const init = self.aliasInitializer(root) orelse return root;
        if (self.query.lexical.enclosingFunction(self.query.firstToken(init)) !=
            self.query.lexical.enclosingFunction(root)) return root;
        const aliased = self.placeOfAliasInitializer(init) orelse return root;
        if (aliased.root == root) return root;
        return self.aliasRoot(aliased.root, depth + 1);
    }

    /// Does this binding hold an alias of a field of some other object?
    fn aliasesAnotherField(self: Solver, root: u32) bool {
        const init = self.aliasInitializer(root) orelse return false;
        const written = self.placeOfAliasInitializer(init) orelse return false;
        if (written.len == 0) return false;
        return written.root != self.aliasRoot(root, 0);
    }

    /// May this name be the very object the receiver names?
    ///
    /// `aliasRoot` follows what this file writes — `var me = self;`,
    /// `const ref = &self;` — but a parameter is filled by whoever calls, and
    /// no line of the file is the assignment that made one pointer and the
    /// receiver the same object. `fn matches(self: *Packet, other: *Packet)`
    /// therefore keeps the two names apart however alike they look, and a write
    /// through `other` would be taken for a write to an unrelated local. The
    /// question is read from the parameter's own declared type instead, through
    /// the same walk `otherParametersCannotAlias` uses for a whole prototype:
    /// a parameter whose type can reach the receiver's container may be the
    /// receiver itself.
    ///
    /// Only a receiver a caller passes by pointer is asked about. A by-value
    /// receiver is a copy that owns storage of its own, which no other name can
    /// reach, and a name the lexical index records no declaration for is not a
    /// parameter this scan can attribute. A declared type this file cannot read —
    /// a bare `anytype` the instantiation decides — is not evidence of anything,
    /// so it answers the direction that keeps the warning.
    fn parameterMayNameReceiver(self: Solver, written_root: u32, receiver_root: u32) bool {
        const tree = self.query.tree;
        const candidate = self.bindingForToken(written_root) orelse return false;
        if (candidate.kind != .parameter) return false;
        const method = self.declaringFunction(receiver_root) orelse return true;
        const receiver = receiverNameToken(tree, method) orelse return false;
        if (receiver != receiver_root or !receiverIsSinglePointer(tree, method)) return false;
        const written = constructor_facts.parameterTypeNode(tree, candidate.node) orelse return true;
        if (written == 0 or written >= tree.nodes.len) return true;
        return self.typeMayNameReceiver(written, method, 0);
    }

    fn aliasInitializer(self: Solver, root: u32) ?u32 {
        const candidate = self.bindingForToken(root) orelse return null;
        if (candidate.kind != .variable) return null;
        const full = self.query.tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return null;
        return @intFromEnum(full.ast.init_node.unwrap() orelse return null);
    }

    /// The object an aliasing initializer names, without the field path, so
    /// that `me` and `self` compare equal and `ref` is recognised as a name for
    /// a field of some object.
    fn placeOfAliasInitializer(self: Solver, init: u32) ?Path {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        if (init >= tags.len) return null;
        var operand = init;
        if (tags[init] == .address_of) {
            operand = @intFromEnum(tree.nodes.items(.data)[init].node);
        }
        return self.storagePlace(operand);
    }

    /// Does `expr` read or write the object `root` names, through any spelling
    /// including one of the file's own aliases? Used where the expression has
    /// no place this scan can build, so the answer has to be conservative.
    fn mentionsObject(self: Solver, expr: u32, root: u32) bool {
        const target = self.aliasRoot(root, 0);
        const Visitor = struct {
            query: *const QueryContext,
            solver: Solver,
            target: u32,
            found: bool = false,
            stop: bool = false,

            pub fn visit(visitor: *@This(), _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
                if (tag != .identifier) return;
                const bound = visitor.query.resolveIdentifierBinding(node) orelse return;
                if (visitor.solver.aliasRoot(bound, 0) != visitor.target) return;
                visitor.found = true;
                visitor.stop = true;
            }
        };
        var visitor = Visitor{ .query = self.query, .solver = self, .target = target };
        // The visitor only reads bindings and sets a flag, so it has no error
        // to return and the walk cannot fail.
        ast_walk.walk(Visitor, self.query.tree, expr, &visitor) catch unreachable;
        return visitor.found;
    }

    fn containingBlock(self: Solver, node: u32) ?u32 {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        var current = node;
        while (current != 0) {
            const parent = self.query.lexical.parent(current) orelse return null;
            if (parent == 0 or parent >= tags.len) return null;
            switch (tags[parent]) {
                .block, .block_semicolon, .block_two, .block_two_semicolon => return parent,
                else => {},
            }
            current = parent;
        }
        return null;
    }

    // -----------------------------------------------------------------
    // What a call does to one place
    // -----------------------------------------------------------------

    const Receiver = union(enum) {
        /// The callee is handed the storage itself.
        slot: Path,
        /// The callee is handed a value read out of an optional, which aliases
        /// no optional slot and so cannot put a null back where it came from.
        /// What the callee reaches on its own account — a global it names, a
        /// parameter it was handed — is a different question, and one this
        /// file asks for every other receiver.
        loaded,
        /// Nothing this analysis can read.
        unresolved,
    };

    fn receiverOf(self: Solver, expr: u32) Receiver {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var node = expr;
        var depth: u32 = 0;
        while (depth < 16) : (depth += 1) {
            if (node == 0 or node >= tags.len) return .unresolved;
            switch (tags[node]) {
                .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
                .@"try", .@"comptime" => node = @intFromEnum(datas[node].node),
                .@"catch", .@"orelse" => node = @intFromEnum(datas[node].node_and_node[0]),
                .unwrap_optional => return .loaded,
                .identifier, .field_access => return .{ .slot = self.storagePlace(node) orelse return .unresolved },
                else => return .unresolved,
            }
        }
        return .unresolved;
    }

    fn callEffectOnPlace(self: Solver, call_node: u32, place: Path, depth: u32) Effect {
        if (depth >= 4) return .invalidated;
        const tree = self.query.tree;
        const call = fullCall(tree, call_node) orelse return .invalidated;

        // Anything the callee is handed out of the guarded object may write
        // through it.
        for (call.ast.params) |param| {
            if (self.placeReaches(@intFromEnum(param), place)) return .invalidated;
        }

        const field_access = calleeFieldAccess(tree, call_node) orelse return .untouched;
        switch (self.receiverOf(@intFromEnum(field_access[0]))) {
            .loaded => return self.foreignCallEffect(call_node, place, depth),
            .unresolved => return if (self.mentionsObject(@intFromEnum(field_access[0]), place.root)) .invalidated else .untouched,
            .slot => |receiver| {
                if (self.aliasRoot(receiver.root, 0) != self.aliasRoot(place.root, 0))
                    return self.foreignCallEffect(call_node, place, depth);
                if (receiver.len > place.len) return .untouched;
                const method = self.calleeAtCall(call_node) orelse return .invalidated;
                return self.methodEffect(method, place.slice()[receiver.len..], depth + 1, self.callerObservesFailure(call_node));
            },
        }
    }

    /// The same call analysis expressed relative to a callee's own receiver, so
    /// a nested method call can be followed to what it writes.
    fn callEffectWithin(self: Solver, call_node: u32, base: Path, suffix: []const []const u8, depth: u32) Effect {
        if (depth >= 4) return .invalidated;
        const tree = self.query.tree;
        const call = fullCall(tree, call_node) orelse return .invalidated;
        for (call.ast.params) |param| {
            if (pathTouches(self, @intFromEnum(param), base, suffix)) return .invalidated;
        }
        const field_access = calleeFieldAccess(tree, call_node) orelse return .untouched;
        switch (self.receiverOf(@intFromEnum(field_access[0]))) {
            .loaded => {
                const place = placeUnder(base, suffix) orelse return .invalidated;
                return self.foreignCallEffect(call_node, place, depth);
            },
            .unresolved => return if (self.mentionsObject(@intFromEnum(field_access[0]), base.root)) .invalidated else .untouched,
            .slot => |receiver| {
                if (self.aliasRoot(receiver.root, 0) != self.aliasRoot(base.root, 0)) {
                    const place = placeUnder(base, suffix) orelse return .invalidated;
                    return self.foreignCallEffect(call_node, place, depth);
                }
                if (receiver.len > suffix.len) return .untouched;
                const method = self.calleeAtCall(call_node) orelse return .invalidated;
                return self.methodEffect(method, suffix[receiver.len..], depth + 1, self.callerObservesFailure(call_node));
            },
        }
    }

    /// What a call reached through a receiver this file cannot spell as the
    /// place's own object does to that place.
    ///
    /// A receiver of another name is a different object as far as the spelling
    /// of the call goes, and what the callee writes through its own receiver
    /// and its own parameters was settled before the call was made:
    /// `otherParametersCannotAlias` has already refused every prototype that
    /// takes one that could reach this place. What nothing has settled is the
    /// storage the callee reaches without being handed it, and a global is
    /// exactly that — `session.read(sink)` fills the receiver with the address
    /// of the module-level `session`, which neither the prototype nor either
    /// body ever says. So the body is read here, and a write that reaches the
    /// place is the destruction of it.
    ///
    /// A value read out of an optional is a receiver of another name too.
    /// `self.queue.?.stopSession()` hands the callee the payload, so the call
    /// cannot put a null back into `queue` and the payload slot stays proven
    /// whatever the body does — but the body is still a body, and everything
    /// it names is still storage it can write. `Queue.stopSession` clears the
    /// module-level `session.region`, so the `self.region.?` that follows the
    /// payload call is destroyed by exactly the callback the `q.stopSession()`
    /// row is destroyed by. Both receivers answer the same question here.
    ///
    /// A declaration this scan cannot attribute is not followed. Its body lives
    /// in another file, where this file's globals have no name at all, and
    /// everything such a callee could reach is what the arguments read above
    /// already handed it. A payload is the one receiver whose declaration is
    /// still named here, because the field it was read from is written with a
    /// container this file reads.
    fn foreignCallEffect(self: Solver, call_node: u32, place: Path, depth: u32) Effect {
        const method = self.calleeAtCall(call_node) orelse
            self.loadedCalleeAtCall(call_node) orelse
            return .untouched;
        const body = functionBody(self.query.tree, method) orelse return .invalidated;
        return if (self.statementInvalidatesPlace(body, place, true, depth + 1)) .invalidated else .untouched;
    }

    /// The declaration a call reached through a payload names, or null for
    /// every other shape of receiver.
    ///
    /// `self.queue.?.stopSession()` reads its callee out of the payload, and
    /// the payload is the field the receiver's own container declares, so the
    /// member is looked up in the container that field is written with — the
    /// same lookup a parameter's declared type gives, and not a name match on
    /// anything. A field this file cannot type answers nothing, which is the
    /// answer a receiver this scan cannot spell gives everywhere else.
    fn loadedCalleeAtCall(self: Solver, call_node: u32) ?u32 {
        const access = calleeFieldAccess(self.query.tree, call_node) orelse return null;
        const payload = self.loadedPayloadOf(@intFromEnum(access[0])) orelse return null;
        return self.memberDeclaration(payload, self.fieldName(access[1]));
    }

    /// The expression a receiver read out of an optional takes its value
    /// from, or null when the receiver is spelled in any other shape.
    ///
    /// The wrappers `receiverOf` steps through are stepped through here for
    /// the same reason: the shape that decides is the one the operand of the
    /// `?` is spelled in, however many wrappers sit in front of it.
    fn loadedPayloadOf(self: Solver, expr: u32) ?u32 {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var node = expr;
        var depth: u32 = 0;
        while (depth < 16) : (depth += 1) {
            if (node == 0 or node >= tags.len) return null;
            switch (tags[node]) {
                .grouped_expression => node = @intFromEnum(datas[node].node_and_token[0]),
                .@"try", .@"comptime" => node = @intFromEnum(datas[node].node),
                .@"catch", .@"orelse" => node = @intFromEnum(datas[node].node_and_node[0]),
                .unwrap_optional => return @intFromEnum(datas[node].node_and_token[0]),
                else => return null,
            }
        }
        return null;
    }

    /// What a callee leaves in the field its receiver's path names.
    ///
    /// This scan is what makes an installer trustworthy and a teardown fatal
    /// without trusting any name: only an unconditional write of a value that
    /// cannot be null installs, every successful exit of the body has to leave
    /// the field installed, and anything the scan cannot read invalidates.
    /// An exit that does not install the field is `not_installed`: the caller
    /// cannot count on an installation, yet the exit does not put a null back,
    /// so a field an earlier statement installed survives it.
    ///
    /// An `errdefer` rollback depends on the caller. It runs only when the
    /// call failed, which is a path the caller has already left when the
    /// failure propagates out of it — a `try`, or a handler that returns,
    /// breaks or continues — and a state it never reaches. A caller that
    /// swallows the failure and carries on observes the rolled-back field
    /// instead, so the body belongs to the effect there. `observes_failure`
    /// carries that answer from the call site.
    ///
    /// Installing also takes a receiver that *is* the caller's storage. A
    /// by-value receiver is a copy handed to the callee, so `self.field = 5`
    /// inside it writes that copy and leaves the caller's field untouched;
    /// crediting it as an installation would prove a caller's own unwrap with
    /// a write that never reached it. Its writes still invalidate, because a
    /// callee handed a copy can still reach the caller through the rest of
    /// what it was given.
    ///
    /// A call the body makes is no exemption: `var mine = self;
    /// mine.installByPointer(value);` installs the copy's own field through a
    /// receiver that is a pointer, and the caller's storage is still the
    /// caller's. That exit installs nothing for the caller, which is what
    /// `not_installed` records.
    fn methodEffect(
        self: Solver,
        method: u32,
        suffix: []const []const u8,
        depth: u32,
        observes_failure: bool,
    ) Effect {
        if (depth >= 4 or suffix.len == 0 or suffix.len > max_depth) return .invalidated;
        const tree = self.query.tree;
        var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = constructor_facts.treeFnProto(tree, method, &proto_buffer) orelse return .invalidated;
        if (proto.ast.params.len == 0) return .invalidated;
        const base = Path{ .root = receiverNameToken(tree, method) orelse return .invalidated };

        const body = functionBody(tree, method) orelse return .invalidated;
        var scan = EffectScan{
            .base = base,
            .suffix = suffix,
            .depth = depth + 1,
            .method = method,
            .observes_failure = observes_failure,
            .installs = receiverIsSinglePointer(tree, method),
        };
        self.scanEffectBlock(body, true, &scan);
        // Installing needs a receiver that is the caller's storage, and the
        // only paths that establish it are the writes this scan reads as
        // unconditional on a receiver of that shape. A nested call reaches the
        // caller's field only through its own receiver, so a by-value method
        // that installs through one has not installed anything here: the copy
        // is what the write lands on, and the caller's field survives an
        // earlier statement's installation rather than being counted twice.
        if (!scan.installs and scan.effect == .installs) scan.effect = .not_installed;
        return scan.effect;
    }

    fn scanEffectBlock(self: Solver, body: u32, unconditional: bool, scan: *EffectScan) void {
        const tree = self.query.tree;
        var block_buffer: [2]u32 = undefined;
        const statements = ast_walk.getBlockStatements(tree, body, &block_buffer) orelse {
            // An expression-bodied function is one unconditional statement.
            self.scanEffectSubtree(body, unconditional, scan);
            return;
        };
        for (statements) |statement| self.scanEffectStatement(statement, unconditional, scan);
    }

    fn scanEffectStatement(self: Solver, statement: u32, unconditional: bool, scan: *EffectScan) void {
        const tree = self.query.tree;
        if (statement >= tree.nodes.len or scan.effect == .invalidated) return;
        switch (tree.nodeTag(@enumFromInt(statement))) {
            // A `defer` body runs before the scope ends, so it describes the
            // state a caller observes. An `errdefer` body runs only when the
            // function leaves with an error: a caller whose failure path ends
            // the call never reaches the state it produces, while a caller
            // that carries on after a swallowed failure observes exactly that.
            .@"errdefer" => {
                // Its body describes the failure path alone, so it can undo an
                // installation but never establish one.
                if (scan.observes_failure) self.scanEffectSubtree(statement, false, scan);
                return;
            },
            .@"defer" => {
                self.scanDeferredBody(statement, unconditional, scan);
                return;
            },
            // A conditional write is not an installation, unless it is the one
            // shape whose two paths both leave the field filled.
            .@"if",
            .if_simple,
            => {
                if (self.lazyInstallsPlace(statement, scan)) {
                    mergeEffect(&scan.effect, .installs);
                    return;
                }
                self.scanEffectSubtree(statement, false, scan);
                return;
            },
            // Under any branch a write may or may not have run, so it can never
            // be the unconditional installation a caller needs.
            .@"while",
            .while_simple,
            .while_cont,
            .@"for",
            .for_simple,
            .@"switch",
            .switch_comma,
            .@"orelse",
            .@"catch",
            .bool_and,
            .bool_or,
            => {
                self.scanEffectSubtree(statement, false, scan);
                return;
            },
            else => self.scanEffectSubtree(statement, unconditional, scan),
        }
    }

    /// A `defer` body runs when its scope ends, so what the caller observes is
    /// what that body leaves behind — and the body is read as a statement of
    /// its own rather than walked flat. `defer if (self.field == null)
    /// self.field = 0;` leaves the place installed on both of its paths, and a
    /// body written as a block says the same thing one level down, so both are
    /// the installation a caller needs. A write under any other condition
    /// leaves one path unfilled and keeps the answer the generic branch scan
    /// gives it; a body written without a condition is still the unconditional
    /// write it reads as.
    fn scanDeferredBody(self: Solver, statement: u32, unconditional: bool, scan: *EffectScan) void {
        const body = self.deferredBody(statement) orelse {
            self.scanEffectSubtree(statement, unconditional, scan);
            return;
        };
        self.scanEffectStatement(body, unconditional, scan);
    }

    /// The expression a `defer` runs when its scope ends.
    ///
    /// A body written as a block contributes the one statement inside it,
    /// because that is the expression the block holds. Anything the tree does
    /// not spell as a single statement stays the body it is.
    fn deferredBody(self: Solver, statement: u32) ?u32 {
        const tree = self.query.tree;
        if (statement >= tree.nodes.len) return null;
        if (tree.nodeTag(@enumFromInt(statement)) != .@"defer") return null;
        const body = @intFromEnum(tree.nodes.items(.data)[statement].node);
        if (body == 0 or body >= tree.nodes.len) return null;
        var block_buffer: [2]u32 = undefined;
        if (ast_walk.getBlockStatements(tree, body, &block_buffer)) |statements| {
            if (statements.len == 1) return statements[0];
        }
        return body;
    }

    /// Does this `if` leave the place installed on both of its paths?
    ///
    /// `if (self.field == null) self.field = 1;` reaches everything after it
    /// with a non-null field however the condition went: the arm that ran wrote
    /// one, and the other arm is running precisely because the field was not
    /// null. That is the whole of the shape — the null test has to be on this
    /// exact field, there is no `else` arm to un-fill it, and the arm has to be
    /// a single write of a value that cannot be null. An `else`, a nullable
    /// value, an arm written as a block, a condition about anything else, and a
    /// receiver the caller did not hand over all leave one path unfilled, so
    /// each of them keeps the answer the generic branch scan gives.
    fn lazyInstallsPlace(self: Solver, statement: u32, scan: *const EffectScan) bool {
        const tree = self.query.tree;
        if (!scan.installs) return false;
        const full = tree.fullIf(@enumFromInt(statement)) orelse return false;
        if (full.ast.else_expr.unwrap() != null) return false;
        if (full.payload_token != null) return false;
        const place = scan.place();
        if (!self.conditionProvesNull(@intFromEnum(full.ast.cond_expr), place)) return false;
        return self.statementInstallsPlace(@intFromEnum(full.ast.then_expr), place, true);
    }

    fn scanEffectSubtree(self: Solver, root: u32, unconditional: bool, scan: *EffectScan) void {
        const scan_tree = self.query.tree;
        const Visitor = struct {
            solver: Solver,
            scan: *EffectScan,
            root: u32,
            unconditional: bool,
            found: Effect = .untouched,
            stop: bool = false,

            /// Records what one node does, never letting a weaker answer
            /// replace a stronger one the scan already holds.
            fn raise(visitor: *@This(), effect: Effect) void {
                visitor.found = strongerEffect(visitor.found, effect);
                if (visitor.found == .invalidated) visitor.stop = true;
            }

            pub fn visit(visitor: *@This(), _: *const std.zig.Ast, node: u32, tag: std.zig.Ast.Node.Tag) !void {
                if (visitor.found == .invalidated) return;
                switch (tag) {
                    .@"asm",
                    .asm_simple,
                    .address_of,
                    .assign,
                    .assign_destructure,
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
                    .call,
                    .call_comma,
                    .call_one,
                    .call_one_comma,
                    .builtin_call,
                    .builtin_call_comma,
                    .builtin_call_two,
                    .builtin_call_two_comma,
                    .@"return",
                    => {},
                    else => return,
                }
                // A rollback body belongs to the error path, which the caller
                // never reaches when its own failure path ends the call.
                if (!visitor.scan.observes_failure and visitor.solver.insideErrdefer(node, visitor.root)) return;
                const tree = visitor.solver.query.tree;
                const datas = tree.nodes.items(.data);
                switch (tag) {
                    .@"asm", .asm_simple => visitor.raise(.invalidated),
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
                        if (!writeTouches(visitor.solver, lhs, visitor.scan.base, visitor.scan.suffix)) return;
                        const rhs = @intFromEnum(datas[node].node_and_node[1]);
                        if (visitor.unconditional and visitor.scan.installs and visitor.solver.storesNonNull(rhs, 0)) {
                            visitor.raise(.installs);
                        } else {
                            visitor.raise(.invalidated);
                        }
                    },
                    .assign_destructure => {
                        const full = tree.assignDestructure(@enumFromInt(node));
                        for (full.ast.variables) |variable| {
                            if (!writeTouches(visitor.solver, @intFromEnum(variable), visitor.scan.base, visitor.scan.suffix)) continue;
                            visitor.raise(.invalidated);
                            return;
                        }
                    },
                    .address_of => {
                        if (!writeTouches(visitor.solver, @intFromEnum(datas[node].node), visitor.scan.base, visitor.scan.suffix)) return;
                        visitor.raise(.invalidated);
                    },
                    .call, .call_comma, .call_one, .call_one_comma => {
                        const effect = visitor.solver.callEffectWithin(node, visitor.scan.base, visitor.scan.suffix, visitor.scan.depth);
                        if (effect == .untouched) return;
                        visitor.raise(effect);
                    },
                    .@"return" => {
                        if (!visitor.solver.successfulExitLeavesPlaceUninstalled(node, visitor.scan)) return;
                        // An exit that installs nothing takes the installation
                        // with it, but it does not put a null back.
                        visitor.raise(.not_installed);
                    },
                    .builtin_call, .builtin_call_comma, .builtin_call_two, .builtin_call_two_comma => {
                        var buffer: [2]std.zig.Ast.Node.Index = undefined;
                        const params = tree.builtinCallParams(&buffer, @enumFromInt(node)) orelse {
                            if (visitor.solver.mentionsObject(node, visitor.scan.base.root)) {
                                visitor.raise(.invalidated);
                            }
                            return;
                        };
                        for (params) |param| {
                            if (!writeTouches(visitor.solver, @intFromEnum(param), visitor.scan.base, visitor.scan.suffix)) continue;
                            visitor.raise(.invalidated);
                            return;
                        }
                    },
                    else => {},
                }
            }
        };

        var visitor = Visitor{ .solver = self, .scan = scan, .root = root, .unconditional = unconditional };
        ast_walk.walk(Visitor, scan_tree, root, &visitor) catch {
            scan.effect = .invalidated;
            return;
        };
        mergeEffect(&scan.effect, visitor.found);
    }

    /// An `errdefer` body belongs to the error path, which a caller whose own
    /// failure path ends the call never reaches.
    fn insideErrdefer(self: Solver, node: u32, root: u32) bool {
        const tags = self.query.tree.nodes.items(.tag);
        var current = node;
        while (current != 0 and current != root) {
            const parent = self.query.lexical.parent(current) orelse return false;
            if (parent == 0 or parent >= tags.len) return false;
            if (tags[parent] == .@"errdefer") return true;
            current = parent;
        }
        return false;
    }

    /// Can the caller of this call still be running after the call failed?
    ///
    /// A `try` and a handler that returns, breaks or continues both end the
    /// caller's own flow on failure, so the state the failure path produces is
    /// a state no statement after the call can observe. Anything else — a
    /// discarded error, an empty handler, a value read out of the union — lets
    /// the caller carry on, and the failure path is part of what it sees.
    fn callerObservesFailure(self: Solver, call_node: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        var node = call_node;
        var depth: u32 = 0;
        while (depth < 8) : (depth += 1) {
            const parent = self.query.lexical.parent(node) orelse return false;
            if (parent == 0 or parent >= tags.len) return false;
            switch (tags[parent]) {
                .@"try" => return false,
                .@"catch", .@"orelse" => return !guards.handlerPreventsCompletion(
                    tree,
                    @intFromEnum(datas[parent].node_and_node[1]),
                    tags,
                    datas,
                ),
                .grouped_expression => node = @intFromEnum(datas[parent].node_and_token[0]),
                .@"comptime" => node = @intFromEnum(datas[parent].node),
                else => return false,
            }
        }
        return false;
    }

    /// Does this `return` leave the callee successfully without the place
    /// being installed where it stands?
    ///
    /// An installation a caller may rely on has to survive every way the
    /// callee can leave, not only the one that falls off the end: `if (fail)
    /// return; self.field = 1;` hands the caller a field that is still null.
    /// Returning an error does not reach a successful caller. Returning a
    /// receiver field is still a successful exit and must preserve the fact.
    ///
    /// The proof is the same lexical question every other statement in this
    /// file asks, minus the answers a call carries: `if (self.field != null)
    /// return;` and a plain `self.field = 1; return;` are settled by the
    /// guard or the write that precedes the exit.
    fn successfulExitLeavesPlaceUninstalled(self: Solver, node: u32, scan: *const EffectScan) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (node >= tags.len) return false;
        if (datas[node].opt_node.unwrap()) |operand| {
            const value = @intFromEnum(operand);
            if (value < tags.len and tags[value] == .error_value) return false;
            // `catch |err| return err;` hands the caller the failure it was
            // given, which is not a value the place had to survive.
            if (self.isCaughtErrorPayload(node, value)) return false;
        }
        if (!self.isOwnStatementOfMethod(node, scan.method)) return false;
        return !self.provesPlaceWithoutCalls(node, scan.place());
    }

    /// Is `operand` the error a `catch` around `node` binds?
    fn isCaughtErrorPayload(self: Solver, node: u32, operand: u32) bool {
        const tree = self.query.tree;
        const token_tags = tree.tokens.items(.tag);
        if (operand >= tree.nodes.len or tree.nodeTag(@enumFromInt(operand)) != .identifier) return false;
        const name = tree.nodeMainToken(@enumFromInt(operand));
        if (name >= tree.tokens.len) return false;
        var current = node;
        var depth: u32 = 0;
        while (depth < 64) : (depth += 1) {
            const parent = self.query.lexical.parent(current) orelse return false;
            if (parent == 0) return false;
            // `catch |err|` and `catch |*err|` bind the name one or two tokens
            // past the keyword.
            if (tree.nodeTag(@enumFromInt(parent)) == .@"catch") {
                var bound = tree.nodeMainToken(@enumFromInt(parent)) + 2;
                if (bound < token_tags.len and token_tags[bound] == .asterisk) bound += 1;
                if (bound < token_tags.len and bound == name) return true;
            }
            current = parent;
        }
        return false;
    }

    /// Is `node` a statement of `method` itself rather than of a function
    /// declared inside its body?
    fn isOwnStatementOfMethod(self: Solver, node: u32, method: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        var current = node;
        var depth: u32 = 0;
        while (depth < 64) : (depth += 1) {
            const parent = self.query.lexical.parent(current) orelse return false;
            if (parent == 0) return false;
            if (parent == method) return true;
            if (tags[parent] == .fn_decl) return false;
            current = parent;
        }
        return false;
    }

    // -----------------------------------------------------------------
    // What a value expression can store
    // -----------------------------------------------------------------

    /// Is the value `node` produces non-null?
    ///
    /// The syntactic forms answer without a type query, so the proof behaves
    /// the same whether or not the frontend produced type information.
    fn storesNonNull(self: Solver, node: u32, depth: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (node == 0 or node >= tags.len or depth >= 12) return false;
        if (guards.isDefinitelyNonNullExpression(tree, node, self.type_context, tags, datas)) return true;
        switch (tags[node]) {
            .@"try", .@"comptime" => return self.storesNonNull(@intFromEnum(datas[node].node), depth + 1),
            .@"orelse" => return self.storesNonNull(@intFromEnum(datas[node].node_and_node[1]), depth + 1),
            .grouped_expression => return self.storesNonNull(@intFromEnum(datas[node].node_and_token[0]), depth + 1),
            // `p.*` carries the pointee's own nullability: reading a `*?T`
            // yields an optional again, so only a pointer to a type that
            // cannot be optional makes it a non-null value.
            .deref => return self.derefStoresNonNull(@intFromEnum(datas[node].node), depth + 1),
            .identifier => return self.identifierStoresNonNull(node, depth),
            .call, .call_comma, .call_one, .call_one_comma => {
                // Only a call this file declares answers here: a method's
                // result type is a property of its receiver's type, which this
                // scan does not resolve.
                const call = fullCall(tree, node) orelse return false;
                const fn_expr = @intFromEnum(call.ast.fn_expr);
                if (tree.nodeTag(@enumFromInt(fn_expr)) != .identifier) return false;
                const function = self.resolvePlainFunction(fn_expr) orelse return false;
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const proto = constructor_facts.treeFnProto(tree, function, &buffer) orelse return false;
                const return_type = proto.ast.return_type.unwrap() orelse return false;
                return self.typeIsNonOptional(@intFromEnum(return_type), depth + 1);
            },
            else => return false,
        }
    }

    fn identifierStoresNonNull(self: Solver, node: u32, depth: u32) bool {
        const candidate = self.bindingCandidate(node) orelse return false;
        switch (candidate.kind) {
            .parameter => {
                const written = constructor_facts.parameterTypeNode(self.query.tree, candidate.node) orelse return false;
                return self.typeIsNonOptional(written, depth + 1);
            },
            .variable => {
                const full = self.query.tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return false;
                if (full.ast.type_node.unwrap()) |written| return self.typeIsNonOptional(@intFromEnum(written), depth + 1);
                const init = full.ast.init_node.unwrap() orelse return false;
                return self.storesNonNull(@intFromEnum(init), depth + 1);
            },
            else => return false,
        }
    }

    /// Can the type `type_node` describe hold null?
    ///
    /// A name is followed through this file's own alias declarations, all the
    /// way to the type it was given. An annotation of `type` is the one
    /// spelling that does not describe the instances a name stands for: it
    /// describes the type value the alias holds, so `const Height: type =
    /// ?u32` still names optional instances and its initializer is what has to
    /// be classified. A name this scan cannot follow is an unknown type, and
    /// an unknown type is never assumed to be non-optional.
    fn typeIsNonOptional(self: Solver, type_node: u32, depth: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (type_node == 0 or type_node >= tags.len or depth >= 12) return false;
        switch (tags[type_node]) {
            .optional_type => return false,
            .error_union => return self.typeIsNonOptional(@intFromEnum(datas[type_node].node_and_node[1]), depth + 1),
            .anyframe_type => return false,
            .identifier => {
                // The built-in type names are the only names that are provably
                // not optional without a declaration to read.
                if (isBuiltinTypeName(self.fieldName(tree.nodes.items(.main_token)[type_node]))) return true;
                const candidate = self.bindingCandidate(type_node) orelse return false;
                if (candidate.kind != .variable) return false;
                const full = self.query.tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return false;
                if (full.ast.type_node.unwrap()) |written| {
                    // The annotation describes the alias itself, so the type
                    // the alias stands for is the value it was given.
                    if (typeNodeIsTypeKeyword(tree, @intFromEnum(written), tags)) {
                        const annotated = full.ast.init_node.unwrap() orelse return false;
                        return self.typeValueIsNonOptional(@intFromEnum(annotated), depth + 1);
                    }
                    return self.typeIsNonOptional(@intFromEnum(written), depth + 1);
                }
                const init = full.ast.init_node.unwrap() orelse return false;
                return self.typeValueIsNonOptional(@intFromEnum(init), depth + 1);
            },
            else => return false,
        }
    }

    /// Is `node`, used where a type is spelled, a type that cannot be optional?
    ///
    /// A literal container declaration — `struct { ... }`, `enum { ... }`,
    /// `union { ... }` or `union(enum) { ... }`, in any layout — is a type that
    /// cannot hold null, and so is a primitive name and a name this file
    /// follows to one. An optional literal is not. A value literal such as
    /// `.{ ... }` is not a type declaration at all, and anything this scan
    /// cannot classify is unknown rather than non-null.
    fn typeValueIsNonOptional(self: Solver, node: u32, depth: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (node == 0 or node >= tags.len or depth >= 12) return false;
        const tag = tags[node];
        if (call_resolver.isContainerTag(tag)) return true;
        switch (tag) {
            .optional_type => return false,
            .error_union => return self.typeValueIsNonOptional(@intFromEnum(datas[node].node_and_node[1]), depth + 1),
            // A generic type application is only a type when its callee names a
            // declaration this file owns; an unresolved one is unknown, and a
            // factory call that happens to sit here proves nothing.
            .call, .call_comma, .call_one, .call_one_comma => {
                const call = fullCall(tree, node) orelse return false;
                const fn_expr = @intFromEnum(call.ast.fn_expr);
                if (tree.nodeTag(@enumFromInt(fn_expr)) != .identifier) return false;
                return self.typeValueIsNonOptional(fn_expr, depth + 1);
            },
            .identifier, .field_access => return self.typeIsNonOptional(node, depth + 1),
            else => return false,
        }
    }

    /// `p.*` yields the pointee, which is non-null only when the pointer's
    /// target type cannot be optional. A pointer this scan cannot read proves
    /// nothing.
    fn derefStoresNonNull(self: Solver, pointer_expr: u32, depth: u32) bool {
        const tree = self.query.tree;
        const pointer = self.storagePlace(pointer_expr) orelse return false;
        const candidate = self.bindingForToken(pointer.root) orelse return false;
        const written = switch (candidate.kind) {
            .variable => blk: {
                const full = tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return false;
                break :blk @intFromEnum(full.ast.type_node.unwrap() orelse return false);
            },
            .parameter => constructor_facts.parameterTypeNode(tree, candidate.node) orelse return false,
            else => return false,
        };
        return self.pointeeIsNonOptional(written, depth + 1);
    }

    /// Strips the pointer layers off a declared type and asks whether what it
    /// finally points at can be optional.
    fn pointeeIsNonOptional(self: Solver, type_node: u32, depth: u32) bool {
        if (depth >= 8 or type_node >= self.query.tree.nodes.len) return false;
        const tree = self.query.tree;
        switch (tree.nodeTag(@enumFromInt(type_node))) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                const pointer = tree.fullPtrType(@enumFromInt(type_node)) orelse return false;
                return self.pointeeIsNonOptional(@intFromEnum(pointer.ast.child_type), depth + 1);
            },
            .optional_type => return false,
            .error_union => return self.pointeeIsNonOptional(@intFromEnum(tree.nodes.items(.data)[type_node].node_and_node[1]), depth + 1),
            .identifier => return self.typeIsNonOptional(type_node, depth + 1),
            else => return false,
        }
    }

    // -----------------------------------------------------------------
    // Constructed owners
    // -----------------------------------------------------------------

    /// The fields `init_node` hands a successfully built value on *every*
    /// success path. A field installed on only one path, by a return this scan
    /// cannot read, or behind a constructor it cannot attribute installs
    /// nothing.
    fn ownerFacts(self: Solver, init_node: u32, depth: u32) OwnerFacts {
        var facts = OwnerFacts{ .known = true };
        self.collectInitFacts(init_node, depth, &facts);
        return facts;
    }

    fn collectInitFacts(self: Solver, node: u32, depth: u32, facts: *OwnerFacts) void {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (!facts.known or depth >= max_nesting or node == 0 or node >= tags.len) return;
        switch (tags[node]) {
            .grouped_expression => {
                self.collectInitFacts(@intFromEnum(datas[node].node_and_token[0]), depth + 1, facts);
                return;
            },
            .@"comptime" => {
                self.collectInitFacts(@intFromEnum(datas[node].node), depth + 1, facts);
                return;
            },
            .@"try" => {
                self.collectInitFacts(@intFromEnum(datas[node].node), depth + 1, facts);
                return;
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
                const init = tree.fullStructInit(&buffer, @enumFromInt(node)) orelse return;
                for (init.ast.fields) |value_node| {
                    const value = @intFromEnum(value_node);
                    const name_token = structInitFieldNameToken(tree, value_node) orelse {
                        facts.known = false;
                        return;
                    };
                    const name = self.fieldName(name_token);
                    var path: [max_depth][]const u8 = undefined;
                    path[0] = name;
                    if (self.storesNonNull(value, 0)) facts.insert(path[0..1]);

                    // A nested owner carries its own facts, so a driver built
                    // from a constructed session keeps `session.region`.
                    var nested = OwnerFacts{ .known = true };
                    self.collectInitFacts(value, depth + 1, &nested);
                    if (!nested.known) {
                        facts.known = false;
                        return;
                    }
                    for (nested.paths[0..nested.len], nested.depths[0..nested.len]) |candidate, nested_depth| {
                        // The stored depth is the length of the path itself, so
                        // it — not the table slot — is what this field shifts
                        // by one when the nested fact is re-measured from here.
                        const inner: usize = nested_depth;
                        if (inner + 1 > max_depth) {
                            facts.known = false;
                            return;
                        }
                        path[0] = name;
                        for (candidate[0..inner], 0..) |field, position| path[1 + position] = field;
                        facts.insert(path[0 .. inner + 1]);
                    }
                }
                return;
            },
            .call, .call_comma, .call_one, .call_one_comma => {
                const call = fullCall(tree, node) orelse return;
                const fn_expr = @intFromEnum(call.ast.fn_expr);
                if (tree.nodeTag(@enumFromInt(fn_expr)) != .identifier) return;
                const function = self.resolvePlainFunction(fn_expr) orelse return;
                self.collectReturnFacts(function, depth + 1, facts);
                return;
            },
            else => {},
        }
    }

    fn collectReturnFacts(self: Solver, function: u32, depth: u32, facts: *OwnerFacts) void {
        if (!facts.known or depth >= max_nesting) return;
        // A name resolves to the prototype that declares it while a return
        // belongs to the `fn_decl` that owns it, so both spellings are named
        // here and every return path is counted against the declaration.
        const declaration = self.declarationOfPrototype(function);
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = constructor_facts.treeFnProto(tree, function, &buffer) orelse {
            facts.known = false;
            return;
        };
        const return_type = proto.ast.return_type.unwrap() orelse {
            facts.known = false;
            return;
        };
        // An optional result can be null however the body spells its return.
        if (!self.typeIsNonOptional(@intFromEnum(return_type), 0)) {
            facts.known = false;
            return;
        }

        var returns: usize = 0;
        var node: u32 = 1;
        while (node < tags.len) : (node += 1) {
            if (tags[node] != .@"return") continue;
            if (constructor_facts.enclosingFunction(self.query, node) != declaration) continue;
            const value = tree.nodes.items(.data)[node].opt_node.unwrap() orelse {
                facts.known = false;
                return;
            };
            var per_return = OwnerFacts{ .known = true };
            self.collectInitFacts(@intFromEnum(value), depth + 1, &per_return);
            if (!per_return.known) {
                facts.known = false;
                return;
            }
            returns += 1;
            if (returns == 1) {
                facts.* = per_return;
            } else {
                facts.intersect(per_return);
            }
            if (!facts.known) return;
        }
        if (returns == 0) facts.known = false;
    }

    // -----------------------------------------------------------------
    // Declarations
    // -----------------------------------------------------------------

    fn bindingCandidate(self: Solver, node: u32) ?lexical_index.Candidate {
        const name_token = self.query.resolveIdentifierBinding(node) orelse return null;
        return self.bindingForToken(name_token);
    }

    /// The declaration a name token introduces, read back out of the index the
    /// name itself was resolved through.
    fn bindingForToken(self: Solver, name_token: u32) ?lexical_index.Candidate {
        if (name_token == 0) return null;
        const name = import_resolver.normalizeIdentifier(self.query.tree.tokenSlice(name_token));
        var best: ?lexical_index.Candidate = null;
        for (self.query.lexical.namedCandidates(name)) |*candidate| {
            if (candidate.name_token == name_token) best = candidate.*;
        }
        return best;
    }

    fn resolvePlainFunction(self: Solver, expr: u32) ?u32 {
        const tree = self.query.tree;
        if (tree.nodeTag(@enumFromInt(expr)) != .identifier) return null;
        const token = tree.nodes.items(.main_token)[expr];
        return self.query.lexical.findFunction(import_resolver.normalizeIdentifier(tree.tokenSlice(token)), token);
    }

    /// The type one expression denotes, read through this file's own lexical
    /// index alone: a declaration outside it is never resolved, so the answer is
    /// either a container this file declares or nothing at all.
    fn resolvedExprType(self: Solver, expr: u32) ?call_resolver.ResolvedType {
        if (expr == 0 or expr >= self.query.tree.nodes.len) return null;
        const files = [_]import_resolver.File{.{
            .path = "",
            .tree = self.query.tree,
            .lexical_index = self.query.lexical,
        }};
        const resolver = call_resolver.ProjectTypeResolver{ .files = &files, .file_index = 0 };
        return resolver.resolveExprType(expr);
    }

    /// The declaration a prototype belongs to.
    ///
    /// The project's resolver answers with the prototype — the node that
    /// carries the name, the parameters and the return type — while every
    /// question here is asked of the `fn_decl` that owns it, so the two are
    /// named once and compared everywhere else. A prototype with no body is its
    /// own declaration: there is no body to read, which each such question
    /// already counts as "cannot prove".
    fn declarationOfPrototype(self: Solver, proto: u32) u32 {
        const tree = self.query.tree;
        if (proto == 0 or proto >= tree.nodes.len) return proto;
        if (tree.nodeTag(@enumFromInt(proto)) == .fn_decl) return proto;
        // A prototype's first token is the `fn` its declaration opens with, and
        // the index answers with the innermost function that owns a token, so
        // this names the declaration that holds it — even for a function
        // declared inside another one.
        const owner = self.query.lexical.enclosingFunction(self.query.firstToken(proto)) orelse return proto;
        if (owner >= tree.nodes.len or tree.nodeTag(@enumFromInt(owner)) != .fn_decl) return proto;
        return owner;
    }

    /// The declaration a call reaches, read from the receiver's own lexical
    /// type rather than from the spelling of a name.
    ///
    /// A method's identity is the pair of the container that declares it and
    /// the declaration itself, so two containers may declare the same name
    /// without either call reaching the other: `owner.append` and `sink.append`
    /// are two different functions even when nothing else tells them apart.
    /// Nothing here can attribute a call — a receiver whose type this file never
    /// spells out, a callee out of another file, a name shadowed by a local —
    /// and a call it cannot attribute is a call it cannot judge, which the
    /// callers answer as "not proven" rather than "some other method".
    fn calleeAtCall(self: Solver, call_node: u32) ?u32 {
        const callable = self.callableAtCall(call_node) orelse return null;
        return self.declarationOfPrototype(callable.proto_node);
    }

    /// The declaration a call reaches together with the shape it was reached
    /// in: `implicit_self_count` is how many leading prototype parameters this
    /// call site never writes, so argument `i` is parameter `i + that`.
    fn callableAtCall(self: Solver, call_node: u32) ?call_resolver.CallableInfo {
        const tree = self.query.tree;
        if (call_node >= tree.nodes.len or !isCallTag(tree.nodeTag(@enumFromInt(call_node)))) return null;
        const files = [_]import_resolver.File{.{
            .path = "",
            .tree = tree,
            .lexical_index = self.query.lexical,
        }};
        const resolver = call_resolver.ProjectTypeResolver{ .files = &files, .file_index = 0 };
        return resolver.resolveCallableAtCall(call_node);
    }

    /// Does `expr` carry a container of its own that is not `container`?
    ///
    /// This is how a method reference is attributed: a receiver this file can
    /// type to another container names that container's member, so a
    /// same-named reference there is a reference to that method rather than to
    /// this one. A receiver nothing here can type decides nothing, and a
    /// reference it cannot place may still name this method to a caller the
    /// file cannot see.
    fn receiverCarriesOtherContainer(self: Solver, expr: u32, container: u32) bool {
        const resolved = self.resolvedExprType(expr) orelse return false;
        const carried = resolved.container_node orelse return false;
        return carried != container;
    }

    fn declarationIsFilePrivate(self: Solver, method: u32) bool {
        const tree = self.query.tree;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = constructor_facts.treeFnProto(tree, method, &buffer) orelse return false;
        // An exported, external or inlined method has callers this file does
        // not contain, so no set of local callers can bound it.
        if (proto.visib_token != null or proto.extern_export_inline_token != null) return false;
        // A declaration no container holds is a top-level one, and nothing but
        // its own visibility says whether another file can name it: without
        // `pub` there is no spelling of it outside this file, and it is a
        // member of no container, so a receiver elsewhere cannot reach it.
        const container = constructor_facts.enclosingContainer(self.query, method) orelse
            return true;
        // The enclosing container is the type itself, and a container carries
        // no visibility of its own: the declaration that introduces its name
        // is what says whether code in another file can reach it.
        const declaration = self.declarationOfContainer(container) orelse return false;
        const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return false;
        if (full.visib_token != null or full.extern_export_token != null) return false;
        return true;
    }

    /// The declaration a container is written as the value of, which is the
    /// one that gives its name a visibility this file can read.
    ///
    /// A container spelled where no declaration introduces it — a parameter
    /// type, a return type, a literal inside an expression — can be reached
    /// through every value of that type, so this answers nothing and the
    /// method keeps its warning.
    fn declarationOfContainer(self: Solver, container: u32) ?u32 {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        var current = container;
        var depth: u32 = 0;
        while (depth < 8) : (depth += 1) {
            const parent = self.query.lexical.parent(current) orelse return null;
            if (parent == 0 or parent >= tags.len) return null;
            if (import_resolver.isVarDeclTag(tags[parent])) return parent;
            current = parent;
        }
        return null;
    }

    /// A method reference that is not the callee of a call can be invoked from
    /// somewhere this scan never sees, so the proof stops at the first one.
    ///
    /// A method is reached through its container — `Owner.read`, `Self.read`,
    /// `app.read` — so every reference to one is a field access and is
    /// attributed the way a call is: a receiver whose own type this file
    /// declares places the reference in that container, and one that places it
    /// in another container names that container's method. A receiver nothing
    /// here can type leaves the reference open, because it may still name this
    /// method to a caller the file cannot see. The callee of a call is not a
    /// reference at all: that call is one of the callers this proof already
    /// enumerates. A declaration no container holds is reached the other way
    /// round — by a bare name and never through a receiver — so the references
    /// to it are the ones `everyReferenceIsACall` enumerates.
    fn methodEscapes(self: Solver, method: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        const name = self.fieldName(methodNameToken(tree, method) orelse return true);
        const container = constructor_facts.enclosingContainer(self.query, method) orelse
            return !self.everyReferenceIsACall(method);
        var node: u32 = 1;
        while (node < tags.len) : (node += 1) {
            if (tags[node] != .field_access) continue;
            const access = datas[node].node_and_token;
            if (!std.mem.eql(u8, self.fieldName(access[1]), name)) continue;
            const owner = self.query.lexical.parent(node) orelse return true;
            if (owner == 0 or owner >= tags.len) return true;
            if (isCallTag(tags[owner])) {
                const call = fullCall(tree, owner) orelse return true;
                if (@intFromEnum(call.ast.fn_expr) != node) return true;
                continue;
            }
            if (self.receiverCarriesOtherContainer(@intFromEnum(access[0]), container)) continue;
            return true;
        }
        return false;
    }

    /// A parameter that could name the receiver's own storage would let the
    /// callee rewrite the field its own unwrap depends on.
    ///
    /// Zig keeps an `anytype` or `...` parameter out of a prototype's own
    /// parameter list altogether — `Ast.FnProto.Iterator` exists precisely
    /// because they are "simple identifiers and not sub-expressions" — so the
    /// prototype is read through its own iteration, which is in the order the
    /// parameters are written. Such a parameter carries whatever the
    /// instantiation gives it, so its proof is not this scan's to make.
    fn otherParametersCannotAlias(self: Solver, method: u32) bool {
        const tree = self.query.tree;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = constructor_facts.treeFnProto(tree, method, &buffer) orelse return false;
        var index: usize = 0;
        var params = proto.iterate(tree);
        while (params.next()) |param| : (index += 1) {
            if (param.type_expr == null) return false;
            if (index == 0) continue;
            const written = constructor_facts.parameterTypeNode(tree, @intFromEnum(param.type_expr.?)) orelse return false;
            if (written == 0 or written >= tree.nodes.len) return false;
            if (self.typeMayNameReceiver(written, method, 0)) return false;
        }
        return true;
    }

    /// Can a value of `type_node` reach the receiver's own storage?
    ///
    /// The walk follows the shapes that can actually carry a pointer: a pointer
    /// of any size — `*T`, `[]T` and `[*]T` are all pointer types — an
    /// optional, an error union, an array, a generic application read through
    /// the arguments it is given, a type alias this file declares, and a
    /// container spelled out in place and read through its fields. A name this
    /// file does not declare is a name and nothing more, so it answers "no";
    /// that is what keeps a `*std.ArrayList(u8)` sink from being read as an
    /// alias of the receiver. Every other shape, and a walk that runs out of
    /// depth, answers "may name", which leaves the warning in place.
    fn typeMayNameReceiver(self: Solver, type_node: u32, method: u32, depth: u32) bool {
        if (depth >= 8 or type_node == 0 or type_node >= self.query.tree.nodes.len) return true;
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        const datas = tree.nodes.items(.data);
        if (call_resolver.isContainerTag(tags[type_node])) return self.containerMayNameReceiver(type_node, method, depth + 1);
        switch (tags[type_node]) {
            .ptr_type, .ptr_type_aligned, .ptr_type_bit_range, .ptr_type_sentinel => {
                const pointer = tree.fullPtrType(@enumFromInt(type_node)) orelse return true;
                return self.typeMayNameReceiver(@intFromEnum(pointer.ast.child_type), method, depth + 1);
            },
            .optional_type => return self.typeMayNameReceiver(@intFromEnum(datas[type_node].node), method, depth + 1),
            .error_union => return self.typeMayNameReceiver(@intFromEnum(datas[type_node].node_and_node[1]), method, depth + 1),
            .array_type => return self.typeMayNameReceiver(
                @intFromEnum(tree.arrayType(@enumFromInt(type_node)).ast.elem_type),
                method,
                depth + 1,
            ),
            .array_type_sentinel => return self.typeMayNameReceiver(
                @intFromEnum(tree.arrayTypeSentinel(@enumFromInt(type_node)).ast.elem_type),
                method,
                depth + 1,
            ),
            .call, .call_comma, .call_one, .call_one_comma => {
                // A generic application is read through what it is given, so
                // `ArrayList(*App)` is seen for what it holds while
                // `ArrayList(u8)` is not mistaken for one.
                const call = fullCall(tree, type_node) orelse return true;
                const container = constructor_facts.enclosingContainer(self.query, method) orelse return true;
                if (constructor_facts.denotesContainer(self.query, type_node, container)) return true;
                for (call.ast.params) |argument| {
                    if (self.typeMayNameReceiver(@intFromEnum(argument), method, depth + 1)) return true;
                }
                return false;
            },
            .identifier, .field_access => return self.namedTypeMayNameReceiver(type_node, method, depth),
            else => return true,
        }
    }

    /// A name written in a type position: the receiver's own container, a type
    /// alias this file declares, a built-in type name that cannot hold a
    /// pointer, or a name this file cannot read at all.
    fn namedTypeMayNameReceiver(self: Solver, type_node: u32, method: u32, depth: u32) bool {
        const tree = self.query.tree;
        const name = tree.tokenSlice(tree.nodes.items(.main_token)[type_node]);
        // `const X: type = ...` describes the value the alias was given, which
        // this file can read; `comptime T: type` names whatever the
        // instantiation decides, which it cannot.
        if (std.mem.eql(u8, name, "type")) {
            const declared = self.declaredTypeNode(type_node) orelse return true;
            return self.typeMayNameReceiver(declared, method, depth + 1);
        }
        if (tree.nodeTag(@enumFromInt(type_node)) == .identifier and isBuiltinTypeName(name)) return false;
        const container = constructor_facts.enclosingContainer(self.query, method) orelse return true;
        if (constructor_facts.denotesContainer(self.query, type_node, container)) return true;
        const declared = self.declaredTypeNode(type_node) orelse return false;
        return self.typeMayNameReceiver(declared, method, depth + 1);
    }

    /// The fields of a container spelled out in a parameter, read for one that
    /// could point at the receiver. An enum and an opaque hold no storage, so
    /// neither names anything, and a method declares a function rather than
    /// storage: a value of the type reaches no receiver through one, so a
    /// container that carries its own methods beside a plain field still says
    /// what that field holds. `fn append(self: *Sink, ...)` is therefore no
    /// reason to read `*Sink` as an alias of a `Session` receiver, while every
    /// other unreadable member may still hold storage and answers as before.
    fn containerMayNameReceiver(self: Solver, type_node: u32, method: u32, depth: u32) bool {
        const tree = self.query.tree;
        const tags = tree.nodes.items(.tag);
        if (depth >= 8 or type_node >= tree.nodes.len) return true;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        const full = tree.fullContainerDecl(&buffer, @enumFromInt(type_node)) orelse return true;
        const keyword = tree.tokenSlice(full.ast.main_token);
        if (std.mem.eql(u8, keyword, "enum") or std.mem.eql(u8, keyword, "opaque")) return false;
        for (full.ast.members) |member| {
            if (@intFromEnum(member) >= tags.len) return true;
            // A method declares a function rather than storage, so the walk
            // reads the fields this container holds and not the functions it
            // also declares. `treeFnProto` is where this file already answers
            // "is this member a function declaration", so that answer is read
            // from there rather than from a second list of prototype tags.
            var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;
            if (constructor_facts.treeFnProto(tree, @intFromEnum(member), &proto_buffer) != null) continue;
            switch (tags[@intFromEnum(member)]) {
                .container_field, .container_field_init, .container_field_align => {},
                // A member this scan cannot read may still hold storage.
                else => return true,
            }
            const field = tree.fullContainerField(member) orelse return true;
            const written = field.ast.type_expr.unwrap() orelse return true;
            if (self.typeMayNameReceiver(@intFromEnum(written), method, depth + 1)) return true;
        }
        return false;
    }

    /// The type a local alias stands for: its annotation when that annotation
    /// is a real type, and the value it was given when the annotation is
    /// `type`, which describes the alias itself rather than the instances that
    /// value names.
    fn declaredTypeNode(self: Solver, type_node: u32) ?u32 {
        const candidate = self.bindingCandidate(type_node) orelse return null;
        if (candidate.kind != .variable) return null;
        const full = self.query.tree.fullVarDecl(@enumFromInt(candidate.node)) orelse return null;
        const written = full.ast.type_node.unwrap() orelse return @intFromEnum(full.ast.init_node.unwrap() orelse return null);
        if (typeNodeIsTypeKeyword(self.query.tree, @intFromEnum(written), self.query.tree.nodes.items(.tag))) {
            return @intFromEnum(full.ast.init_node.unwrap() orelse return null);
        }
        return @intFromEnum(written);
    }
};

const EffectScan = struct {
    base: Path,
    suffix: []const []const u8,
    depth: u32,
    /// The declaration this scan is reading, so an exit of a function nested
    /// inside its body is not mistaken for one of its own.
    method: u32,
    /// Whether the caller can carry on after this call fails, which is what
    /// puts the error path — and the `errdefer` bodies that run on it — into
    /// the state the caller observes.
    observes_failure: bool = false,
    /// Whether a write this scan reads can install the place in the object the
    /// caller passed. A by-value receiver gets the caller's value, not the
    /// caller's storage, so its writes only invalidate.
    installs: bool = true,
    effect: Effect = .untouched,

    /// The storage this scan is about, as the point query spells it.
    fn place(self: *const EffectScan) Path {
        var result = Path{ .root = self.base.root };
        result.len = self.suffix.len;
        for (self.suffix, 0..) |name, index| result.names[index] = name;
        return result;
    }
};

/// The answers are read as a strength order, so the paths an installation has
/// to cover decide it: an exit that reaches the scope's end without installing
/// outranks the installation, and a rollback outranks both.
fn effectStrength(effect: Effect) u3 {
    return switch (effect) {
        .untouched => 0,
        .installs => 1,
        .not_installed => 2,
        .invalidated => 3,
    };
}

fn strongerEffect(current: Effect, found: Effect) Effect {
    return if (effectStrength(found) > effectStrength(current)) found else current;
}

fn mergeEffect(into: *Effect, found: Effect) void {
    into.* = strongerEffect(into.*, found);
}

fn pathTouches(solver: Solver, expr: u32, base: Path, suffix: []const []const u8) bool {
    return solver.writeReaches(expr, base.root, suffix);
}

/// The place a path `suffix` below the object `base` names, when the two are
/// still short enough to fit in one bounded path.
///
/// A callee's own receiver and the field path its caller wrote underneath it
/// are the two halves of one place, and `callEffectWithin` receives them apart.
/// Putting them back together spells the guarded bytes exactly as the point
/// query spells them, so a body this scan followed is judged against the same
/// place the guard was proved on.
fn placeUnder(base: Path, suffix: []const []const u8) ?Path {
    if (base.len + suffix.len > max_depth) return null;
    var result = base;
    for (suffix, 0..) |name, index| result.names[base.len + index] = name;
    result.len = base.len + suffix.len;
    return result;
}

/// The same question for the positions a callee actually writes through, where
/// a spelling the place builder cannot name still reaches the place.
fn writeTouches(solver: Solver, expr: u32, base: Path, suffix: []const []const u8) bool {
    return solver.writeMayReach(expr, base.root, suffix);
}

/// The built-in type names, the only names that are provably not optional
/// without a declaration to read.
fn isBuiltinTypeName(name: []const u8) bool {
    for ([_][]const u8{
        "bool",  "void",  "noreturn",  "type",         "anyerror",
        "usize", "isize", "anyopaque", "comptime_int", "comptime_float",
        "f16",   "f32",   "f64",       "f80",          "f128",
    }) |builtin| {
        if (std.mem.eql(u8, name, builtin)) return true;
    }
    if (name.len < 2 or (name[0] != 'i' and name[0] != 'u')) return false;
    for (name[1..]) |digit| if (digit < '0' or digit > '9') return false;
    return true;
}

/// Does `type_node` spell the `type` keyword? The tree carries it as a plain
/// identifier rather than a node of its own, and an annotation of `type`
/// describes the type value a declaration holds instead of the instances that
/// value names.
fn typeNodeIsTypeKeyword(
    tree: *const std.zig.Ast,
    type_node: u32,
    tags: []const std.zig.Ast.Node.Tag,
) bool {
    if (type_node >= tags.len or tags[type_node] != .identifier) return false;
    const token = tree.nodeMainToken(@enumFromInt(type_node));
    if (token >= tree.tokens.len) return false;
    return std.mem.eql(u8, tree.tokenSlice(token), "type");
}

fn isCallTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .call, .call_comma, .call_one, .call_one_comma => true,
        else => false,
    };
}

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

fn fullCall(tree: *const std.zig.Ast, node: u32) ?std.zig.Ast.full.Call {
    if (node >= tree.nodes.len) return null;
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    return tree.fullCall(&buffer, @enumFromInt(node));
}

fn functionBody(tree: *const std.zig.Ast, method: u32) ?u32 {
    if (method >= tree.nodes.len or tree.nodeTag(@enumFromInt(method)) != .fn_decl) return null;
    const body = @intFromEnum(tree.nodes.items(.data)[method].node_and_node[1]);
    if (body == 0 or body >= tree.nodes.len) return null;
    return body;
}

fn methodNameToken(tree: *const std.zig.Ast, method: u32) ?u32 {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = constructor_facts.treeFnProto(tree, method, &buffer) orelse return null;
    return proto.name_token;
}

/// The token that names a method's receiver.
///
/// A parameter's own node is the type it was written with, so `self: *Owner`
/// makes the parameter the `*Owner` node and its main token the `*`. The name
/// is the identifier in front of the colon, which is the token the lexical
/// index resolved a use of that name to: reading it from the parameter's main
/// token instead answers "this method has no receiver" for every receiver a
/// caller could actually establish a field on.
fn receiverNameToken(tree: *const std.zig.Ast, method: u32) ?u32 {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = constructor_facts.treeFnProto(tree, method, &buffer) orelse return null;
    var params = proto.iterate(tree);
    const receiver = params.next() orelse return null;
    // A receiver is typed: `fn read(self)` names no storage a caller could
    // establish a field on.
    if (receiver.type_expr == null) return null;
    const name_token = receiver.name_token orelse return null;
    if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return null;
    return @intCast(name_token);
}

/// `*T` or `*const T` only: an optional or doubly indirect receiver is not the
/// storage the field facts describe.
fn receiverIsSinglePointer(tree: *const std.zig.Ast, method: u32) bool {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = constructor_facts.treeFnProto(tree, method, &buffer) orelse return false;
    if (proto.ast.params.len == 0) return false;
    const written = constructor_facts.parameterTypeNode(tree, @intFromEnum(proto.ast.params[0])) orelse return false;
    if (written >= tree.nodes.len or tree.nodeTag(@enumFromInt(written)) != .ptr_type_aligned) return false;
    const pointer = tree.fullPtrType(@enumFromInt(written)) orelse return false;
    const token = tree.nodes.items(.main_token)[written];
    if (token >= tree.tokens.len or tree.tokenTag(token) != .asterisk) return false;
    const child = @intFromEnum(pointer.ast.child_type);
    return child < tree.nodes.len and tree.nodeTag(@enumFromInt(child)) != .ptr_type_aligned;
}

/// The `field_access` a call reads its callee from, or null for every other
/// expression shape.
fn calleeFieldAccess(tree: *const std.zig.Ast, node: u32) ?@FieldType(std.zig.Ast.Node.Data, "node_and_token") {
    if (node >= tree.nodes.len or !isCallTag(tree.nodeTag(@enumFromInt(node)))) return null;
    const call = fullCall(tree, node) orelse return null;
    const fn_expr = @intFromEnum(call.ast.fn_expr);
    if (fn_expr >= tree.nodes.len or tree.nodeTag(@enumFromInt(fn_expr)) != .field_access) return null;
    return tree.nodes.items(.data)[fn_expr].node_and_token;
}

fn containsNode(tree: *const std.zig.Ast, node: u32, target: u32) bool {
    if (node == 0 or node >= tree.nodes.len or target >= tree.nodes.len) return false;
    return tree.firstToken(@enumFromInt(node)) <= tree.firstToken(@enumFromInt(target)) and
        tree.lastToken(@enumFromInt(target)) <= tree.lastToken(@enumFromInt(node));
}

fn isNullLiteral(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    const main_tokens = tree.nodes.items(.main_token);
    if (node >= tags.len or tags[node] != .identifier) return false;
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

test "caller context: every caller has to establish the exact field" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "payload guarded caller", .input = callerFixture("if (self.field) |*held| {\n_ = held;\nself.read();\n}", ""), .warnings = 0 },
        .{ .name = "null compared caller", .input = callerFixture("if (self.field != null) {\nself.read();\n}", ""), .warnings = 0 },
        .{ .name = "early exit caller", .input = callerFixture("if (self.field == null) return 0;\nself.read();", ""), .warnings = 0 },
        .{ .name = "unguarded caller", .input = callerFixture("self.read();", ""), .warnings = 1 },
        .{ .name = "sibling field guarded", .input = callerFixture("if (self.other != null) {\nself.read();\n}", ""), .warnings = 1 },
        .{ .name = "cleared before the call", .input = callerFixture("if (self.field != null) {\nself.field = null;\nself.read();\n}", ""), .warnings = 1 },
        .{ .name = "escaping method reference", .input = callerFixture("if (self.field != null) {\nconst alias: *const fn (*Owner) void = Owner.read;\n_ = alias;\nself.read();\n}", ""), .warnings = 1 },
        .{ .name = "public method", .input = callerFixture("if (self.field != null) {\nself.read();\n}", "pub "), .warnings = 1 },
        .{ .name = "no caller in this file", .input = callerFixture("", ""), .warnings = 1 },
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
            std.debug.print("caller context scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
}

test "constructed owner: field facts survive one nesting and one teardown" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "constructed owner", .input = ownerFixture("var owner = try makeOwner();\nreturn owner.field.?;"), .warnings = 0 },
        .{ .name = "nested constructed owner", .input = ownerFixture("var wrapper = try makeWrapper();\nreturn wrapper.inner.field.?;"), .warnings = 0 },
        .{ .name = "struct literal owner", .input = ownerFixture("var owner = Owner{ .field = 1 };\nreturn owner.field.?;"), .warnings = 0 },
        .{ .name = "bare default owner", .input = ownerFixture("var owner = Owner{};\nreturn owner.field.?;"), .warnings = 1 },
        .{ .name = "undefined owner", .input = ownerFixture("var owner: Owner = undefined;\nreturn owner.field.?;"), .warnings = 1 },
        .{ .name = "recovered constructor error", .input = ownerFixture("var owner = makeOwner() catch Owner{};\nreturn owner.field.?;"), .warnings = 1 },
        .{ .name = "read after teardown", .input = ownerFixture("var owner = try makeOwner();\nowner.deinit();\nreturn owner.field.?;"), .warnings = 1 },
        .{ .name = "replacement after teardown", .input = ownerFixture("var owner = try makeOwner();\nowner.deinit();\nowner.field = 1;\nreturn owner.field.?;"), .warnings = 0 },
        .{ .name = "unrelated owner beside a nullable target", .input = ownerFixture("var target: Owner = .{};\nvar other = try makeOwner();\n_ = other;\nreturn target.field.?;"), .warnings = 1 },
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
            std.debug.print("constructed owner scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
}

test "aliased writes and optional-valued pointers never carry a fact" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "pointer to an optional", .input = aliasFixture("var owner = Owner{};\nvar maybe: ?u32 = null;\nowner.installFromPointer(&maybe);\n_ = owner.field.?;"), .warnings = 1 },
        .{ .name = "pointer to a plain value", .input = aliasFixture("var owner = Owner{};\nvar plain: u32 = 1;\nowner.installFromPlainPointer(&plain);\n_ = owner.field.?;"), .warnings = 0 },
        .{ .name = "nullable alias type", .input = aliasFixture("var owner = Owner{};\nvar maybe: AliasedField = null;\nowner.installFromAlias(maybe);\n_ = owner.field.?;"), .warnings = 1 },
        .{ .name = "direct clear", .input = aliasFixture("var owner = Owner{ .field = 1 };\nowner.clear();\n_ = owner.field.?;"), .warnings = 1 },
        .{ .name = "clear through an alias", .input = aliasFixture("var owner = Owner{ .field = 1 };\nowner.clearThroughAlias();\n_ = owner.field.?;"), .warnings = 1 },
        .{ .name = "replacement through an alias", .input = aliasFixture("var owner = Owner{ .field = 1 };\nvar me = owner;\nme.field = 2;\n_ = owner.field.?;"), .warnings = 0 },
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
            std.debug.print("alias scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
}

fn aliasFixture(comptime body: [:0]const u8) [:0]const u8 {
    return "const Owner = struct {\n" ++
        "field: ?u32 = null,\n\n" ++
        "fn installFromPointer(self: *Owner, src: *?u32) void {\nself.field = src.*;\n}\n\n" ++
        "fn installFromPlainPointer(self: *Owner, src: *u32) void {\nself.field = src.*;\n}\n\n" ++
        "fn installFromAlias(self: *Owner, value: AliasedField) void {\nself.field = value;\n}\n\n" ++
        "fn clear(self: *Owner) void {\nself.field = null;\n}\n\n" ++
        "fn clearThroughAlias(self: *Owner) void {\nvar me = self;\nme.field = null;\n}\n" ++
        "};\n\n" ++
        "const MaybeField = ?u32;\n" ++
        "const AliasedField = MaybeField;\n\n" ++
        "test \"owner runs\" {\n" ++ body ++ "\n}\n";
}

fn callerFixture(
    comptime call_site: []const u8,
    comptime visibility: []const u8,
) [:0]const u8 {
    return "const Owner = struct {\n" ++
        "field: ?u32 = null,\nother: ?u32 = null,\n\n" ++
        visibility ++ "fn read(self: *Owner) void {\n_ = self.field.?;\n}\n\n" ++
        "fn drive(self: *Owner) u32 {\n" ++ call_site ++ "\nreturn 0;\n}\n\n" ++
        "};\n\n" ++
        "pub fn exercise(owner: *Owner) u32 {\nreturn owner.drive();\n}\n\n" ++
        "test \"drive runs\" {\nvar owner: Owner = .{ .field = 1, .other = 1 };\n_ = owner.drive();\n}\n";
}

fn ownerFixture(comptime body: []const u8) [:0]const u8 {
    return "const Owner = struct {\n" ++
        "field: ?u32 = null,\n\n" ++
        "fn deinit(self: *Owner) void {\nself.field = null;\n}\n" ++
        "};\n\n" ++
        "const Wrapper = struct {\n" ++
        "inner: Owner = .{},\n" ++
        "};\n\n" ++
        "fn makeOwner() error{No}!Owner {\nreturn .{ .field = 1 };\n}\n\n" ++
        "fn makeWrapper() error{No}!Wrapper {\nreturn .{ .inner = try makeOwner() };\n}\n\n" ++
        "fn read() error{No}!u32 {\n" ++ body ++ "\n}\n";
}

test "a global the receiver pointer may stand for: alias, literal, disjoint field" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "aliased global type", .input = foreignGlobalFixture("const Alias = Session;\nvar session: Alias = .{};", "session.region = null;", "session"), .warnings = 1 },
        .{ .name = "global type read from its literal", .input = foreignGlobalFixture("var session = Session{};", "session.region = null;", "session"), .warnings = 1 },
        .{ .name = "divergent field of that global", .input = foreignGlobalFixture("var session: Session = .{};", "session.marks = 0;", "session"), .warnings = 0 },
        .{ .name = "global of another container", .input = foreignGlobalFixture("const Other = struct {\nregion: ?Region = null,\n};\nvar session: Other = .{};\nvar current: Session = .{};", "session.region = null;", "current"), .warnings = 0 },
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
            std.debug.print("foreign global scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
}

/// A receiver a caller fills with the address of a module-level object, and a
/// method on a foreign parameter that writes one field of that object. The
/// declaration is written at file scope, where no container encloses it, and
/// the object the driver calls is named apart from the one that body writes.
fn foreignGlobalFixture(
    comptime declaration: [:0]const u8,
    comptime drop_body: [:0]const u8,
    comptime receiver: [:0]const u8,
) [:0]const u8 {
    return "const Region = struct {\nwidth: u16 = 80,\n};\n\n" ++
        "const Session = struct {\nregion: ?Region = null,\nmarks: u8 = 0,\n\n" ++
        "fn readAfterDrop(self: *Session, sink: *Sink) u16 {\nsink.drop();\nreturn self.region.?.width;\n}\n" ++
        "};\n\n" ++
        "const Sink = struct {\nfn drop(self: *Sink) void {\n" ++ drop_body ++ "\n}\n};\n\n" ++
        declaration ++ "\n\n" ++
        "fn drive(sink: *Sink) u16 {\n" ++ receiver ++ ".region = .{ .width = 80 };\n" ++
        "return " ++ receiver ++ ".readAfterDrop(sink);\n}\n\n" ++
        "test \"drive runs\" {\nvar sink: Sink = .{};\n_ = drive(&sink);\n}\n";
}

test "a nested install reaches the caller through a pointer receiver only" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "pointer receiver", .input = nestedInstallFixture("*Owner"), .warnings = 0 },
        .{ .name = "by-value receiver", .input = nestedInstallFixture("Owner"), .warnings = 1 },
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
            std.debug.print("nested install scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
}

/// The same body under both receiver spellings: `mine.installDirect` installs
/// the receiver's own field through a pointer receiver either way, and only one
/// of the two receivers is the caller's storage.
fn nestedInstallFixture(comptime receiver: [:0]const u8) [:0]const u8 {
    return "const Owner = struct {\nfield: ?u32 = null,\n\n" ++
        "fn installNested(self: " ++ receiver ++ ", value: u32) void {\nvar mine = self;\nmine.installDirect(value);\n}\n\n" ++
        "fn installDirect(self: *Owner, value: u32) void {\nself.field = value;\n}\n\n" ++
        "fn readField(self: *Owner) u32 {\nreturn self.field.?;\n}\n" ++
        "};\n\n" ++
        "fn drive() u32 {\nvar owner: Owner = .{};\nowner.installNested(1);\nreturn owner.readField();\n}\n\n" ++
        "test \"drive runs\" {\n_ = drive();\n}\n";
}

test "an argument evaluated after the object a generic call is handed runs first" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "cleared in the last argument", .input = lateArgumentFixture("&sink, value, self.clear()"), .warnings = 1 },
        .{ .name = "cleared in the first argument", .input = lateArgumentFixture("&sink, self.clear(), value"), .warnings = 1 },
        .{ .name = "nothing cleared after the hand-over", .input = lateArgumentFixture("&sink, value, 0"), .warnings = 0 },
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
            std.debug.print("late argument scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
    }
}

/// The owner the generic function is handed is installed by a `try` ahead of
/// the call, so only an operand the call evaluates after the hand-over can take
/// the field back out before the body runs.
fn lateArgumentFixture(comptime arguments: [:0]const u8) [:0]const u8 {
    return "const Owner = struct {\nindex: ?u32 = null,\n\n" ++
        "fn ensure(self: *Owner) !void {\nif (self.index == null) self.index = 0;\n}\n\n" ++
        "fn clear(self: *Owner) u8 {\nself.index = null;\nreturn 0;\n}\n\n" ++
        "fn append(self: *Owner, value: u8) void {\nself.index.? += value;\n}\n\n" ++
        "fn process(self: *Owner, value: u8) !void {\n" ++
        "try self.ensure();\n" ++
        "var sink: Sink = .{ .owner = self };\n" ++
        "scan(" ++ arguments ++ ");\n" ++
        "}\n};\n\n" ++
        "const Sink = struct {\nowner: *Owner,\n\n" ++
        "fn append(self: *Sink, value: u8) void {\nself.owner.append(value);\n}\n" ++
        "};\n\n" ++
        "fn scan(sink: anytype, value: u8, extra: u8) void {\n_ = extra;\nsink.append(value);\n}\n\n" ++
        "test \"owner runs\" {\nvar owner: Owner = .{};\ntry owner.process(1, 0);\n}\n";
}

/// The 1-based line `needle` is written on, for a fixture whose findings are
/// pinned to a line rather than only counted.
fn lineOf(code: []const u8, needle: []const u8) usize {
    const offset = std.mem.indexOf(u8, code, needle) orelse return 0;
    return 1 + std.mem.count(u8, code[0..offset], "\n");
}

test "an argument that clears the field before the callee is entered defeats the guard" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "cleared in the argument", .input = calleeArgumentFixture("self.wipe() +% value"), .warnings = 1 },
        .{ .name = "nothing cleared in the argument", .input = calleeArgumentFixture("value"), .warnings = 0 },
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
            std.debug.print("callee argument scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| {
            try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
            // The report belongs to the unwrap the callee reaches, never to the
            // argument the caller wrote in front of the call.
            try std.testing.expectEqual(lineOf(case.input, "self.index.?"), diagnostic.range.start.line);
        }
    }
}

/// A caller that installs the field and then calls the method that unwraps it,
/// handing the call the `argument` it evaluates before the body is entered.
/// Zig evaluates the receiver, then every argument, and reaches the body only
/// after the last of them, so an argument that clears the field decides what
/// the callee is entered with however well the statement before it is guarded.
fn calleeArgumentFixture(comptime argument: [:0]const u8) [:0]const u8 {
    return "const Owner = struct {\nindex: ?u32 = null,\n\n" ++
        "fn ensure(self: *Owner) !void {\nif (self.index == null) self.index = 0;\n}\n\n" ++
        "fn wipe(self: *Owner) u8 {\nself.index = null;\nreturn 0;\n}\n\n" ++
        "fn add(self: *Owner, value: u8) void {\nself.index.? += value;\n}\n\n" ++
        "fn process(self: *Owner, value: u8) !void {\n" ++
        "try self.ensure();\n" ++
        "self.add(" ++ argument ++ ");\n" ++
        "}\n};\n\n" ++
        "test \"owner runs\" {\nvar owner: Owner = .{};\ntry owner.process(3);\n}\n";
}

test "a swallowed installer failure keeps the warning at the unwrap it reaches" {
    const cases = [_]struct { name: []const u8, input: [:0]const u8, warnings: usize }{
        .{ .name = "failure swallowed", .input = swallowedInstallerFixture("_ = self.ensure(fail) catch {};"), .warnings = 1 },
        .{ .name = "failure propagated", .input = swallowedInstallerFixture("try self.ensure(fail);"), .warnings = 0 },
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
            std.debug.print("swallowed installer scenario: {s}\n", .{case.name});
            return err;
        };
        for (diagnostics.items) |diagnostic| {
            try std.testing.expectEqualStrings("optional-unwrap", diagnostic.rule_id);
            // The installer is what the caller reaches, and a handler that
            // carries on is not an unwrap site: the one report belongs to the
            // `.?` inside the method the failure leaves unreached.
            try std.testing.expectEqual(lineOf(case.input, "self.index.?"), diagnostic.range.start.line);
            try std.testing.expect(lineOf(case.input, "catch {};") != diagnostic.range.start.line);
        }
    }
}

/// An installer that can fail, called through `install` before the method that
/// unwraps the field the installer fills. A propagated failure leaves the
/// caller before the call, so only the success path reaches the unwrap; a
/// swallowed one carries on into it with whatever the failure left behind.
fn swallowedInstallerFixture(comptime install: [:0]const u8) [:0]const u8 {
    return "const Owner = struct {\nindex: ?u32 = null,\n\n" ++
        "fn ensure(self: *Owner, fail: bool) error{Unavailable}!void {\n" ++
        "if (fail) return error.Unavailable;\n" ++
        "if (self.index == null) self.index = 0;\n}\n\n" ++
        "fn add(self: *Owner, value: u8) void {\nself.index.? += value;\n}\n\n" ++
        "fn process(self: *Owner, value: u8, fail: bool) !void {\n" ++ install ++ "\n" ++
        "self.add(value);\n" ++
        "}\n};\n\n" ++
        "test \"owner runs\" {\nvar owner: Owner = .{};\ntry owner.process(3, false);\n}\n";
}
