const std = @import("std");
const ids = @import("../ids.zig");
const BuildMetadata = @import("../build_metadata.zig").BuildMetadata;
const Cfg = @import("../cfg.zig").Cfg;
const AbstractValue = @import("value.zig").AbstractValue;
const Constraint = @import("constraints.zig").Constraint;
const ConstraintManager = @import("constraints.zig").ConstraintManager;
const Environment = @import("env.zig").Environment;
const store_mod = @import("store.zig");
const VarId = ids.VarId;
const CfgNodeId = ids.CfgNodeId;
const ResourceState = store_mod.ResourceState;
const Store = store_mod.Store;
const StoreViolation = store_mod.StoreViolation;

/// Represents a position in the analysis - a specific point in the CFG.
/// ProgramPoint identifies a CFG node plus whether we are at the pre-state
/// (before the node executes) or post-state (after the node executes).
/// Includes the CFG pointer to distinguish nodes from different CFGs during
/// interprocedural analysis.
pub const ProgramPoint = struct {
    /// Index of the CFG node
    node_index: CfgNodeId,
    /// Whether this is a pre-state (before node execution) or post-state (after)
    kind: Kind,
    /// The CFG this node belongs to (for interprocedural analysis)
    cfg: *const Cfg,

    pub const Kind = enum {
        /// Before the CFG node is executed
        pre,
        /// After the CFG node has been executed
        post,
    };

    pub fn init(node_index: CfgNodeId, kind: Kind, cfg: *const Cfg) ProgramPoint {
        return .{
            .node_index = node_index,
            .kind = kind,
            .cfg = cfg,
        };
    }

    pub fn initPre(node_index: CfgNodeId, cfg: *const Cfg) ProgramPoint {
        return init(node_index, .pre, cfg);
    }

    pub fn initPost(node_index: CfgNodeId, cfg: *const Cfg) ProgramPoint {
        return init(node_index, .post, cfg);
    }

    pub fn eql(self: ProgramPoint, other: ProgramPoint) bool {
        return self.node_index == other.node_index and
            self.kind == other.kind and
            self.cfg == other.cfg;
    }

    pub fn hash(self: ProgramPoint) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const node_index = ids.cfgIndex(self.node_index);
        hasher.update(std.mem.asBytes(&node_index));
        hasher.update(std.mem.asBytes(&self.kind));
        hasher.update(std.mem.asBytes(&@intFromPtr(self.cfg)));
        return hasher.final();
    }
};

/// Error state of the program: whether we are on an error path or success path.
pub const ErrorState = enum {
    /// Normal execution path (no error)
    normal,
    /// Error path (error has been produced but not yet handled)
    error_active,
    /// Error has been caught and handled
    error_handled,
};

/// Which arm of a `catch` expression a path ran. The guarded call produced
/// the value, or its handler did.
pub const CatchArm = enum {
    /// The guarded call succeeded, so it produced the value.
    success,
    /// The guarded call failed and its handler ran instead.
    failure,
};

/// How many `catch` arm decisions a path carries in the state itself. A path
/// needs one per `catch` expression whose arms it has entered and not yet
/// read, which is the handler chain it is nested in; a path carrying more
/// than this spills the rest into a list it owns, so a chain of any depth
/// keeps every decision a binding below it is about to read.
pub const inline_pending_catch_arms: usize = 4;

/// One `catch` expression's arm, as this path ran it.
const CatchArmFact = struct {
    /// AST node of the `catch` expression the arm belongs to.
    catch_node: u32,
    arm: CatchArm,
};

/// The `catch` expressions whose arms a path has entered and not yet bound,
/// and which arm each one ran, oldest first.
///
/// Recorded per expression rather than as one flag because a `catch` nested in
/// another handler's value decides its own arm after the outer one, and its
/// success edge returns the error state to normal - so the state alone cannot
/// say which of the two calls on the path produced the binding.
pub const PendingCatchArms = struct {
    /// The decisions a path carries without allocating, oldest first.
    inline_facts: [inline_pending_catch_arms]CatchArmFact = no_facts,
    inline_count: u8 = 0,
    /// The decisions past the inline ones, oldest first. Allocated only once a
    /// path really carries more pending arms than the inline ones hold, so the
    /// common chain of four or fewer costs nothing.
    ///
    /// Dropping the outermost decisions instead of spilling them would be a
    /// silent truncation: a handler nested deeper than the inline ones reads
    /// the innermost decisions, but a binding under the whole chain reads the
    /// outermost one, and losing it hands that binding the wrong call.
    spilled: ?std.ArrayList(CatchArmFact) = null,

    const no_facts: [inline_pending_catch_arms]CatchArmFact =
        [_]CatchArmFact{.{ .catch_node = 0, .arm = .success }} ** inline_pending_catch_arms;

    /// How many arms this path carries, inline and spilled together.
    pub fn len(self: *const PendingCatchArms) usize {
        return self.inline_count + self.spillLen();
    }

    fn spillLen(self: *const PendingCatchArms) usize {
        const spilled = self.spilled orelse return 0;
        return spilled.items.len;
    }

    /// The arm this path carries at `index`, oldest first.
    fn factAt(self: *const PendingCatchArms, index: usize) ?CatchArmFact {
        if (index < self.inline_count) return self.inline_facts[index];
        const spilled = self.spilled orelse return null;
        const rest = index - self.inline_count;
        if (rest >= spilled.items.len) return null;
        return spilled.items[rest];
    }

    /// Record the arm a path took out of `catch_node`.
    ///
    /// Fails only when the spill has to grow and the allocator cannot, which
    /// leaves this path's arms exactly as they were.
    pub fn push(
        self: *PendingCatchArms,
        allocator: std.mem.Allocator,
        catch_node: u32,
        arm: CatchArm,
    ) std.mem.Allocator.Error!void {
        // Entering the same `catch` again re-decides its own arm, so the
        // newest decision is the one that holds.
        var i = self.len();
        while (i > 0) {
            i -= 1;
            const fact = self.factAt(i) orelse continue;
            if (fact.catch_node != catch_node) continue;
            self.setArmAt(i, arm);
            return;
        }
        // The inline facts are the oldest arms of the path, so room left in
        // them is room ahead of the spill: a new decision goes right after the
        // newest one, which lands inline exactly when the spill is empty.
        if (self.inline_count < inline_pending_catch_arms) {
            std.debug.assert(self.spilled == null);
            self.inline_facts[self.inline_count] = .{ .catch_node = catch_node, .arm = arm };
            self.inline_count += 1;
            return;
        }
        if (self.spilled) |*spilled| {
            try spilled.append(allocator, .{ .catch_node = catch_node, .arm = arm });
            return;
        }
        var spilled: std.ArrayList(CatchArmFact) = .empty;
        errdefer spilled.deinit(allocator);
        try spilled.append(allocator, .{ .catch_node = catch_node, .arm = arm });
        self.spilled = spilled;
    }

    /// Re-decide the arm this path already carries for one expression.
    fn setArmAt(self: *PendingCatchArms, index: usize, arm: CatchArm) void {
        if (index < self.inline_count) {
            self.inline_facts[index].arm = arm;
            return;
        }
        const spilled = self.spilled orelse return;
        const rest = index - self.inline_count;
        if (rest >= spilled.items.len) return;
        spilled.items[rest].arm = arm;
    }

    /// The arm this path took out of `catch_node`, or null when it carries no
    /// decision for that expression.
    pub fn get(self: *const PendingCatchArms, catch_node: u32) ?CatchArm {
        var i = self.len();
        while (i > 0) {
            i -= 1;
            const fact = self.factAt(i) orelse continue;
            if (fact.catch_node == catch_node) return fact.arm;
        }
        return null;
    }

    /// Drop the arms of the `catch` expressions named in `nodes`, which a
    /// binding has just read: the value they produced is bound here, so no
    /// point below that binding is still holding it. A path that carried more
    /// arms than the inline ones hold gives its spill back here, so settling a
    /// chain does not keep the buffer alive for the rest of the analysis.
    ///
    /// The arms that survive keep their order, and the oldest of them move back
    /// into the inline slots the settled ones left free. That is what keeps the
    /// inline facts the first arms of the path: a later push lands after every
    /// arm the path still carries instead of in a hole below them, which would
    /// publish a settled arm in place of the new one.
    pub fn forget(self: *PendingCatchArms, allocator: std.mem.Allocator, nodes: []const u32) void {
        var kept: usize = 0;
        for (self.inline_facts[0..self.inline_count]) |fact| {
            if (std.mem.indexOfScalar(u32, nodes, fact.catch_node) != null) continue;
            self.inline_facts[kept] = fact;
            kept += 1;
        }

        if (self.spilled) |*spilled| {
            var spill_kept: usize = 0;
            for (spilled.items) |fact| {
                if (std.mem.indexOfScalar(u32, nodes, fact.catch_node) != null) continue;
                spilled.items[spill_kept] = fact;
                spill_kept += 1;
            }
            const room = inline_pending_catch_arms - kept;
            const moved = @min(room, spill_kept);
            std.mem.copyForwards(
                CatchArmFact,
                self.inline_facts[kept..][0..moved],
                spilled.items[0..moved],
            );
            kept += moved;
            // What stays spilled is what is left of it, oldest first and
            // without the holes the move left behind.
            std.mem.copyForwards(
                CatchArmFact,
                spilled.items[0 .. spill_kept - moved],
                spilled.items[moved..spill_kept],
            );
            spilled.shrinkRetainingCapacity(spill_kept - moved);
            if (spilled.items.len == 0) {
                spilled.deinit(allocator);
                self.spilled = null;
            }
        }
        self.inline_count = @intCast(kept);
        // A spill only ever holds what the inline facts have no room for.
        const inline_full: u8 = @intCast(inline_pending_catch_arms);
        if (self.spilled != null) std.debug.assert(self.inline_count == inline_full);
    }

    pub fn eql(self: *const PendingCatchArms, other: *const PendingCatchArms) bool {
        const total = self.len();
        if (total != other.len()) return false;
        var i: usize = 0;
        while (i < total) : (i += 1) {
            const left = self.factAt(i) orelse return false;
            const right = other.factAt(i) orelse return false;
            if (left.catch_node != right.catch_node or left.arm != right.arm) return false;
        }
        return true;
    }

    /// Join of two paths' pending arms.
    ///
    /// An arm both paths carry the same way survives: that expression decided
    /// the same thing either way, so a binding below it still names the same
    /// acquisition. An arm only one path carries, or one the two decide
    /// differently, is dropped - the value has two possible origins there, and
    /// keeping either of them would name a call the other path never made.
    ///
    /// Merging is what the graph does only after it has checked the two paths
    /// agree on their provenance, so this normally keeps everything; the
    /// per-expression reading is what makes it say so rather than erase every
    /// decision because one of them differs.
    pub fn join(
        self: *const PendingCatchArms,
        other: *const PendingCatchArms,
        allocator: std.mem.Allocator,
    ) std.mem.Allocator.Error!PendingCatchArms {
        var result: PendingCatchArms = .{};
        errdefer result.deinit(allocator);
        const total = self.len();
        var i: usize = 0;
        while (i < total) : (i += 1) {
            const fact = self.factAt(i) orelse continue;
            if (other.get(fact.catch_node) != fact.arm) continue;
            try result.push(allocator, fact.catch_node, fact.arm);
        }
        return result;
    }

    /// Copy the arms into arms that own their own spill.
    pub fn clone(self: *const PendingCatchArms, allocator: std.mem.Allocator) std.mem.Allocator.Error!PendingCatchArms {
        var copy: PendingCatchArms = .{
            .inline_facts = self.inline_facts,
            .inline_count = self.inline_count,
        };
        if (self.spilled) |spilled| {
            var new_spill: std.ArrayList(CatchArmFact) = .empty;
            errdefer new_spill.deinit(allocator);
            try new_spill.ensureTotalCapacityPrecise(allocator, spilled.items.len);
            new_spill.appendSliceAssumeCapacity(spilled.items);
            copy.spilled = new_spill;
        }
        return copy;
    }

    /// Give back the spill, if this path carries one.
    pub fn deinit(self: *PendingCatchArms, allocator: std.mem.Allocator) void {
        if (self.spilled) |*spilled| {
            spilled.deinit(allocator);
            self.spilled = null;
        }
    }

    pub fn updateHash(self: *const PendingCatchArms, hasher: *std.hash.Wyhash) void {
        const total = self.len();
        hasher.update(std.mem.asBytes(&total));
        for (self.inline_facts[0..self.inline_count]) |fact| {
            hasher.update(std.mem.asBytes(&fact.catch_node));
            hasher.update(std.mem.asBytes(&fact.arm));
        }
        if (self.spilled) |spilled| {
            for (spilled.items) |fact| {
                hasher.update(std.mem.asBytes(&fact.catch_node));
                hasher.update(std.mem.asBytes(&fact.arm));
            }
        }
    }
};

/// Represents a call site in the inline call stack.
/// Used to track interprocedural analysis context.
pub const CallSite = struct {
    /// CFG node index of the call instruction
    call_node: CfgNodeId,
    /// The CFG containing the call site
    caller_cfg: *const Cfg,
    /// Return point: the CFG node to continue from after the call returns
    return_node: CfgNodeId,
};

/// Key for identifying a widening point in a specific interprocedural context.
/// Used to track states at loop headers, the only points where a state can be
/// replaced after the point was already processed.
/// States from different calling contexts must not be merged, and neither must
/// states whose pending `catch` arms name a different acquisition: merging
/// those drops the arm they disagree on, which is the fact a binding below
/// the loop reads to know which call produced its value.
/// Executed ownership edges also partition the chains: a backedge that stored
/// a payload must not lose that transfer to a header that never stored it.
pub const WideningKey = struct {
    /// Hash of the ProgramPoint (node + CFG + pre/post)
    point_hash: u64,
    /// Hash of the calling context (inline depth + call stack), pending
    /// `catch` arms, and executed ownership edges
    context_hash: u64,

    pub fn init(point: ProgramPoint, state: *const ProgramState) WideningKey {
        return .{
            .point_hash = point.hash(),
            .context_hash = state.contextHash(),
        };
    }

    pub fn eql(self: WideningKey, other: WideningKey) bool {
        return self.point_hash == other.point_hash and
            self.context_hash == other.context_hash;
    }

    pub fn hash(self: WideningKey) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&self.point_hash));
        hasher.update(std.mem.asBytes(&self.context_hash));
        return hasher.final();
    }

    pub const HashContext = struct {
        pub fn hash(_: HashContext, key: WideningKey) u64 {
            return key.hash();
        }

        pub fn eql(_: HashContext, a: WideningKey, b: WideningKey) bool {
            return a.eql(b);
        }
    };
};

/// Copy the live items into a list sized for exactly those items.
///
/// `appendSlice` on an empty list rounds the request up through the list's
/// growth policy, so a state cloned per CFG node and per successor edge keeps
/// that slack alive for as long as the clone is retained.
fn cloneCallSites(list: std.ArrayList(CallSite), allocator: std.mem.Allocator) std.mem.Allocator.Error!std.ArrayList(CallSite) {
    var copy: std.ArrayList(CallSite) = .empty;
    try copy.ensureTotalCapacityPrecise(allocator, list.items.len);
    copy.appendSliceAssumeCapacity(list.items);
    return copy;
}

/// Abstract program state for path-sensitive analysis.
/// Stores the environment mapping variables to abstract values,
/// plus path constraints from branch conditions, and error state.
pub const ProgramState = struct {
    /// Environment mapping variables to abstract values
    env: Environment,
    /// Constraint manager for path conditions
    constraints: ConstraintManager,
    /// Store tracking heap/resource regions
    store: Store,
    /// Error state tracking (normal, error_active, error_handled)
    error_state: ErrorState,
    /// Which arm each `catch` expression on this path ran, for the ones whose
    /// binding has not been read yet
    catch_arms: PendingCatchArms = .{},
    /// Cached hash for efficient deduplication
    cached_hash: ?u64,
    /// Current inlining depth (0 = top-level function)
    inline_depth: u32,
    /// Call stack for interprocedural analysis (stored as indices into call_sites)
    call_stack: std.ArrayList(CallSite),
    /// Build metadata (target configuration, etc.) - shared pointer, not owned
    build_metadata: ?*const BuildMetadata,

    pub fn init(allocator: std.mem.Allocator) ProgramState {
        return .{
            .env = Environment.init(allocator),
            .constraints = ConstraintManager.init(allocator),
            .store = Store.init(allocator),
            .error_state = .normal,
            .cached_hash = null,
            .catch_arms = .{},
            .inline_depth = 0,
            .call_stack = .empty,
            .build_metadata = null,
        };
    }

    pub fn deinit(self: *ProgramState) void {
        const allocator = self.env.allocator;
        self.catch_arms.deinit(allocator);
        self.env.deinit();
        self.constraints.deinit();
        self.store.deinit();
        self.call_stack.deinit(allocator);
    }

    pub fn eql(self: *const ProgramState, other: *const ProgramState) bool {
        if (self.inline_depth != other.inline_depth) return false;
        if (!self.env.eql(&other.env)) return false;
        if (!self.constraints.eql(&other.constraints)) return false;
        if (!self.store.eql(&other.store)) return false;
        if (self.error_state != other.error_state) return false;
        if (!self.catch_arms.eql(&other.catch_arms)) return false;
        // Compare call stacks to distinguish different calling contexts
        if (self.call_stack.items.len != other.call_stack.items.len) return false;
        for (self.call_stack.items, other.call_stack.items) |cs1, cs2| {
            if (cs1.call_node != cs2.call_node or
                cs1.return_node != cs2.return_node or
                cs1.caller_cfg != cs2.caller_cfg)
            {
                return false;
            }
        }
        return true;
    }

    pub fn computeHash(self: *ProgramState) u64 {
        if (self.cached_hash) |h| return h;
        var hasher = std.hash.Wyhash.init(0);
        const env_hash = self.env.computeHash();
        hasher.update(std.mem.asBytes(&env_hash));
        const constraints_hash = self.constraints.computeHash();
        hasher.update(std.mem.asBytes(&constraints_hash));
        const store_hash = self.store.computeHash();
        hasher.update(std.mem.asBytes(&store_hash));
        hasher.update(std.mem.asBytes(&self.error_state));
        self.catch_arms.updateHash(&hasher);
        hasher.update(std.mem.asBytes(&self.inline_depth));
        // Include call stack in hash to distinguish different calling contexts
        for (self.call_stack.items) |cs| {
            const call_node = ids.cfgIndex(cs.call_node);
            const return_node = ids.cfgIndex(cs.return_node);
            hasher.update(std.mem.asBytes(&call_node));
            hasher.update(std.mem.asBytes(&return_node));
            hasher.update(std.mem.asBytes(&@intFromPtr(cs.caller_cfg)));
        }
        const h = hasher.final();
        self.cached_hash = h;
        return h;
    }

    pub fn clone(self: *const ProgramState, allocator: std.mem.Allocator) !ProgramState {
        var new_call_stack = try cloneCallSites(self.call_stack, allocator);
        errdefer new_call_stack.deinit(allocator);
        var new_env = try self.env.clone(allocator);
        errdefer new_env.deinit();
        var new_constraints = try self.constraints.clone(allocator);
        errdefer new_constraints.deinit();
        var new_store = try self.store.clone(allocator);
        errdefer new_store.deinit();
        var new_catch_arms = try self.catch_arms.clone(allocator);
        errdefer new_catch_arms.deinit(allocator);
        return .{
            .env = new_env,
            .constraints = new_constraints,
            .store = new_store,
            .error_state = self.error_state,
            .catch_arms = new_catch_arms,
            .cached_hash = self.cached_hash,
            .inline_depth = self.inline_depth,
            .call_stack = new_call_stack,
            .build_metadata = self.build_metadata,
        };
    }

    pub fn invalidateCache(self: *ProgramState) void {
        self.cached_hash = null;
    }

    pub fn getVar(self: *const ProgramState, var_id: VarId) ?AbstractValue {
        return self.env.get(var_id);
    }

    /// Assign `value` to `var_id`, dropping the constraints that named it.
    ///
    /// The two are one step. A fact about the variable came from a guard that
    /// read the value it is about to stop having, so keeping it says the path
    /// still requires that value: it prunes branches the assignment makes
    /// reachable, and once the new value contradicts it, it prunes the path.
    ///
    /// The write lands first, so a write that cannot be made leaves the facts
    /// with the value the variable still holds rather than with none at all.
    pub fn setVar(self: *ProgramState, var_id: VarId, value: AbstractValue) !void {
        try self.env.set(var_id, value);
        self.constraints.forgetVar(var_id);
        self.invalidateCache();
    }

    pub fn envSize(self: *const ProgramState) usize {
        return self.env.size();
    }

    /// Track a resource allocation for a region.
    pub fn trackAllocation(self: *ProgramState, region: VarId) !void {
        try self.store.markAllocated(region);
        self.invalidateCache();
    }

    /// Track a resource open for a region.
    pub fn trackOpen(self: *ProgramState, region: VarId) !void {
        try self.store.markOpened(region);
        self.invalidateCache();
    }

    /// Track a resource free for a region.
    pub fn trackFree(self: *ProgramState, region: VarId, call_token: ?u32) !void {
        try self.store.markFreed(region, call_token);
        self.invalidateCache();
    }

    /// Track freeing resources owned by a region (does not free the region itself).
    pub fn trackFreeOwned(self: *ProgramState, region: VarId, call_token: ?u32) !void {
        try self.store.markFreeOwned(region, call_token);
        self.invalidateCache();
    }

    /// Track a resource close for a region.
    pub fn trackClose(self: *ProgramState, region: VarId, call_token: ?u32) !void {
        try self.store.markClosed(region, call_token);
        self.invalidateCache();
    }

    /// Track a resource known to be non-allocated.
    pub fn trackNonAllocation(self: *ProgramState, region: VarId) !void {
        try self.store.markNonAllocated(region);
        self.invalidateCache();
    }

    pub fn resetRegion(self: *ProgramState, region: VarId) void {
        self.store.resetRegion(region);
        self.invalidateCache();
    }

    /// Replace a value binding without discarding its old held obligation.
    /// Transaction and temporary-payload resets continue to use `resetRegion`.
    pub fn replaceRegionForBinding(
        self: *ProgramState,
        region: VarId,
        replacement: store_mod.BindingReplacement,
    ) std.mem.Allocator.Error!store_mod.BindingReleases {
        const releases = try self.store.replaceRegionForBinding(region, replacement);
        self.invalidateCache();
        return releases;
    }

    /// The name that really holds the block a resize was handed, read before
    /// the store that writes the resize's result over its binding.
    ///
    /// `bytes = allocator.realloc(bytes, n)` writes the result over the very
    /// name the call was handed the block through, and that write is what
    /// promotes whichever alias outlived it over the name being replaced.
    /// Reading the answer afterwards names the binding that was replaced rather
    /// than the name still holding what was freed. Nothing is settled here: the
    /// query changes no region, no schedule and no obligation, so the cache
    /// stays as it is.
    pub fn reallocSourceAfterReplacement(
        self: *const ProgramState,
        region: VarId,
        source: VarId,
    ) VarId {
        return self.store.reallocSourceAfterReplacement(region, source);
    }

    pub fn sameResource(self: *const ProgramState, a: VarId, b: VarId) bool {
        return self.store.sameResource(a, b);
    }

    /// Queued cleanup reads the replacement binding at its eventual exit.
    pub fn restoreBindingReleases(
        self: *ProgramState,
        region: VarId,
        releases: store_mod.BindingReleases,
    ) std.mem.Allocator.Error!void {
        try self.store.restoreBindingReleases(region, releases);
        self.invalidateCache();
    }

    pub fn trackEscape(self: *ProgramState, region: VarId) void {
        self.store.escapeRegion(region);
        self.invalidateCache();
    }

    pub fn trackEscapeOwned(self: *ProgramState, region: VarId) std.mem.Allocator.Error!void {
        try self.store.escapeOwned(region);
        self.invalidateCache();
    }

    pub fn trackEscapeByName(self: *ProgramState, tree: *const std.zig.Ast, name: []const u8) !void {
        try self.store.escapeByName(tree, name);
        self.invalidateCache();
    }

    /// Track a resource use for a region.
    pub fn trackUse(self: *ProgramState, region: VarId, call_token: ?u32) !void {
        try self.store.markUsed(region, call_token);
        self.invalidateCache();
    }

    /// Track a deferred free for a region.
    pub fn trackDeferredFree(self: *ProgramState, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        try self.store.markDeferredFree(region, call_token, scope_node);
        self.invalidateCache();
    }

    /// Track a deferred free-owned for a region.
    pub fn trackDeferredFreeOwned(self: *ProgramState, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        try self.store.markDeferredFreeOwned(region, call_token, scope_node);
        self.invalidateCache();
    }

    /// Track a deferred close for a region.
    pub fn trackDeferredClose(self: *ProgramState, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        try self.store.markDeferredClose(region, call_token, scope_node);
        self.invalidateCache();
    }

    pub fn trackErrdeferredFree(self: *ProgramState, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        try self.store.markErrdeferredFree(region, call_token, scope_node);
        self.invalidateCache();
    }

    pub fn trackErrdeferredFreeOwned(self: *ProgramState, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        try self.store.markErrdeferredFreeOwned(region, call_token, scope_node);
        self.invalidateCache();
    }

    pub fn trackErrdeferredClose(self: *ProgramState, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        try self.store.markErrdeferredClose(region, call_token, scope_node);
        self.invalidateCache();
    }

    pub fn applyErrdeferredReleases(self: *ProgramState, return_node: u32, parent_map: []const u32) !void {
        try self.store.applyErrdeferredReleases(return_node, parent_map);
        self.invalidateCache();
    }

    pub fn trackOwnership(self: *ProgramState, resource: VarId, container: VarId) !void {
        try self.store.recordOwnership(resource, container);
        self.invalidateCache();
    }

    /// Hand a payload's owned resources to the aggregate storing it.
    pub fn adoptOwnedResources(self: *ProgramState, payload: VarId, container: VarId) void {
        self.store.adoptOwnedResources(payload, container);
        self.invalidateCache();
    }

    /// True when `container` owns at least one resource in this state.
    pub fn hasOwnedResources(self: *const ProgramState, container: VarId) bool {
        return self.store.hasOwnedResources(container);
    }

    /// Track a region aliasing another region.
    pub fn trackAlias(self: *ProgramState, alias: VarId, target: VarId) !void {
        try self.store.aliasRegion(alias, target);
        self.invalidateCache();
    }

    /// Track resource leaks in the current state.
    pub fn trackLeaks(self: *ProgramState) !void {
        try self.store.recordLeaks(self.isErrorPath());
        self.invalidateCache();
    }

    /// Get the resource state for a region, if known.
    pub fn getRegionState(self: *const ProgramState, region: VarId) ?ResourceState {
        return self.store.getState(region);
    }

    /// Get store violations recorded in this state.
    pub fn getStoreViolations(self: *const ProgramState) []const StoreViolation {
        return self.store.getViolations();
    }

    /// Add a constraint to this state and refine variable values accordingly.
    pub fn addConstraint(self: *ProgramState, constraint: Constraint) !void {
        try self.constraints.addConstraint(constraint);
        self.invalidateCache();

        // Refine the relevant variable's value based on the constraint
        const var_id: ?VarId = switch (constraint) {
            .int_compare => |ic| ic.var_id,
            .null_check => |nc| nc.var_id,
            .bool_check => |bc| bc.var_id,
            .var_compare => |vc| vc.var1_id,
            .literal_bool => null, // No variable to refine for literal bool constraints
        };

        if (var_id) |vid| {
            if (self.env.get(vid)) |current_val| {
                if (ConstraintManager.refineValue(current_val, constraint)) |refined| {
                    try self.env.set(vid, refined);
                }
            }
        }
    }

    /// Check if this state's constraints are satisfiable.
    pub fn isSatisfiable(self: *const ProgramState) bool {
        return self.constraints.isSatisfiable(&self.env);
    }

    pub fn constraintCount(self: *const ProgramState) usize {
        return self.constraints.size();
    }

    /// Check if there's a constraint proving a variable is non-null.
    pub fn hasNonNullConstraint(self: *const ProgramState, var_id: VarId) bool {
        for (self.constraints.constraints.items) |constraint| {
            switch (constraint) {
                .null_check => |nc| {
                    if (nc.var_id == var_id and !nc.is_null) {
                        return true;
                    }
                },
                else => {},
            }
        }
        return false;
    }

    /// Set the error state of this program state.
    pub fn setErrorState(self: *ProgramState, error_state: ErrorState) void {
        self.error_state = error_state;
        self.invalidateCache();
    }

    /// Get the current error state.
    pub fn getErrorState(self: *const ProgramState) ErrorState {
        return self.error_state;
    }

    /// Record the arm this path takes out of the `catch` expression at
    /// `catch_node`. Leaving such an expression is what decides the arm, so
    /// this is called on the edge out of it and never on the expression.
    ///
    /// Fails only when the path already carries more pending arms than the
    /// state holds itself and the spill cannot grow, which leaves the arms
    /// this path had exactly as they were.
    pub fn pushCatchArm(self: *ProgramState, catch_node: u32, arm: CatchArm) !void {
        try self.catch_arms.push(self.env.allocator, catch_node, arm);
        self.invalidateCache();
    }

    /// The arm this path took out of the `catch` expression at `catch_node`,
    /// or null when the path carries no decision for it.
    pub fn getCatchArm(self: *const ProgramState, catch_node: u32) ?CatchArm {
        return self.catch_arms.get(catch_node);
    }

    /// Drop the pending arms of the `catch` expressions named in `nodes`.
    pub fn forgetCatchArms(self: *ProgramState, nodes: []const u32) void {
        self.catch_arms.forget(self.env.allocator, nodes);
        self.invalidateCache();
    }

    /// Check if we are on an error path.
    pub fn isErrorPath(self: *const ProgramState) bool {
        return self.error_state == .error_active;
    }

    /// Check if we are on a normal (non-error) path.
    pub fn isNormalPath(self: *const ProgramState) bool {
        return self.error_state == .normal;
    }

    /// Get the current inlining depth.
    pub fn getInlineDepth(self: *const ProgramState) u32 {
        return self.inline_depth;
    }

    /// Increment inline depth when entering an inlined function.
    pub fn incrementInlineDepth(self: *ProgramState) void {
        self.inline_depth += 1;
        self.invalidateCache();
    }

    /// Decrement inline depth when returning from an inlined function.
    pub fn decrementInlineDepth(self: *ProgramState) void {
        if (self.inline_depth > 0) {
            self.inline_depth -= 1;
        }
        self.invalidateCache();
    }

    /// Push a call site onto the call stack.
    pub fn pushCallSite(self: *ProgramState, call_site: CallSite) !void {
        try self.call_stack.append(self.env.allocator, call_site);
        self.invalidateCache();
    }

    /// Pop a call site from the call stack.
    pub fn popCallSite(self: *ProgramState) ?CallSite {
        if (self.call_stack.items.len > 0) {
            self.invalidateCache();
            return self.call_stack.pop();
        }
        return null;
    }

    /// Get the top of the call stack without removing it.
    pub fn peekCallSite(self: *const ProgramState) ?CallSite {
        if (self.call_stack.items.len > 0) {
            return self.call_stack.items[self.call_stack.items.len - 1];
        }
        return null;
    }

    /// Check if we are at an inline call site (depth > 0).
    pub fn isInlined(self: *const ProgramState) bool {
        return self.inline_depth > 0;
    }

    /// Compute the widening context: calling stack, pending `catch` provenance,
    /// and executed ownership edges. Numeric values still widen within it.
    ///
    /// The provenance belongs in it because a widening point must not absorb a
    /// state whose pending arms name a different acquisition for the bindings
    /// below it. Keyed without it, the two would share one chain and the first
    /// merge between them would drop whichever arm they disagree on, leaving
    /// that binding unable to say which call produced its value.
    /// Ownership belongs here for the same reason: intersecting a stored
    /// payload's owner with a zero-pass path drops a transfer that did execute.
    pub fn contextHash(self: *const ProgramState) u64 {
        var hasher = std.hash.Wyhash.init(0);
        hasher.update(std.mem.asBytes(&self.inline_depth));
        for (self.call_stack.items) |cs| {
            const call_node = ids.cfgIndex(cs.call_node);
            const return_node = ids.cfgIndex(cs.return_node);
            hasher.update(std.mem.asBytes(&call_node));
            hasher.update(std.mem.asBytes(&return_node));
            hasher.update(std.mem.asBytes(&@intFromPtr(cs.caller_cfg)));
        }
        self.catch_arms.updateHash(&hasher);
        const ownership_hash = self.store.ownershipHash();
        hasher.update(std.mem.asBytes(&ownership_hash));
        return hasher.final();
    }

    /// Widening operator for program states.
    /// Used at widening points to ensure convergence by over-approximating.
    /// This should only be called on states with the same loop-header key
    /// (same ProgramPoint, calling context, catch arms, and ownership edges).
    ///
    /// Widening rules:
    /// - Environment: widened using `Environment.widen`.
    /// - Constraints: widened using `ConstraintManager.widen` (intersection).
    /// - Store: widened using `Store.widen`.
    ///   The graph requires matching ownership edges, so their intersection
    ///   preserves executed transfers without inventing unexecuted ones.
    /// - Error state: if equal, keep; if different, set to `.error_active` (conservative).
    /// - Pending catch arms: joined expression by expression. An arm both
    ///   paths agree on is kept, so a binding below still names the same
    ///   acquisition; one they disagree on is dropped, which leaves that
    ///   expression's own binding unable to name an acquisition rather than
    ///   naming the wrong call. `ExplodedGraph` only widens states whose
    ///   provenance matches, so this normally keeps every arm.
    /// - Inline depth and call stack: preserved from `self` (same context assumption).
    /// - Cached hash: cleared after widening.
    pub fn widen(self: *const ProgramState, other: *const ProgramState) !ProgramState {
        const allocator = self.env.allocator;

        var new_env = try self.env.widen(&other.env);
        errdefer new_env.deinit();

        var new_constraints = try self.constraints.widen(&other.constraints);
        errdefer new_constraints.deinit();

        var new_store = try self.store.widen(&other.store, allocator);
        errdefer new_store.deinit();

        // Error state join: if different, set to .error_active (conservative)
        const new_error_state = if (self.error_state == other.error_state)
            self.error_state
        else
            .error_active;

        // Clone call stack from self (same context assumption)
        var new_call_stack = try cloneCallSites(self.call_stack, allocator);
        errdefer new_call_stack.deinit(allocator);

        var new_catch_arms = try self.catch_arms.join(&other.catch_arms, allocator);
        errdefer new_catch_arms.deinit(allocator);

        return .{
            .env = new_env,
            .constraints = new_constraints,
            .store = new_store,
            .error_state = new_error_state,
            .catch_arms = new_catch_arms,
            .cached_hash = null, // Clear cached hash after widening
            .inline_depth = self.inline_depth, // Preserve from self (same context)
            .call_stack = new_call_stack,
            .build_metadata = self.build_metadata,
        };
    }

    /// Returns true if `self` is at least as general as `other`.
    /// Requires the same calling context to avoid cross-context subsumption.
    pub fn subsumes(self: *const ProgramState, other: *const ProgramState) bool {
        if (self.inline_depth != other.inline_depth) return false;
        if (self.call_stack.items.len != other.call_stack.items.len) return false;
        for (self.call_stack.items, other.call_stack.items) |self_cs, other_cs| {
            if (self_cs.call_node != other_cs.call_node) return false;
            if (self_cs.return_node != other_cs.return_node) return false;
            if (@intFromPtr(self_cs.caller_cfg) != @intFromPtr(other_cs.caller_cfg)) return false;
        }

        if (self.error_state != other.error_state) return false;
        if (!self.catch_arms.eql(&other.catch_arms)) return false;
        if (!self.env.subsumes(&other.env)) return false;
        if (!self.constraints.subsumes(&other.constraints)) return false;
        if (!self.store.subsumes(&other.store)) return false;

        return true;
    }
};

test "ProgramPoint basic operations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg1 = Cfg.init(allocator);
    defer cfg1.deinit();
    var cfg2 = Cfg.init(allocator);
    defer cfg2.deinit();

    const point1 = ProgramPoint.initPre(ids.cfgId(5), &cfg1);
    try testing.expectEqual(ids.cfgId(5), point1.node_index);
    try testing.expectEqual(ProgramPoint.Kind.pre, point1.kind);

    const point2 = ProgramPoint.initPost(ids.cfgId(5), &cfg1);
    try testing.expectEqual(ids.cfgId(5), point2.node_index);
    try testing.expectEqual(ProgramPoint.Kind.post, point2.kind);

    try testing.expect(!point1.eql(point2));

    const point3 = ProgramPoint.initPre(ids.cfgId(5), &cfg1);
    try testing.expect(point1.eql(point3));

    try testing.expect(point1.hash() != point2.hash());
    try testing.expectEqual(point1.hash(), point3.hash());

    // Test CFG identity: same node index but different CFG should not be equal
    const point4 = ProgramPoint.initPre(ids.cfgId(5), &cfg2);
    try testing.expect(!point1.eql(point4));
    try testing.expect(point1.hash() != point4.hash());
}

test "ProgramState basic operations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    try testing.expectEqual(@as(usize, 0), state1.envSize());

    try state1.setVar(ids.varId(42), .{ .concrete_int = 10 });
    try testing.expectEqual(@as(usize, 1), state1.envSize());

    const val = state1.getVar(ids.varId(42));
    try testing.expect(val != null);
    try testing.expect(val.?.eql(.{ .concrete_int = 10 }));

    var state2 = try state1.clone(allocator);
    defer state2.deinit();

    try testing.expect(state1.eql(&state2));

    try state2.setVar(ids.varId(42), .{ .concrete_int = 20 });
    try testing.expect(!state1.eql(&state2));
}

test "ProgramState with constraints" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    try state.setVar(ids.varId(1), .{ .concrete_int = 42 });

    try state.addConstraint(Constraint.intCompare(ids.varId(1), .eq, 42));
    try testing.expectEqual(@as(usize, 1), state.constraintCount());
    try testing.expect(state.isSatisfiable());

    try state.addConstraint(Constraint.intCompare(ids.varId(1), .eq, 43));
    try testing.expectEqual(@as(usize, 2), state.constraintCount());
    try testing.expect(!state.isSatisfiable());
}

test "ProgramState clone preserves infeasible constraints" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    try state.addConstraint(Constraint.intCompare(ids.varId(1), .eq, 42));
    try state.addConstraint(Constraint.intCompare(ids.varId(1), .ne, 42));

    var state2 = try state.clone(allocator);
    defer state2.deinit();

    try testing.expect(state.eql(&state2));
    try testing.expect(!state2.isSatisfiable());
    try testing.expect(!state.isSatisfiable());
}

test "ProgramState satisfiability" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    try state.setVar(ids.varId(1), .{ .concrete_int = 10 });

    try state.addConstraint(Constraint.intCompare(ids.varId(1), .lt, 20));
    try testing.expect(state.isSatisfiable());

    try state.addConstraint(Constraint.intCompare(ids.varId(1), .gt, 20));
    try testing.expect(!state.isSatisfiable());
}

test "ProgramState assignment drops the stale facts of the assigned variable" {
    const testing = std.testing;
    var state = ProgramState.init(testing.allocator);
    defer state.deinit();

    try state.setVar(ids.varId(1), .{ .concrete_int = 0 });
    try state.addConstraint(Constraint.intCompare(ids.varId(1), .eq, 0));
    try state.setVar(ids.varId(2), .unknown);
    try state.addConstraint(Constraint.nullCheck(ids.varId(2), false));
    try testing.expect(state.isSatisfiable());
    try testing.expectEqual(@as(usize, 2), state.constraintCount());

    try state.setVar(ids.varId(1), .{ .concrete_int = 1 });

    // The premise `i == 0` died with the value it read, so the branch it
    // blocked is reachable again.
    try testing.expect(state.getVar(ids.varId(1)).?.eql(.{ .concrete_int = 1 }));
    try state.addConstraint(Constraint.intCompare(ids.varId(1), .ne, 0));
    try testing.expect(state.isSatisfiable());
    try testing.expectEqual(@as(usize, 2), state.constraintCount());
    // The guard on the variable nobody assigned still holds.
    try testing.expect(state.hasNonNullConstraint(ids.varId(2)));
}

test "ProgramState assignment rehashes the state when the value does not change" {
    const testing = std.testing;
    var state = ProgramState.init(testing.allocator);
    defer state.deinit();

    try state.setVar(ids.varId(1), .{ .concrete_int = 5 });
    try state.addConstraint(Constraint.intCompare(ids.varId(1), .gt, 3));
    const with_fact = state.computeHash();

    try state.setVar(ids.varId(1), .{ .concrete_int = 5 });

    // The binding is the same, but the state it belongs to is not.
    try testing.expect(state.computeHash() != with_fact);
    try testing.expectEqual(@as(usize, 0), state.constraintCount());
}

test "ProgramState refinement keeps the constraint it was derived from" {
    const testing = std.testing;
    var state = ProgramState.init(testing.allocator);
    defer state.deinit();

    try state.setVar(ids.varId(1), .{ .concrete_int = 5 });
    try state.addConstraint(Constraint.intCompare(ids.varId(1), .ge, 0));
    try state.setVar(ids.varId(2), .unknown);
    try state.addConstraint(Constraint.boolCheck(ids.varId(2), true));
    try testing.expectEqual(@as(usize, 2), state.constraintCount());
    try testing.expect(state.isSatisfiable());
    try testing.expect(state.getVar(ids.varId(2)).?.eql(.{ .concrete_bool = true }));

    // Narrowing a value is not giving the variable a new one: only the
    // assignment retires the fact it was read from.
    try state.setVar(ids.varId(1), .{ .concrete_int = 5 });
    try testing.expectEqual(@as(usize, 1), state.constraintCount());
    try testing.expect(state.isSatisfiable());
}

test "ProgramState clone carries the facts an assignment left behind" {
    const testing = std.testing;
    var state = ProgramState.init(testing.allocator);
    defer state.deinit();

    try state.setVar(ids.varId(1), .{ .concrete_int = 0 });
    try state.setVar(ids.varId(2), .unknown);
    try state.addConstraint(Constraint.intCompare(ids.varId(1), .eq, 0));
    try state.setVar(ids.varId(1), .{ .concrete_int = 1 });
    try state.addConstraint(Constraint.intCompare(ids.varId(2), .ne, 5));

    var copy = try state.clone(testing.allocator);
    defer copy.deinit();

    try testing.expect(state.eql(&copy));
    try testing.expectEqual(state.computeHash(), copy.computeHash());
    try testing.expectEqual(@as(usize, 1), copy.constraintCount());
    // Each of them retires its own facts, so the compacted list of one is not
    // the list the other compacts.
    try copy.setVar(ids.varId(2), .{ .concrete_int = 7 });
    try testing.expectEqual(@as(usize, 0), copy.constraintCount());
    try testing.expectEqual(@as(usize, 1), state.constraintCount());
}

test "ProgramState assignment keeps the variable's facts when the write fails" {
    const testing = std.testing;
    var source = ProgramState.init(testing.allocator);
    defer source.deinit();
    // The variable the write names has a fact but no value: the environment
    // has never recorded it, so the write is the step that has to grow the
    // binding map. A write to a variable the environment already holds has
    // nothing to allocate - it overwrites the value in place - so it cannot
    // be made to fail, and a harness that induces a failure there would be
    // measuring a write that always lands.
    try source.addConstraint(Constraint.intCompare(ids.varId(1), .gt, 0));
    try source.addConstraint(Constraint.nullCheck(ids.varId(2), false));
    const facts = source.constraintCount();

    const Harness = struct {
        fn run(allocator: std.mem.Allocator, original: *const ProgramState, expected_facts: usize) !void {
            var state = try original.clone(allocator);
            defer state.deinit();
            const write_error: ?error{OutOfMemory} = write: {
                state.setVar(ids.varId(1), .{ .concrete_int = 1 }) catch |err| break :write err;
                break :write null;
            };
            // The value and the facts it retires move together: a write that
            // ran out of memory leaves both as they were.
            const assigned = if (state.getVar(ids.varId(1))) |value| value.eql(.{ .concrete_int = 1 }) else false;
            try std.testing.expectEqual(expected_facts - @intFromBool(assigned), state.constraintCount());
            try std.testing.expect(state.hasNonNullConstraint(ids.varId(2)));
            if (write_error) |err| return err;
        }
    };
    try testing.checkAllAllocationFailures(testing.allocator, Harness.run, .{ &source, facts });

    try testing.expectEqual(facts, source.constraintCount());
    try testing.expectEqual(@as(?AbstractValue, null), source.getVar(ids.varId(1)));
}

test "ErrorState enum values" {
    const testing = std.testing;

    try testing.expectEqual(@as(u8, 0), @intFromEnum(ErrorState.normal));
    try testing.expectEqual(@as(u8, 1), @intFromEnum(ErrorState.error_active));
    try testing.expectEqual(@as(u8, 2), @intFromEnum(ErrorState.error_handled));
}

test "ProgramState error state operations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    try testing.expect(state.isNormalPath());
    try testing.expect(!state.isErrorPath());

    state.setErrorState(.error_active);
    try testing.expect(state.isErrorPath());
    try testing.expect(!state.isNormalPath());

    state.setErrorState(.error_handled);
    try testing.expect(!state.isErrorPath());
}

test "ProgramState clone preserves error state" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    state.setErrorState(.error_active);

    var state2 = try state.clone(allocator);
    defer state2.deinit();

    try testing.expectEqual(state.getErrorState(), state2.getErrorState());
}

test "ProgramState equality includes error state" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    try testing.expect(state1.eql(&state2));

    state2.setErrorState(.error_active);
    try testing.expect(!state1.eql(&state2));
}

test "ProgramState hash includes error state" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    try testing.expectEqual(state1.computeHash(), state2.computeHash());

    state2.setErrorState(.error_active);
    try testing.expect(state1.computeHash() != state2.computeHash());
}

test "ProgramState inline depth operations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    try testing.expectEqual(@as(u32, 0), state.getInlineDepth());
    try testing.expect(!state.isInlined());

    state.incrementInlineDepth();
    try testing.expectEqual(@as(u32, 1), state.getInlineDepth());
    try testing.expect(state.isInlined());

    state.decrementInlineDepth();
    try testing.expectEqual(@as(u32, 0), state.getInlineDepth());
    try testing.expect(!state.isInlined());

    // Should not go below 0
    state.decrementInlineDepth();
    try testing.expectEqual(@as(u32, 0), state.getInlineDepth());
}

test "ProgramState call stack operations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    var state = ProgramState.init(allocator);
    defer state.deinit();

    const call_site = CallSite{ .call_node = ids.cfgId(1), .caller_cfg = &cfg, .return_node = ids.cfgId(2) };

    try testing.expectEqual(@as(?CallSite, null), state.peekCallSite());

    try state.pushCallSite(call_site);
    try testing.expect(state.peekCallSite() != null);
    try testing.expectEqual(ids.cfgId(1), state.peekCallSite().?.call_node);

    const popped = state.popCallSite();
    try testing.expect(popped != null);
    try testing.expectEqual(@as(?CallSite, null), state.peekCallSite());
}

test "ProgramState clone keeps an independent calling context" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    var callee_cfg = Cfg.init(allocator);
    defer callee_cfg.deinit();
    const first = CallSite{ .call_node = ids.cfgId(1), .caller_cfg = &cfg, .return_node = ids.cfgId(2) };
    const second = CallSite{ .call_node = ids.cfgId(3), .caller_cfg = &callee_cfg, .return_node = ids.cfgId(4) };
    const third = CallSite{ .call_node = ids.cfgId(5), .caller_cfg = &cfg, .return_node = ids.cfgId(6) };

    var state = ProgramState.init(allocator);
    defer state.deinit();
    state.incrementInlineDepth();
    try state.pushCallSite(first);
    state.incrementInlineDepth();
    try state.pushCallSite(second);
    const original_hash = state.computeHash();
    const original_context = state.contextHash();

    var copy = try state.clone(allocator);
    defer copy.deinit();
    try testing.expect(state.eql(&copy));
    try testing.expectEqual(original_hash, copy.computeHash());
    try testing.expectEqual(original_context, copy.contextHash());
    try testing.expectEqual(state.getInlineDepth(), copy.getInlineDepth());

    try testing.expectEqual(second, copy.popCallSite().?);
    copy.decrementInlineDepth();
    try copy.pushCallSite(third);
    try testing.expectEqual(second, state.peekCallSite().?);
    try testing.expectEqual(original_hash, state.computeHash());
    try testing.expectEqual(original_context, state.contextHash());
    try testing.expect(copy.computeHash() != original_hash);

    try testing.expectEqual(second, state.popCallSite().?);
    try state.pushCallSite(first);
    try testing.expectEqual(third, copy.popCallSite().?);
    try testing.expectEqual(first, copy.popCallSite().?);
    try testing.expect(copy.popCallSite() == null);
    try testing.expectEqual(first, state.peekCallSite().?);
}

test "ProgramState clone outlives its source allocator" {
    const testing = std.testing;
    var cfg = Cfg.init(testing.allocator);
    defer cfg.deinit();
    const call_site = CallSite{ .call_node = ids.cfgId(1), .caller_cfg = &cfg, .return_node = ids.cfgId(2) };
    const metadata = BuildMetadata.init(.{ .arch = .aarch64, .os = .linux, .abi = null }, .release_fast);

    var copy = blk: {
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        var source = ProgramState.init(arena.allocator());
        defer source.deinit();
        try source.setVar(ids.varId(1), .{ .concrete_int = 5 });
        try source.addConstraint(Constraint.intCompare(ids.varId(1), .gt, 0));
        try source.addConstraint(Constraint.nullCheck(ids.varId(2), false));
        try source.addConstraint(Constraint.boolCheck(ids.varId(3), true));
        try source.trackAllocation(ids.varId(4));
        source.setErrorState(.error_active);
        source.incrementInlineDepth();
        try source.pushCallSite(call_site);
        source.build_metadata = &metadata;
        const source_hash = source.computeHash();

        var result = try source.clone(testing.allocator);
        errdefer result.deinit();
        try testing.expect(source.eql(&result));
        try testing.expectEqual(source_hash, result.computeHash());
        break :blk result;
    };
    defer copy.deinit();

    try testing.expect(copy.getVar(ids.varId(1)).?.eql(.{ .concrete_int = 5 }));
    try testing.expect(copy.isSatisfiable());
    try testing.expect(copy.hasNonNullConstraint(ids.varId(2)));
    try testing.expect(copy.isErrorPath());
    try testing.expectEqual(@as(u32, 1), copy.getInlineDepth());
    try testing.expectEqual(metadata.target.os, copy.build_metadata.?.target.os);
    try testing.expectEqual(metadata.optimize_mode, copy.build_metadata.?.optimize_mode);
    try testing.expectEqual(ResourceState.allocated, copy.getRegionState(ids.varId(4)).?);
    const original_hash = copy.computeHash();
    try copy.setVar(ids.varId(1), .{ .concrete_int = 7 });
    try testing.expect(copy.computeHash() != original_hash);
    try copy.trackFree(ids.varId(4), 12);
    try testing.expectEqual(ResourceState.freed, copy.getRegionState(ids.varId(4)).?);
    try copy.addConstraint(Constraint.boolCheck(ids.varId(3), false));
    try testing.expect(!copy.isSatisfiable());
    try testing.expectEqual(call_site, copy.popCallSite().?);
    try copy.pushCallSite(call_site);
    try testing.expectEqual(call_site, copy.peekCallSite().?);
}

test "ProgramState cloning cleans up all domains on allocation failure" {
    const testing = std.testing;
    var cfg = Cfg.init(testing.allocator);
    defer cfg.deinit();
    const call_site = CallSite{ .call_node = ids.cfgId(1), .caller_cfg = &cfg, .return_node = ids.cfgId(2) };
    var source = ProgramState.init(testing.allocator);
    defer source.deinit();
    try source.setVar(ids.varId(1), .{ .concrete_int = 5 });
    try source.addConstraint(Constraint.intCompare(ids.varId(1), .gt, 0));
    try source.addConstraint(Constraint.intCompare(ids.varId(1), .lt, 10));
    try source.addConstraint(Constraint.nullCheck(ids.varId(2), false));
    try source.addConstraint(Constraint.boolCheck(ids.varId(3), true));
    try source.trackAllocation(ids.varId(4));
    try source.trackFree(ids.varId(4), 10);
    try source.trackFree(ids.varId(4), 11);
    source.incrementInlineDepth();
    try source.pushCallSite(call_site);
    const source_hash = source.computeHash();

    const Harness = struct {
        fn run(allocator: std.mem.Allocator, original: *const ProgramState, expected_hash: u64) !void {
            var copy = try original.clone(allocator);
            defer copy.deinit();
            try std.testing.expect(original.eql(&copy));
            try std.testing.expectEqual(expected_hash, copy.computeHash());
            try std.testing.expectEqual(original.peekCallSite(), copy.peekCallSite());
            try std.testing.expect(copy.isSatisfiable());
        }
    };
    try testing.checkAllAllocationFailures(testing.allocator, Harness.run, .{ &source, source_hash });
    source.invalidateCache();
    try testing.expectEqual(source_hash, source.computeHash());
    try testing.expect(source.getVar(ids.varId(1)).?.eql(.{ .concrete_int = 5 }));
    try testing.expectEqual(call_site, source.peekCallSite().?);
    try testing.expectEqual(ResourceState.freed, source.getRegionState(ids.varId(4)).?);
}

test "ProgramState equality includes inline depth" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    try testing.expect(state1.eql(&state2));

    state2.incrementInlineDepth();
    try testing.expect(!state1.eql(&state2));
}

test "ProgramState hash includes inline depth" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    try testing.expectEqual(state1.computeHash(), state2.computeHash());

    state2.incrementInlineDepth();
    try testing.expect(state1.computeHash() != state2.computeHash());
}

test "ProgramState store tracks allocation/free" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    const region = ids.varId(42);

    try state.trackAllocation(region);
    try testing.expectEqual(ResourceState.allocated, state.getRegionState(region).?);

    try state.trackFree(region, 1);
    try testing.expectEqual(ResourceState.freed, state.getRegionState(region).?);
    try testing.expectEqual(@as(usize, 0), state.getStoreViolations().len);
}

test "ProgramState equality includes store" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    try testing.expect(state1.eql(&state2));

    try state2.trackAllocation(ids.varId(5));
    try testing.expect(!state1.eql(&state2));
}

test "ProgramState hash includes store" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    try testing.expectEqual(state1.computeHash(), state2.computeHash());

    try state2.trackAllocation(ids.varId(9));
    try testing.expect(state1.computeHash() != state2.computeHash());
}

test "ProgramState contextHash reflects inline depth" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    try testing.expectEqual(state1.contextHash(), state2.contextHash());

    state2.incrementInlineDepth();
    try testing.expect(state1.contextHash() != state2.contextHash());
}

test "ProgramState contextHash reflects call stack" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    try testing.expectEqual(state1.contextHash(), state2.contextHash());

    try state2.pushCallSite(CallSite{ .call_node = ids.cfgId(1), .caller_cfg = &cfg, .return_node = ids.cfgId(2) });
    try testing.expect(state1.contextHash() != state2.contextHash());
}

test "ProgramState contextHash is stable" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    var state = ProgramState.init(allocator);
    defer state.deinit();

    state.incrementInlineDepth();
    try state.pushCallSite(CallSite{ .call_node = ids.cfgId(5), .caller_cfg = &cfg, .return_node = ids.cfgId(10) });

    const hash1 = state.contextHash();
    const hash2 = state.contextHash();
    try testing.expectEqual(hash1, hash2);
}

test "WideningKey basic operations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    var state = ProgramState.init(allocator);
    defer state.deinit();

    const point1 = ProgramPoint.initPre(ids.cfgId(5), &cfg);
    const point2 = ProgramPoint.initPre(ids.cfgId(6), &cfg);

    const key1 = WideningKey.init(point1, &state);
    const key2 = WideningKey.init(point1, &state);
    const key3 = WideningKey.init(point2, &state);

    try testing.expect(key1.eql(key2));
    try testing.expect(!key1.eql(key3));
    try testing.expectEqual(key1.hash(), key2.hash());
    try testing.expect(key1.hash() != key3.hash());
}

test "WideningKey distinguishes calling contexts" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    state2.incrementInlineDepth();
    try state2.pushCallSite(CallSite{ .call_node = ids.cfgId(1), .caller_cfg = &cfg, .return_node = ids.cfgId(2) });

    const point = ProgramPoint.initPre(ids.cfgId(5), &cfg);

    const key1 = WideningKey.init(point, &state1);
    const key2 = WideningKey.init(point, &state2);

    try testing.expect(!key1.eql(key2));
    try testing.expect(key1.hash() != key2.hash());
}

test "Widening context preserves canonical ownership independent of insertion order" {
    const testing = std.testing;
    const bytes = ids.varId(201);
    const bytes_alias = ids.varId(202);
    const inner = ids.varId(203);
    const out = ids.varId(204);
    const out_alias = ids.varId(205);

    var forward = ProgramState.init(testing.allocator);
    defer forward.deinit();
    try forward.trackAllocation(bytes);
    try forward.trackAlias(bytes_alias, bytes);
    try forward.trackAlias(out_alias, out);
    try forward.store.recordOwnership(bytes_alias, inner);
    try forward.store.recordOwnership(inner, out_alias);

    var reverse = ProgramState.init(testing.allocator);
    defer reverse.deinit();
    try reverse.trackAllocation(bytes);
    try reverse.trackAlias(bytes_alias, bytes);
    try reverse.trackAlias(out_alias, out);
    try reverse.store.recordOwnership(inner, out);
    try reverse.store.recordOwnership(bytes, inner);

    try testing.expectEqual(forward.contextHash(), reverse.contextHash());
    try testing.expect(forward.subsumes(&reverse));
    try testing.expect(reverse.subsumes(&forward));
    var widened = try forward.widen(&reverse);
    defer widened.deinit();
    try widened.trackEscapeOwned(out_alias);
    try widened.store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), widened.getStoreViolations().len);

    var absent = ProgramState.init(testing.allocator);
    defer absent.deinit();
    try absent.trackAllocation(bytes);
    try absent.trackAlias(bytes_alias, bytes);
    try absent.trackAlias(out_alias, out);
    try testing.expect(forward.contextHash() != absent.contextHash());
    try testing.expect(!absent.subsumes(&forward));
    try absent.trackEscapeOwned(out_alias);
    try absent.store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), absent.getStoreViolations().len);
    try testing.expectEqual(bytes, absent.getStoreViolations()[0].region);
}

test "WideningKey HashContext works with HashMap" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    var state = ProgramState.init(allocator);
    defer state.deinit();

    const point1 = ProgramPoint.initPre(ids.cfgId(5), &cfg);
    const point2 = ProgramPoint.initPre(ids.cfgId(6), &cfg);

    const key1 = WideningKey.init(point1, &state);
    const key2 = WideningKey.init(point2, &state);

    var map = std.HashMap(WideningKey, u32, WideningKey.HashContext, std.hash_map.default_max_load_percentage).init(allocator);
    defer map.deinit();

    try map.put(key1, 100);
    try map.put(key2, 200);

    try testing.expectEqual(@as(?u32, 100), map.get(key1));
    try testing.expectEqual(@as(?u32, 200), map.get(key2));
}

test "ProgramState widen composes domain widenings" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    // Set up environments with overlapping and disjoint variables
    try state1.setVar(ids.varId(1), .{ .concrete_int = 10 });
    try state1.setVar(ids.varId(2), .{ .concrete_int = 20 });

    try state2.setVar(ids.varId(1), .{ .concrete_int = 10 }); // same
    try state2.setVar(ids.varId(2), .{ .concrete_int = 30 }); // different

    // Add constraints
    try state1.addConstraint(Constraint.intCompare(ids.varId(1), .eq, 10));
    try state2.addConstraint(Constraint.intCompare(ids.varId(1), .eq, 10)); // shared

    // Track resources
    try state1.trackAllocation(ids.varId(100));
    try state2.trackAllocation(ids.varId(100)); // same

    var widened = try state1.widen(&state2);
    defer widened.deinit();

    // var1 should be preserved (same value)
    const val1 = widened.getVar(ids.varId(1));
    try testing.expect(val1 != null);
    try testing.expect(val1.?.eql(.{ .concrete_int = 10 }));

    // var2 widened the same way: the integer interval keeps the lower bound
    // that did not move and throws the one that did to the `i64` domain end.
    const val2 = widened.getVar(ids.varId(2));
    try testing.expect(val2 != null);
    try testing.expect(val2.?.eql(.{ .int_range = .{
        .min = 20,
        .max = std.math.maxInt(i64),
    } }));

    // Shared constraint should remain
    try testing.expectEqual(@as(usize, 1), widened.constraintCount());

    // Resource state should remain (both agree)
    try testing.expectEqual(ResourceState.allocated, widened.getRegionState(ids.varId(100)).?);
}

test "ProgramState widen clears cached hash" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    // Compute hash before widening
    _ = state1.computeHash();
    try testing.expect(state1.cached_hash != null);

    var widened = try state1.widen(&state2);
    defer widened.deinit();

    // Widened state should have null cached_hash
    try testing.expectEqual(@as(?u64, null), widened.cached_hash);
}

test "ProgramState widen error_state join same" {
    const testing = std.testing;
    const allocator = testing.allocator;

    // Both states have same error_state
    var state1 = ProgramState.init(allocator);
    defer state1.deinit();
    state1.setErrorState(.normal);

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();
    state2.setErrorState(.normal);

    var widened = try state1.widen(&state2);
    defer widened.deinit();

    try testing.expectEqual(ErrorState.normal, widened.getErrorState());

    // Now test with error_active
    var state3 = ProgramState.init(allocator);
    defer state3.deinit();
    state3.setErrorState(.error_active);

    var state4 = ProgramState.init(allocator);
    defer state4.deinit();
    state4.setErrorState(.error_active);

    var widened2 = try state3.widen(&state4);
    defer widened2.deinit();

    try testing.expectEqual(ErrorState.error_active, widened2.getErrorState());
}

test "ProgramState widen error_state join different becomes error_active" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();
    state1.setErrorState(.normal);

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();
    state2.setErrorState(.error_active);

    var widened = try state1.widen(&state2);
    defer widened.deinit();

    // Different error states should become error_active (conservative)
    try testing.expectEqual(ErrorState.error_active, widened.getErrorState());

    // Test the reverse
    var widened2 = try state2.widen(&state1);
    defer widened2.deinit();

    try testing.expectEqual(ErrorState.error_active, widened2.getErrorState());
}

test "ProgramState widen preserves inline depth and call stack" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();
    state1.incrementInlineDepth();
    try state1.pushCallSite(CallSite{ .call_node = ids.cfgId(1), .caller_cfg = &cfg, .return_node = ids.cfgId(2) });

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();
    state2.incrementInlineDepth();
    try state2.pushCallSite(CallSite{ .call_node = ids.cfgId(1), .caller_cfg = &cfg, .return_node = ids.cfgId(2) });

    var widened = try state1.widen(&state2);
    defer widened.deinit();

    // Inline depth and call stack should be preserved from self
    try testing.expectEqual(@as(u32, 1), widened.getInlineDepth());
    try testing.expectEqual(@as(usize, 1), widened.call_stack.items.len);
    try testing.expectEqual(ids.cfgId(1), widened.call_stack.items[0].call_node);
}

test "ProgramState widen with empty states" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    var widened = try state1.widen(&state2);
    defer widened.deinit();

    try testing.expectEqual(@as(usize, 0), widened.envSize());
    try testing.expectEqual(@as(usize, 0), widened.constraintCount());
    try testing.expectEqual(ErrorState.normal, widened.getErrorState());
    try testing.expectEqual(@as(u32, 0), widened.getInlineDepth());
}

test "ProgramState subsumes respects precision ordering" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var general = ProgramState.init(allocator);
    defer general.deinit();

    var specific = ProgramState.init(allocator);
    defer specific.deinit();

    try specific.setVar(ids.varId(1), .{ .concrete_int = 1 });
    try specific.addConstraint(.{ .null_check = .{ .var_id = ids.varId(2), .is_null = false } });

    try testing.expect(general.subsumes(&specific));
    try testing.expect(!specific.subsumes(&general));
}

test "ProgramState widen store violations union" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state1 = ProgramState.init(allocator);
    defer state1.deinit();

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();

    // Create a violation in state1 (double free)
    try state1.trackAllocation(ids.varId(100));
    try state1.trackFree(ids.varId(100), 1);
    try state1.trackFree(ids.varId(100), 2);

    // Create a different violation in state2 (use after free)
    try state2.trackAllocation(ids.varId(200));
    try state2.trackFree(ids.varId(200), 3);
    try state2.trackUse(ids.varId(200), 4);

    try testing.expectEqual(@as(usize, 1), state1.getStoreViolations().len);
    try testing.expectEqual(@as(usize, 1), state2.getStoreViolations().len);

    var widened = try state1.widen(&state2);
    defer widened.deinit();

    // Both violations should be present (union)
    try testing.expectEqual(@as(usize, 2), widened.getStoreViolations().len);
}

test "PendingCatchArms keeps every decision past the inline facts" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    // A handler chain deeper than the state holds inline: dropping its
    // outermost decisions instead of spilling them hands the binding below it
    // the wrong call, so every one of them has to survive.
    const total: u32 = inline_pending_catch_arms + 3;
    var node: u32 = 1;
    while (node <= total) : (node += 1) {
        try state.pushCatchArm(node, if (node % 2 == 0) .success else .failure);
    }
    try testing.expectEqual(@as(usize, total), state.catch_arms.len());

    node = 1;
    while (node <= total) : (node += 1) {
        try testing.expectEqual(if (node % 2 == 0) CatchArm.success else CatchArm.failure, state.getCatchArm(node).?);
    }

    var copy = try state.clone(allocator);
    defer copy.deinit();
    try testing.expect(state.eql(&copy));
    try testing.expectEqual(state.computeHash(), copy.computeHash());
    try testing.expectEqual(state.contextHash(), copy.contextHash());

    // Re-entering one expression re-decides its own arm instead of adding a
    // second decision for it.
    try copy.pushCatchArm(1, .success);
    try testing.expectEqual(@as(usize, total), copy.catch_arms.len());
    try testing.expectEqual(CatchArm.success, copy.getCatchArm(1).?);
    try testing.expect(!copy.catch_arms.eql(&state.catch_arms));
}

test "PendingCatchArms returns its spill once the binding settles it" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    const total: u32 = inline_pending_catch_arms + 2;
    var node: u32 = 1;
    while (node <= total) : (node += 1) {
        try state.pushCatchArm(node, .success);
    }
    try testing.expect(state.catch_arms.spilled != null);

    var first: [1]u32 = .{1};
    state.forgetCatchArms(&first);
    try testing.expect(state.catch_arms.spilled != null);
    try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(1));

    const rest = [_]u32{ 2, 3, 4, 5, 6 };
    state.forgetCatchArms(&rest);
    try testing.expect(state.catch_arms.spilled == null);
    try testing.expectEqual(@as(usize, 0), state.catch_arms.len());
}

/// One `catch` decision a test expects a path to carry, in the order the path
/// carries it. Test support for `PendingCatchArms`, so a check reads as the
/// chain a test built instead of as index arithmetic.
const ExpectedCatchArm = struct {
    node: u32,
    arm: CatchArm,
};

/// Check that the path carries exactly `expected`, oldest first, and that each
/// decision is also readable by the node that names it.
///
/// Where the arms sit is not part of what a path is, so the path also has to
/// compare and hash as one built from the same decisions one at a time, which
/// never spilled at all.
fn expectPendingArms(state: *ProgramState, expected: []const ExpectedCatchArm) !void {
    const testing = std.testing;
    try testing.expectEqual(expected.len, state.catch_arms.len());
    var index: usize = 0;
    while (index < expected.len) : (index += 1) {
        const fact = state.catch_arms.factAt(index) orelse return error.TestUnexpectedResult;
        try testing.expectEqual(expected[index].node, fact.catch_node);
        try testing.expectEqual(expected[index].arm, fact.arm);
        try testing.expectEqual(expected[index].arm, state.getCatchArm(expected[index].node).?);
    }

    var equivalent = ProgramState.init(state.env.allocator);
    defer equivalent.deinit();
    for (expected) |decision| {
        try equivalent.pushCatchArm(decision.node, decision.arm);
    }
    try testing.expect(state.catch_arms.eql(&equivalent.catch_arms));
    try testing.expect(equivalent.catch_arms.eql(&state.catch_arms));
    try testing.expect(state.eql(&equivalent));
    try testing.expectEqual(equivalent.computeHash(), state.computeHash());
    try testing.expectEqual(equivalent.contextHash(), state.contextHash());
}

test "PendingCatchArms settles inline arms and keeps the rest of the chain" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    // A handler chain deeper than the state holds inline: its outermost
    // decisions spill, and a binding under the whole chain reads them.
    const chain = [_]ExpectedCatchArm{
        .{ .node = 1, .arm = .failure },
        .{ .node = 2, .arm = .success },
        .{ .node = 3, .arm = .failure },
        .{ .node = 4, .arm = .success },
        .{ .node = 5, .arm = .failure },
        .{ .node = 6, .arm = .success },
        .{ .node = 7, .arm = .failure },
        .{ .node = 8, .arm = .success },
    };
    for (chain) |decision| {
        try state.pushCatchArm(decision.node, decision.arm);
    }
    try testing.expect(state.catch_arms.spilled != null);
    try expectPendingArms(&state, &chain);

    // Settling the first three arms leaves five, one more than the inline ones
    // hold, so the chain still spills. The slots those three left free take the
    // oldest survivor, and only what is past the inline ones stays spilled.
    const settled = [_]u32{ 1, 2, 3 };
    state.forgetCatchArms(&settled);
    try testing.expect(state.catch_arms.spilled != null);
    const after_settlement = [_]ExpectedCatchArm{
        .{ .node = 4, .arm = .success },
        .{ .node = 5, .arm = .failure },
        .{ .node = 6, .arm = .success },
        .{ .node = 7, .arm = .failure },
        .{ .node = 8, .arm = .success },
    };
    try expectPendingArms(&state, &after_settlement);
    for (settled) |gone| {
        try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(gone));
    }

    // A decision past the inline ones spills, after every arm the path still
    // carries.
    try state.pushCatchArm(9, .success);
    const after_push = [_]ExpectedCatchArm{
        .{ .node = 4, .arm = .success },
        .{ .node = 5, .arm = .failure },
        .{ .node = 6, .arm = .success },
        .{ .node = 7, .arm = .failure },
        .{ .node = 8, .arm = .success },
        .{ .node = 9, .arm = .success },
    };
    try expectPendingArms(&state, &after_push);

    // Settling an arm out of the middle of the spill leaves the rest of it
    // dense: the arms after it are the ones a binding below still reads.
    const from_spill = [_]u32{8};
    state.forgetCatchArms(&from_spill);
    try testing.expectEqual(@as(usize, 1), state.catch_arms.spilled.?.items.len);
    const after_spill_settlement = [_]ExpectedCatchArm{
        .{ .node = 4, .arm = .success },
        .{ .node = 5, .arm = .failure },
        .{ .node = 6, .arm = .success },
        .{ .node = 7, .arm = .failure },
        .{ .node = 9, .arm = .success },
    };
    try expectPendingArms(&state, &after_spill_settlement);
    try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(8));

    // Re-entering an expression re-decides its own arm, in the inline facts and
    // in the spill alike, and adds no second decision for it.
    try state.pushCatchArm(6, .failure);
    try state.pushCatchArm(9, .failure);
    const after_redecision = [_]ExpectedCatchArm{
        .{ .node = 4, .arm = .success },
        .{ .node = 5, .arm = .failure },
        .{ .node = 6, .arm = .failure },
        .{ .node = 7, .arm = .failure },
        .{ .node = 9, .arm = .failure },
    };
    try expectPendingArms(&state, &after_redecision);

    // Settling the inline arms moves the last survivor back into the slots
    // they freed and gives the spill back, so the path carries that one arm
    // and nothing of the chain it came from.
    const inline_arms = [_]u32{ 4, 5, 6, 7 };
    state.forgetCatchArms(&inline_arms);
    try testing.expect(state.catch_arms.spilled == null);
    const last_survivor = [_]ExpectedCatchArm{.{ .node = 9, .arm = .failure }};
    try expectPendingArms(&state, &last_survivor);
    for (inline_arms) |gone| {
        try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(gone));
    }

    // The next decision belongs after the survivor, not in one of the slots the
    // settlement emptied.
    try state.pushCatchArm(10, .success);
    const after_pushed_inline = [_]ExpectedCatchArm{
        .{ .node = 9, .arm = .failure },
        .{ .node = 10, .arm = .success },
    };
    try expectPendingArms(&state, &after_pushed_inline);
    for (inline_arms) |gone| {
        try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(gone));
    }

    // Settling the rest empties the path, and the next decision starts a fresh
    // chain of its own.
    const last_arms = [_]u32{ 9, 10 };
    state.forgetCatchArms(&last_arms);
    try testing.expect(state.catch_arms.spilled == null);
    try testing.expectEqual(@as(usize, 0), state.catch_arms.len());
    try state.pushCatchArm(11, .failure);
    const fresh_chain = [_]ExpectedCatchArm{.{ .node = 11, .arm = .failure }};
    try expectPendingArms(&state, &fresh_chain);
    for (last_arms) |gone| {
        try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(gone));
    }
}

test "PendingCatchArms pushes into the slots a settlement freed" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var state = ProgramState.init(allocator);
    defer state.deinit();

    const total: u32 = inline_pending_catch_arms + 2;
    var node: u32 = 1;
    while (node <= total) : (node += 1) {
        try state.pushCatchArm(node, if (node % 2 == 0) .success else .failure);
    }
    try testing.expect(state.catch_arms.spilled != null);

    // Settling every inline arm of a chain that spilled leaves the survivors
    // in the slots those arms freed and gives the spill back.
    const settled = [_]u32{ 1, 2, 3, 4 };
    state.forgetCatchArms(&settled);
    try testing.expect(state.catch_arms.spilled == null);
    const survivors = [_]ExpectedCatchArm{
        .{ .node = 5, .arm = .failure },
        .{ .node = 6, .arm = .success },
    };
    try expectPendingArms(&state, &survivors);
    for (settled) |gone| {
        try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(gone));
    }

    // The next decision is the third arm of the path, after both survivors:
    // landing it in a slot the settlement emptied would publish a settled arm
    // in its place and lose the two the chain still carries.
    try state.pushCatchArm(7, .failure);
    const with_pushed = [_]ExpectedCatchArm{
        .{ .node = 5, .arm = .failure },
        .{ .node = 6, .arm = .success },
        .{ .node = 7, .arm = .failure },
    };
    try expectPendingArms(&state, &with_pushed);
    for (settled) |gone| {
        try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(gone));
    }

    // Re-deciding a survivor changes the arm it carries, not the order or the
    // number of arms the path has.
    try state.pushCatchArm(5, .success);
    const after_redecision = [_]ExpectedCatchArm{
        .{ .node = 5, .arm = .success },
        .{ .node = 6, .arm = .success },
        .{ .node = 7, .arm = .failure },
    };
    try expectPendingArms(&state, &after_redecision);

    // Settling one of them takes the next decision with it, into the slot it
    // left free.
    const one = [_]u32{6};
    state.forgetCatchArms(&one);
    const after_one = [_]ExpectedCatchArm{
        .{ .node = 5, .arm = .success },
        .{ .node = 7, .arm = .failure },
    };
    try expectPendingArms(&state, &after_one);
    try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(6));

    try state.pushCatchArm(8, .success);
    const with_second_push = [_]ExpectedCatchArm{
        .{ .node = 5, .arm = .success },
        .{ .node = 7, .arm = .failure },
        .{ .node = 8, .arm = .success },
    };
    try expectPendingArms(&state, &with_second_push);

    // Settling the rest empties the path, and the next decision is the only arm
    // it carries.
    const all = [_]u32{ 5, 7, 8 };
    state.forgetCatchArms(&all);
    try testing.expect(state.catch_arms.spilled == null);
    try testing.expectEqual(@as(usize, 0), state.catch_arms.len());
    try state.pushCatchArm(9, .failure);
    const last_arm = [_]ExpectedCatchArm{.{ .node = 9, .arm = .failure }};
    try expectPendingArms(&state, &last_arm);
    for (all) |gone| {
        try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(gone));
    }
}

test "PendingCatchArms spill failure leaves the path's arms intact" {
    const testing = std.testing;
    var failing = std.testing.FailingAllocator.init(testing.allocator, .{});

    var state = ProgramState.init(failing.allocator());
    const inline_capacity: u32 = inline_pending_catch_arms;
    var node: u32 = 1;
    while (node <= inline_capacity) : (node += 1) {
        try state.pushCatchArm(node, .success);
    }

    // The next decision is the first one that needs room of its own.
    failing.fail_index = failing.alloc_index;
    try testing.expectError(error.OutOfMemory, state.pushCatchArm(inline_capacity + 1, .failure));

    try testing.expectEqual(@as(usize, inline_capacity), state.catch_arms.len());
    try testing.expectEqual(@as(?CatchArm, null), state.getCatchArm(inline_capacity + 1));
    try testing.expectEqual(CatchArm.success, state.getCatchArm(1).?);

    state.deinit();
    try testing.expectEqual(failing.allocated_bytes, failing.freed_bytes);
}

test "ProgramState widen keeps the arms both paths agree on" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var first = ProgramState.init(allocator);
    defer first.deinit();
    var second = ProgramState.init(allocator);
    defer second.deinit();

    try first.pushCatchArm(1, .success);
    try first.pushCatchArm(2, .success);
    try second.pushCatchArm(1, .success);
    try second.pushCatchArm(2, .failure);
    try second.pushCatchArm(3, .success);

    var widened = try first.widen(&second);
    defer widened.deinit();

    // The expression both paths ran the same way keeps naming its call; one
    // they disagree about, and one only one path entered, are gone.
    try testing.expectEqual(CatchArm.success, widened.getCatchArm(1).?);
    try testing.expectEqual(@as(?CatchArm, null), widened.getCatchArm(2));
    try testing.expectEqual(@as(?CatchArm, null), widened.getCatchArm(3));
}

test "ProgramState binding replacement keeps the orphan acquisition diagnostic" {
    const testing = std.testing;
    const handle = ids.varId(301);
    var state = ProgramState.init(testing.allocator);
    defer state.deinit();
    try state.trackOpen(handle);
    try state.setVar(handle, .non_null);
    const before = state.computeHash();

    const releases = try state.replaceRegionForBinding(handle, .different);
    try testing.expect(state.cached_hash == null);
    try state.setVar(handle, .null_val);
    try state.restoreBindingReleases(handle, releases);
    try testing.expect(state.getRegionState(handle) == null);
    try testing.expectEqual(@as(usize, 1), state.getStoreViolations().len);
    try testing.expectEqual(store_mod.StoreViolationKind.resource_leak, state.getStoreViolations()[0].kind);
    try testing.expectEqual(handle, state.getStoreViolations()[0].region);
    try testing.expect(state.computeHash() != before);
}
