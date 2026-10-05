const std = @import("std");
const cfg_mod = @import("../cfg.zig");
const ids = @import("../ids.zig");
const Cfg = cfg_mod.Cfg;
const IrNode = cfg_mod.IrNode;
const EngineError = @import("base.zig").EngineError;
const state_mod = @import("state.zig");
const store_mod = @import("store.zig");
const ProgramPoint = state_mod.ProgramPoint;
const ProgramState = state_mod.ProgramState;
const WideningKey = state_mod.WideningKey;

/// Default maximum number of unique states per program point.
/// Beyond this, new states at the same point are widened into an existing node
/// with the same convergence context, or analysis stops if none exists.
const default_max_states_per_point: u32 = 50;

/// A node in the exploded graph, keyed by (ProgramPoint, ProgramState).
pub const ExplodedNode = struct {
    /// The program point (CFG location)
    point: ProgramPoint,
    /// The abstract program state at this point
    state: ProgramState,
    /// Unique index of this node in the exploded graph
    index: u32,
    /// Indices of predecessor nodes in the exploded graph
    predecessors: std.ArrayList(u32),
    /// Indices of successor nodes in the exploded graph
    successors: std.ArrayList(u32),

    pub fn init(point: ProgramPoint, state: ProgramState, index: u32) ExplodedNode {
        return .{
            .point = point,
            .state = state,
            .index = index,
            .predecessors = .empty,
            .successors = .empty,
        };
    }

    pub fn deinit(self: *ExplodedNode, allocator: std.mem.Allocator) void {
        self.state.deinit();
        self.predecessors.deinit(allocator);
        self.successors.deinit(allocator);
    }

    /// Compute a combined hash for point and state (used for deduplication)
    pub fn computeKey(point: ProgramPoint, state: *ProgramState) u64 {
        var hasher = std.hash.Wyhash.init(0);
        // Include CFG identity to prevent collisions across different CFGs
        // during interprocedural analysis
        hasher.update(std.mem.asBytes(&@intFromPtr(point.cfg)));
        const node_index = ids.cfgIndex(point.node_index);
        hasher.update(std.mem.asBytes(&node_index));
        hasher.update(std.mem.asBytes(&point.kind));
        const state_hash = state.computeHash();
        hasher.update(std.mem.asBytes(&state_hash));
        return hasher.final();
    }
};

/// The exploded graph: a representation of all reachable (ProgramPoint, ProgramState) pairs.
/// This is the core data structure for path-sensitive analysis.
pub const ExplodedGraph = struct {
    allocator: std.mem.Allocator,
    /// All nodes in the exploded graph
    nodes: std.ArrayList(ExplodedNode),
    /// Map from (point, state) hash to node index for deduplication
    /// Hash collisions are possible; we accept the small risk as a pragmatic
    /// tradeoff for memory and performance.
    node_map: std.AutoHashMap(u64, u32),
    /// Reference to the CFG being analyzed
    cfg: *const Cfg,
    /// Count of states per program point (for widening)
    point_state_counts: std.AutoHashMap(u64, u32),
    /// Node indices per program point (for subsumption and cap widening)
    point_nodes: std.AutoHashMap(u64, std.ArrayList(u32)),
    /// Maximum number of unique states per program point before cap widening
    max_states_per_point: u32,
    /// Stored states at widening points (keyed by WideningKey)
    widening_states: std.HashMap(WideningKey, ProgramState, WideningKey.HashContext, std.hash_map.default_max_load_percentage),
    /// Visit count at widening points for delayed widening (keyed by WideningKey)
    widening_visits: std.HashMap(WideningKey, u32, WideningKey.HashContext, std.hash_map.default_max_load_percentage),
    /// Count of nodes created after widening
    widened_nodes: u32,
    /// Count of times widening converged (widened state equals previous)
    widening_converged: u32,

    pub fn init(allocator: std.mem.Allocator, cfg: *const Cfg) ExplodedGraph {
        return .{
            .allocator = allocator,
            .nodes = .empty,
            .node_map = std.AutoHashMap(u64, u32).init(allocator),
            .cfg = cfg,
            .point_state_counts = std.AutoHashMap(u64, u32).init(allocator),
            .point_nodes = std.AutoHashMap(u64, std.ArrayList(u32)).init(allocator),
            .max_states_per_point = default_max_states_per_point,
            .widening_states = std.HashMap(WideningKey, ProgramState, WideningKey.HashContext, std.hash_map.default_max_load_percentage).init(allocator),
            .widening_visits = std.HashMap(WideningKey, u32, WideningKey.HashContext, std.hash_map.default_max_load_percentage).init(allocator),
            .widened_nodes = 0,
            .widening_converged = 0,
        };
    }

    pub fn deinit(self: *ExplodedGraph) void {
        for (self.nodes.items) |*node| {
            node.deinit(self.allocator);
        }
        self.nodes.deinit(self.allocator);
        self.node_map.deinit();
        self.point_state_counts.deinit();
        var point_iter = self.point_nodes.valueIterator();
        while (point_iter.next()) |list_ptr| {
            list_ptr.deinit(self.allocator);
        }
        self.point_nodes.deinit();
        // Deinit stored widening states
        var it = self.widening_states.valueIterator();
        while (it.next()) |state_ptr| {
            state_ptr.deinit();
        }
        self.widening_states.deinit();
        self.widening_visits.deinit();
    }

    /// Options for widening at program points.
    pub const WideningOptions = struct {
        /// Whether to apply widening at this point
        apply_widening: bool = false,
        /// The widening key (must be provided if apply_widening is true)
        widening_key: ?WideningKey = null,
    };

    /// Result of getOrCreateNode operation.
    pub const GetOrCreateResult = struct {
        /// Index of the node
        index: u32,
        /// Whether this is a newly created node
        is_new: bool,
        /// Whether widening was applied
        widening_applied: bool = false,
        /// Whether widening converged (state unchanged after widening)
        converged: bool = false,
        /// Whether an existing node's state was updated (reprocess needed)
        state_updated: bool = false,
        /// Whether the caller should deinit the input state.
        /// True when: (1) node already exists (is_new == false), or
        ///            (2) widening was applied (the widened state, not input, was consumed)
        caller_should_deinit: bool = false,
    };

    const CapWideningResult = struct {
        index: u32,
        converged: bool,
        state_updated: bool,
    };

    fn ensurePointNodes(self: *ExplodedGraph, point_key: u64) EngineError!*std.ArrayList(u32) {
        const entry = self.point_nodes.getOrPut(point_key) catch |err| switch (err) {
            error.OutOfMemory => return EngineError.OutOfMemory,
        };
        if (!entry.found_existing) {
            entry.value_ptr.* = .empty;
        }
        return entry.value_ptr;
    }

    fn findSubsumingNode(self: *ExplodedGraph, point_key: u64, state: *const ProgramState) ?u32 {
        if (self.point_nodes.getPtr(point_key)) |list| {
            for (list.items) |index| {
                const existing_state = &self.nodes.items[index].state;
                if (existing_state.subsumes(state)) return index;
            }
        }
        return null;
    }

    /// Whether two states reached a widening point from the same context.
    ///
    /// The pending `catch` arms are part of that answer: two paths that have
    /// entered different arms of the same expression name different
    /// acquisitions for the bindings below them, so widening one into the
    /// other would drop whichever arm they disagree on and leave that binding
    /// unable to say which call produced its value. `WideningKey` keeps such
    /// paths in separate chains, so this normally holds and turns a state that
    /// genuinely came from elsewhere into the limit it is.
    /// Executed ownership must agree too: a transfer from a backedge cannot
    /// be intersected with a zero-pass state, nor copied onto that state.
    fn sameContext(a: *const ProgramState, b: *const ProgramState) bool {
        if (a.inline_depth != b.inline_depth) return false;
        if (a.call_stack.items.len != b.call_stack.items.len) return false;
        for (a.call_stack.items, b.call_stack.items) |call_site, other_site| {
            if (call_site.call_node != other_site.call_node or
                call_site.return_node != other_site.return_node or
                call_site.caller_cfg != other_site.caller_cfg)
            {
                return false;
            }
        }
        if (!a.catch_arms.eql(&b.catch_arms)) return false;
        return a.store.ownershipEql(&b.store);
    }

    fn widenOnCap(self: *ExplodedGraph, point_key: u64, state: *ProgramState) EngineError!CapWideningResult {
        const list = self.point_nodes.getPtr(point_key) orelse
            return error.AnalysisLimitExceeded;

        var target_index: ?u32 = null;
        for (list.items) |index| {
            const existing_state = &self.nodes.items[index].state;
            if (sameContext(existing_state, state)) {
                target_index = index;
                break;
            }
        }

        const cap_index = target_index orelse return error.AnalysisLimitExceeded;
        var target_node = &self.nodes.items[cap_index];

        var widened = target_node.state.widen(state) catch |err| switch (err) {
            error.OutOfMemory => return EngineError.OutOfMemory,
        };
        if (widened.eql(&target_node.state)) {
            widened.deinit();
            self.widening_converged += 1;
            return .{ .index = cap_index, .converged = true, .state_updated = false };
        }

        const new_key = ExplodedNode.computeKey(target_node.point, &widened);
        if (self.node_map.get(new_key)) |existing_index| {
            if (existing_index != cap_index) {
                widened.deinit();
                return .{ .index = existing_index, .converged = true, .state_updated = false };
            }
        }

        const old_key = ExplodedNode.computeKey(target_node.point, &target_node.state);
        target_node.state.deinit();
        target_node.state = widened;

        if (new_key != old_key) {
            _ = self.node_map.remove(old_key);
            self.node_map.putAssumeCapacity(new_key, cap_index);
        }

        self.widened_nodes += 1;
        return .{ .index = cap_index, .converged = false, .state_updated = true };
    }

    /// Get or create a node for the given point and state.
    /// Returns the node index and whether it was newly created.
    /// Ownership: The caller should deinit `state` if `is_new == false` OR if `widening_applied == true`.
    /// When widening is applied, the widened state (not the original) is used for the new node.
    pub fn getOrCreateNode(self: *ExplodedGraph, point: ProgramPoint, state: *ProgramState) EngineError!GetOrCreateResult {
        return self.getOrCreateNodeWithWidening(point, state, .{});
    }

    /// Get or create a node for the given point and state, with optional widening support.
    ///
    /// Flow:
    /// 1. Apply optional widening at the current program point. The key
    ///    partitions pending `catch` provenance and executed ownership edges,
    ///    so disagreeing paths widen in separate chains.
    /// 2. Deduplicate by (point, state) hash as usual.
    /// 3. Drop states subsumed by an existing node at this point. Subsumption
    ///    continues from the existing node, so it may only absorb a state that
    ///    adds no fact the checkers read; see `Store.subsumes`.
    /// 4. At the state cap, widen into a state with the same calling context,
    ///    pending `catch` provenance, and ownership edges, or return
    ///    AnalysisLimitExceeded without admitting another state.
    /// 5. Otherwise, create a new node.
    /// On error, the caller retains ownership of the input state.
    pub fn getOrCreateNodeWithWidening(
        self: *ExplodedGraph,
        point: ProgramPoint,
        state: *ProgramState,
        options: WideningOptions,
    ) EngineError!GetOrCreateResult {
        if (self.max_states_per_point == 0) return error.AnalysisLimitExceeded;

        var current_state = state;
        var widened_state: ?ProgramState = null;
        errdefer if (widened_state) |*ws| ws.deinit();
        var widening_applied = false;
        var converged = false;

        // Step 1: Apply optional widening at this point.
        if (options.apply_widening) {
            if (options.widening_key) |widening_key| {
                const visit_count = self.widening_visits.get(widening_key) orelse 0;

                if (visit_count == 0) {
                    // Reserve both maps before either takes ownership.
                    try self.widening_states.ensureUnusedCapacity(1);
                    try self.widening_visits.ensureUnusedCapacity(1);
                    const state_clone = try state.clone(self.allocator);
                    self.widening_states.putAssumeCapacity(widening_key, state_clone);
                    self.widening_visits.putAssumeCapacity(widening_key, 1);
                } else {
                    // Subsequent visits: widen incoming state with stored state
                    if (self.widening_states.getPtr(widening_key)) |stored_state| {
                        if (!sameContext(stored_state, state)) return error.AnalysisLimitExceeded;
                        const ws = stored_state.widen(state) catch |err| switch (err) {
                            error.OutOfMemory => return EngineError.OutOfMemory,
                        };
                        widened_state = ws;
                        widening_applied = true;

                        // Check for convergence: if widened state equals stored state, we've converged
                        if (ws.eql(stored_state)) {
                            converged = true;
                            self.widening_converged += 1;
                        } else {
                            // Clone first so allocation failure preserves the stored state.
                            const new_clone = try ws.clone(self.allocator);
                            stored_state.deinit();
                            stored_state.* = new_clone;
                        }

                        // Increment visit count
                        self.widening_visits.putAssumeCapacity(widening_key, visit_count + 1);
                    }

                    // Use widened state for deduplication
                    if (widened_state != null) {
                        current_state = &widened_state.?;
                    }
                }
            }
        }

        // Step 2: Deduplicate by (point, state) hash
        const key = ExplodedNode.computeKey(point, current_state);
        if (self.node_map.get(key)) |existing_index| {
            if (widened_state) |*ws| {
                ws.deinit();
            }
            return .{
                .index = existing_index,
                .is_new = false,
                .widening_applied = widening_applied,
                .converged = converged,
                .state_updated = false,
                .caller_should_deinit = true,
            };
        }

        const point_key = point.hash();

        // Step 3: Subsumption check against existing nodes at this point
        if (self.findSubsumingNode(point_key, current_state)) |existing_index| {
            if (widened_state) |*ws| {
                ws.deinit();
            }
            return .{
                .index = existing_index,
                .is_new = false,
                .widening_applied = widening_applied,
                .converged = converged,
                .state_updated = false,
                .caller_should_deinit = true,
            };
        }

        // Step 4: Check per-point state limit and widen into existing node if needed
        const current_count = self.point_state_counts.get(point_key) orelse 0;
        if (current_count >= self.max_states_per_point) {
            const cap_result = try self.widenOnCap(point_key, current_state);
            if (widened_state) |*ws| {
                ws.deinit();
            }
            return .{
                .index = cap_result.index,
                .is_new = false,
                .widening_applied = true,
                .converged = converged or cap_result.converged,
                .state_updated = cap_result.state_updated,
                .caller_should_deinit = true,
            };
        }

        const index: u32 = @intCast(self.nodes.items.len);

        // Finish all fallible allocations before transferring state ownership.
        try self.nodes.ensureUnusedCapacity(self.allocator, 1);
        try self.node_map.ensureUnusedCapacity(1);
        try self.point_state_counts.ensureUnusedCapacity(1);
        const point_list = try self.ensurePointNodes(point_key);
        try point_list.ensureUnusedCapacity(self.allocator, 1);

        const node_state = if (widened_state) |ws| ws else state.*;
        self.nodes.appendAssumeCapacity(ExplodedNode.init(point, node_state, index));
        self.node_map.putAssumeCapacity(key, index);
        self.point_state_counts.putAssumeCapacity(point_key, current_count + 1);
        point_list.appendAssumeCapacity(index);
        widened_state = null;

        if (widening_applied) {
            self.widened_nodes += 1;
        }

        // Caller should deinit the input state if widening was applied (the widened state was consumed, not the input)
        return .{
            .index = index,
            .is_new = true,
            .widening_applied = widening_applied,
            .converged = converged,
            .state_updated = false,
            .caller_should_deinit = widening_applied,
        };
    }

    /// Add an edge between two exploded graph nodes.
    /// Edges are deduplicated: a given (from, to) pair is recorded at most once,
    /// so repeated calls after state updates don't accumulate duplicates.
    /// On allocation failure neither list is mutated, so the successors/predecessors
    /// lockstep invariant is preserved.
    pub fn addEdge(self: *ExplodedGraph, from_index: u32, to_index: u32) EngineError!void {
        if (from_index >= self.nodes.items.len or to_index >= self.nodes.items.len) {
            return;
        }

        const successors = &self.nodes.items[from_index].successors;
        for (successors.items) |existing| {
            if (existing == to_index) return;
        }

        try successors.ensureUnusedCapacity(self.allocator, 1);
        try self.nodes.items[to_index].predecessors.ensureUnusedCapacity(self.allocator, 1);

        successors.appendAssumeCapacity(to_index);
        self.nodes.items[to_index].predecessors.appendAssumeCapacity(from_index);
    }

    /// Get a node by index
    pub fn getNode(self: *const ExplodedGraph, index: u32) ?*const ExplodedNode {
        if (index >= self.nodes.items.len) return null;
        return &self.nodes.items[index];
    }

    /// Get node count
    pub fn nodeCount(self: *const ExplodedGraph) usize {
        return self.nodes.items.len;
    }

    /// A zero cap rejects all states with AnalysisLimitExceeded.
    pub fn setMaxStatesPerPoint(self: *ExplodedGraph, max: u32) void {
        self.max_states_per_point = max;
    }

    /// Get the count of nodes created after widening.
    pub fn getWidenedNodeCount(self: *const ExplodedGraph) u32 {
        return self.widened_nodes;
    }

    /// Get the count of times widening converged.
    pub fn getWideningConvergedCount(self: *const ExplodedGraph) u32 {
        return self.widening_converged;
    }

    /// Get the count of distinct widening points being tracked.
    /// Each point in a unique calling context is counted separately.
    pub fn getTrackedWideningPointCount(self: *const ExplodedGraph) u32 {
        return @intCast(self.widening_states.count());
    }
};

test "ExplodedGraph node creation and deduplication" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.fn_entry));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var state1 = ProgramState.init(allocator);
    try state1.setVar(ids.varId(1), .{ .concrete_int = 42 });

    const result1 = try graph.getOrCreateNode(point, &state1);
    try testing.expect(result1.is_new);
    try testing.expectEqual(@as(u32, 0), result1.index);
    try testing.expectEqual(@as(usize, 1), graph.nodeCount());

    // Same point, same state should deduplicate
    var state1_clone = try state1.clone(allocator);
    const result2 = try graph.getOrCreateNode(point, &state1_clone);
    if (result2.caller_should_deinit) {
        state1_clone.deinit();
    }
    try testing.expect(!result2.is_new);
    try testing.expect(result2.caller_should_deinit);
    try testing.expectEqual(@as(u32, 0), result2.index);
    try testing.expectEqual(@as(usize, 1), graph.nodeCount());

    // Same point, different state should create new node
    var state2 = ProgramState.init(allocator);
    try state2.setVar(ids.varId(1), .{ .concrete_int = 100 });
    const result3 = try graph.getOrCreateNode(point, &state2);
    try testing.expect(result3.is_new);
    try testing.expectEqual(@as(u32, 1), result3.index);
    try testing.expectEqual(@as(usize, 2), graph.nodeCount());
}

test "ExplodedGraph subsumption avoids redundant states" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.fn_entry));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var general = ProgramState.init(allocator);
    try general.setVar(ids.varId(1), .unknown);
    const result1 = try graph.getOrCreateNode(point, &general);
    try testing.expect(result1.is_new);

    var specific = ProgramState.init(allocator);
    try specific.setVar(ids.varId(1), .{ .concrete_int = 42 });

    const result2 = try graph.getOrCreateNode(point, &specific);
    try testing.expect(!result2.is_new);
    try testing.expectEqual(result1.index, result2.index);
    try testing.expectEqual(@as(usize, 1), graph.nodeCount());

    specific.deinit();
}

test "ExplodedGraph edge operations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.fn_entry));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var state1 = ProgramState.init(allocator);
    const result1 = try graph.getOrCreateNode(point, &state1);

    var state2 = ProgramState.init(allocator);
    const result2 = try graph.getOrCreateNode(point, &state2);

    try graph.addEdge(result1.index, result2.index);

    const node1 = graph.getNode(result1.index) orelse return error.TestUnexpectedResult;
    const node2 = graph.getNode(result2.index) orelse return error.TestUnexpectedResult;

    try testing.expectEqual(@as(usize, 1), node1.successors.items.len);
    try testing.expectEqual(@as(usize, 1), node2.predecessors.items.len);
    try testing.expectEqual(result2.index, node1.successors.items[0]);
    try testing.expectEqual(result1.index, node2.predecessors.items[0]);
}

test "ExplodedGraph addEdge deduplicates repeated edges" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.fn_entry));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var state1 = ProgramState.init(allocator);
    try state1.setVar(ids.varId(1), .{ .concrete_int = 1 });
    const result1 = try graph.getOrCreateNode(point, &state1);

    var state2 = ProgramState.init(allocator);
    try state2.setVar(ids.varId(1), .{ .concrete_int = 2 });
    const result2 = try graph.getOrCreateNode(point, &state2);

    try graph.addEdge(result1.index, result2.index);
    try graph.addEdge(result1.index, result2.index);
    try graph.addEdge(result1.index, result2.index);

    const node1 = graph.getNode(result1.index) orelse return error.TestUnexpectedResult;
    const node2 = graph.getNode(result2.index) orelse return error.TestUnexpectedResult;

    try testing.expectEqual(@as(usize, 1), node1.successors.items.len);
    try testing.expectEqual(@as(usize, 1), node2.predecessors.items.len);
    try testing.expectEqual(result2.index, node1.successors.items[0]);
    try testing.expectEqual(result1.index, node2.predecessors.items[0]);
}

test "ExplodedGraph addEdge keeps distinct edges" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.fn_entry));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var state1 = ProgramState.init(allocator);
    try state1.setVar(ids.varId(1), .{ .concrete_int = 1 });
    const result1 = try graph.getOrCreateNode(point, &state1);

    var state2 = ProgramState.init(allocator);
    try state2.setVar(ids.varId(1), .{ .concrete_int = 2 });
    const result2 = try graph.getOrCreateNode(point, &state2);

    var state3 = ProgramState.init(allocator);
    try state3.setVar(ids.varId(1), .{ .concrete_int = 3 });
    const result3 = try graph.getOrCreateNode(point, &state3);

    try graph.addEdge(result1.index, result2.index);
    try graph.addEdge(result1.index, result3.index);
    try graph.addEdge(result1.index, result2.index);

    const node1 = graph.getNode(result1.index) orelse return error.TestUnexpectedResult;

    try testing.expectEqual(@as(usize, 2), node1.successors.items.len);
}

test "ExplodedGraph widening first visit stores state" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var state = ProgramState.init(allocator);
    try state.setVar(ids.varId(1), .{ .concrete_int = 10 });

    const widening_key = WideningKey.init(point, &state);

    const result = try graph.getOrCreateNodeWithWidening(point, &state, .{
        .apply_widening = true,
        .widening_key = widening_key,
    });

    try testing.expect(result.is_new);
    try testing.expect(!result.widening_applied);
    try testing.expect(!result.converged);
    try testing.expectEqual(@as(u32, 0), graph.getWidenedNodeCount());
    try testing.expectEqual(@as(u32, 0), graph.getWideningConvergedCount());

    // Verify state was stored
    try testing.expect(graph.widening_states.get(widening_key) != null);
    try testing.expectEqual(@as(?u32, 1), graph.widening_visits.get(widening_key));
}

test "ExplodedGraph widening subsequent visit applies widening" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    // First visit: store state
    var state1 = ProgramState.init(allocator);
    try state1.setVar(ids.varId(1), .{ .concrete_int = 10 });

    const widening_key = WideningKey.init(point, &state1);

    _ = try graph.getOrCreateNodeWithWidening(point, &state1, .{
        .apply_widening = true,
        .widening_key = widening_key,
    });

    // Second visit: different state should be widened
    var state2 = ProgramState.init(allocator);
    try state2.setVar(ids.varId(1), .{ .concrete_int = 20 }); // different value

    const result = try graph.getOrCreateNodeWithWidening(point, &state2, .{
        .apply_widening = true,
        .widening_key = widening_key,
    });

    try testing.expect(result.is_new);
    try testing.expect(result.widening_applied);
    try testing.expect(!result.converged); // widened to unknown, different from stored
    try testing.expectEqual(@as(u32, 1), graph.getWidenedNodeCount());
    try testing.expectEqual(@as(?u32, 2), graph.widening_visits.get(widening_key));
    // Caller needs to clean up state2 since it wasn't consumed (widened state was used instead)
    state2.deinit();
}

test "ExplodedGraph widening convergence detection" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    // First visit: store state with unknown value
    var state1 = ProgramState.init(allocator);
    try state1.setVar(ids.varId(1), .unknown);

    const widening_key = WideningKey.init(point, &state1);

    _ = try graph.getOrCreateNodeWithWidening(point, &state1, .{
        .apply_widening = true,
        .widening_key = widening_key,
    });

    // Second visit: same unknown value should converge
    var state2 = ProgramState.init(allocator);
    try state2.setVar(ids.varId(1), .unknown);

    const result = try graph.getOrCreateNodeWithWidening(point, &state2, .{
        .apply_widening = true,
        .widening_key = widening_key,
    });

    // Should deduplicate since widened state equals stored state
    try testing.expect(!result.is_new);
    try testing.expect(result.widening_applied);
    try testing.expect(result.converged);
    try testing.expectEqual(@as(u32, 1), graph.getWideningConvergedCount());
    // Caller needs to clean up state2 since it wasn't consumed
    state2.deinit();
}

test "ExplodedGraph widening stats tracking" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    try testing.expectEqual(@as(u32, 0), graph.getWidenedNodeCount());
    try testing.expectEqual(@as(u32, 0), graph.getWideningConvergedCount());
}

test "ExplodedGraph widen-on-cap updates existing node" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    graph.setMaxStatesPerPoint(2);

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var state1 = ProgramState.init(allocator);
    try state1.setVar(ids.varId(1), .{ .concrete_int = 10 });
    const result1 = try graph.getOrCreateNode(point, &state1);
    try testing.expect(result1.is_new);

    var state2 = ProgramState.init(allocator);
    try state2.setVar(ids.varId(1), .{ .concrete_int = 20 });
    const result2 = try graph.getOrCreateNode(point, &state2);
    try testing.expect(result2.is_new);

    var state3 = ProgramState.init(allocator);
    try state3.setVar(ids.varId(1), .{ .concrete_int = 30 });

    const result = try graph.getOrCreateNodeWithWidening(point, &state3, .{});

    try testing.expect(!result.is_new);
    try testing.expect(result.widening_applied);
    try testing.expect(result.state_updated);

    // The cap widened `10` and `30` into one integer interval: the lower bound
    // did not move and is kept, the upper one did and is thrown to the end of
    // the `i64` domain. The loop condition can still read it.
    const widened_node = graph.getNode(result.index) orelse return error.TestUnexpectedResult;
    const widened_counter = widened_node.state.getVar(ids.varId(1)) orelse
        return error.TestUnexpectedResult;
    try testing.expect(widened_counter.eql(.{ .int_range = .{
        .min = 10,
        .max = std.math.maxInt(i64),
    } }));

    state3.deinit();
}

test "ExplodedGraph widen-on-cap respects context" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.fn_entry));
    _ = try cfg.addNode(IrNode.init(.fn_entry));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    graph.setMaxStatesPerPoint(1);

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var state1 = ProgramState.init(allocator);
    try state1.setVar(ids.varId(1), .{ .concrete_int = 10 });
    const result1 = try graph.getOrCreateNode(point, &state1);
    try testing.expect(result1.is_new);

    var state2 = ProgramState.init(allocator);
    defer state2.deinit();
    try state2.setVar(ids.varId(1), .{ .concrete_int = 20 });
    try state2.pushCallSite(state_mod.CallSite{ .call_node = ids.cfgId(0), .caller_cfg = &cfg, .return_node = ids.cfgId(1) });

    try testing.expectError(error.AnalysisLimitExceeded, graph.getOrCreateNodeWithWidening(point, &state2, .{}));
    try testing.expectEqual(@as(usize, 1), graph.nodeCount());
    const stored = graph.getNode(result1.index) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(usize, 0), stored.state.call_stack.items.len);
    const stored_value = stored.state.getVar(ids.varId(1)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(i64, 10), stored_value.concrete_int);
    try testing.expectEqual(@as(usize, 1), state2.call_stack.items.len);
    const incoming_value = state2.getVar(ids.varId(1)) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(i64, 20), incoming_value.concrete_int);
}

test "ExplodedGraph without widening options works as before" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();

    _ = try cfg.addNode(IrNode.init(.fn_entry));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var state = ProgramState.init(allocator);
    try state.setVar(ids.varId(1), .{ .concrete_int = 42 });

    const result = try graph.getOrCreateNode(point, &state);

    try testing.expect(result.is_new);
    try testing.expect(!result.widening_applied);
    try testing.expect(!result.converged);
    try testing.expectEqual(@as(u32, 0), graph.getWidenedNodeCount());
}

test "ExplodedGraph zero cap rejects states without taking ownership" {
    const allocator = std.testing.allocator;
    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    const entry = try cfg.addNode(IrNode.init(.fn_entry));
    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();
    graph.setMaxStatesPerPoint(0);

    var state = ProgramState.init(allocator);
    var owns_state = true;
    defer if (owns_state) state.deinit();
    try state.setVar(ids.varId(1), .{ .concrete_int = 42 });
    const point = ProgramPoint.initPre(entry, &cfg);
    try std.testing.expectError(error.AnalysisLimitExceeded, graph.getOrCreateNodeWithWidening(point, &state, .{
        .apply_widening = true,
        .widening_key = WideningKey.init(point, &state),
    }));
    try std.testing.expectEqual(@as(usize, 0), graph.nodeCount());
    try std.testing.expectEqual(@as(u32, 0), graph.getTrackedWideningPointCount());
    const value = state.getVar(ids.varId(1)) orelse return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(i64, 42), value.concrete_int);

    graph.setMaxStatesPerPoint(1);
    const result = try graph.getOrCreateNode(point, &state);
    owns_state = result.caller_should_deinit;
    try std.testing.expect(result.is_new);
}

test "ExplodedGraph cap one widens the same context with transactional allocation" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testCapAllocationFailure, .{});
}

fn testCapAllocationFailure(allocator: std.mem.Allocator) !void {
    var cfg = Cfg.init(std.testing.allocator);
    defer cfg.deinit();
    const entry = try cfg.addNode(IrNode.init(.fn_entry));
    const exit = try cfg.addNode(IrNode.init(.fn_exit));
    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();
    graph.setMaxStatesPerPoint(1);
    const point = ProgramPoint.initPre(entry, &cfg);
    const bytes = ids.varId(30);
    const out = ids.varId(31);

    var first = ProgramState.init(allocator);
    var owns_first = true;
    defer if (owns_first) first.deinit();
    try first.setVar(ids.varId(1), .{ .concrete_int = 10 });
    first.incrementInlineDepth();
    try first.pushCallSite(.{ .call_node = entry, .caller_cfg = &cfg, .return_node = exit });
    // What the checkers below the loop read: the transfer the aggregate store
    // executed, and a handler chain deeper than the inline facts hold.
    try first.trackAllocation(bytes);
    try first.trackOwnership(bytes, out);
    var arm_node: u32 = 1;
    while (arm_node <= 6) : (arm_node += 1) {
        try first.pushCatchArm(arm_node, .success);
    }
    const initial = try graph.getOrCreateNode(point, &first);
    owns_first = initial.caller_should_deinit;

    const initial_node = graph.getNode(initial.index) orelse return error.TestUnexpectedResult;
    var incoming = try initial_node.state.clone(allocator);
    defer incoming.deinit();
    try incoming.setVar(ids.varId(1), .{ .concrete_int = 20 });
    const result = graph.getOrCreateNode(point, &incoming) catch |err| {
        try std.testing.expectEqual(@as(usize, 1), graph.nodeCount());
        const unchanged = graph.getNode(initial.index) orelse return error.TestUnexpectedResult;
        const unchanged_value = unchanged.state.getVar(ids.varId(1)) orelse
            return error.TestUnexpectedResult;
        try std.testing.expectEqual(@as(i64, 10), unchanged_value.concrete_int);
        // The transfer and the spilled arms stayed with the state the graph had
        // already stored, and the failed call changed nothing on either side.
        try std.testing.expect(unchanged.state.hasOwnedResources(out));
        try std.testing.expectEqual(@as(usize, 6), unchanged.state.catch_arms.len());
        try std.testing.expect(unchanged.state.catch_arms.spilled != null);
        const incoming_value = incoming.getVar(ids.varId(1)) orelse return error.TestUnexpectedResult;
        try std.testing.expectEqual(@as(i64, 20), incoming_value.concrete_int);
        try std.testing.expect(incoming.hasOwnedResources(out));
        try std.testing.expectEqual(@as(usize, 6), incoming.catch_arms.len());
        return err;
    };
    try std.testing.expect(result.widening_applied);
    try std.testing.expect(result.state_updated);
    try std.testing.expect(result.caller_should_deinit);
    try std.testing.expectEqual(initial.index, result.index);
    try std.testing.expectEqual(@as(usize, 1), graph.nodeCount());
    const widened = graph.getNode(result.index) orelse return error.TestUnexpectedResult;
    const widened_counter = widened.state.getVar(ids.varId(1)) orelse
        return error.TestUnexpectedResult;
    try std.testing.expect(widened_counter.eql(.{ .int_range = .{
        .min = 10,
        .max = std.math.maxInt(i64),
    } }));
    try std.testing.expectEqual(@as(u32, 1), widened.state.getInlineDepth());
    try std.testing.expectEqual(entry, widened.state.call_stack.items[0].call_node);
    try std.testing.expect(widened.state.hasOwnedResources(out));
    try std.testing.expectEqual(@as(usize, 6), widened.state.catch_arms.len());
    try std.testing.expect(widened.state.catch_arms.spilled != null);
    var widened_arm: u32 = 1;
    while (widened_arm <= 6) : (widened_arm += 1) {
        try std.testing.expectEqual(state_mod.CatchArm.success, widened.state.getCatchArm(widened_arm).?);
    }
}

test "ExplodedGraph insertion preserves ownership on allocation failure" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testInsertionAllocationFailure, .{});
}

fn testInsertionAllocationFailure(allocator: std.mem.Allocator) !void {
    var cfg = Cfg.init(std.testing.allocator);
    defer cfg.deinit();
    const node = try cfg.addNode(IrNode.init(.loop_header));
    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();
    const point = ProgramPoint.initPre(node, &cfg);
    const bytes = ids.varId(30);
    const out = ids.varId(31);

    for (0..3) |value| {
        var state = ProgramState.init(std.testing.allocator);
        var owns_state = true;
        defer if (owns_state) state.deinit();
        try state.setVar(ids.varId(1), .{ .concrete_int = @intCast(value) });
        // Every insert here carries the same transfer and the same spilled arm
        // chain, so a failure has to leave both on one side or the other,
        // never half on each.
        try state.trackAllocation(bytes);
        try state.trackOwnership(bytes, out);
        var arm_node: u32 = 1;
        while (arm_node <= 6) : (arm_node += 1) {
            try state.pushCatchArm(arm_node, if (arm_node % 2 == 0) .success else .failure);
        }

        const before = graph.nodeCount();
        const result = graph.getOrCreateNodeWithWidening(point, &state, .{
            .apply_widening = true,
            .widening_key = WideningKey.init(point, &state),
        }) catch |err| {
            // The graph kept the nodes it had, and the caller's state still
            // carries everything it brought.
            try std.testing.expectEqual(before, graph.nodeCount());
            try std.testing.expect(state.hasOwnedResources(out));
            try std.testing.expectEqual(@as(usize, 6), state.catch_arms.len());
            return err;
        };
        owns_state = result.caller_should_deinit;
        const stored = graph.getNode(result.index) orelse return error.TestUnexpectedResult;
        const observed = stored.state.getVar(ids.varId(1)) orelse return error.TestUnexpectedResult;
        try std.testing.expect(observed.subsumes(.{ .concrete_int = @intCast(value) }));
        // The stored state holds the transfer and the whole arm chain, spilled
        // decisions included.
        try std.testing.expect(stored.state.hasOwnedResources(out));
        try std.testing.expectEqual(@as(usize, 6), stored.state.catch_arms.len());
        try std.testing.expect(stored.state.catch_arms.spilled != null);
        var stored_arm: u32 = 1;
        while (stored_arm <= 6) : (stored_arm += 1) {
            const arm: state_mod.CatchArm = if (stored_arm % 2 == 0) .success else .failure;
            try std.testing.expectEqual(arm, stored.state.getCatchArm(stored_arm).?);
        }
    }
}

test "ExplodedGraph keeps an executed ownership transfer out of the owner-free header" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const bytes = ids.varId(10);
    const out = ids.varId(11);
    const counter = ids.varId(12);

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();
    graph.setMaxStatesPerPoint(4);

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    // The header entry state holds the allocation but has not stored the
    // payload into the aggregate yet, and it says nothing about the cursor.
    var header = ProgramState.init(allocator);
    var owns_header = true;
    defer if (owns_header) header.deinit();
    try header.setVar(counter, .unknown);
    try header.trackAllocation(bytes);
    const header_result = try graph.getOrCreateNodeWithWidening(point, &header, .{
        .apply_widening = true,
        .widening_key = WideningKey.init(point, &header),
    });
    owns_header = header_result.caller_should_deinit;
    try testing.expect(header_result.is_new);

    // The backedge state is the same allocation once `aggregate[i] = payload`
    // has handed the payload's resources over and the cursor has advanced.
    var backedge = ProgramState.init(allocator);
    var owns_backedge = true;
    defer if (owns_backedge) backedge.deinit();
    try backedge.setVar(counter, .{ .concrete_int = 1 });
    try backedge.trackAllocation(bytes);
    try backedge.trackOwnership(bytes, out);
    const backedge_result = try graph.getOrCreateNodeWithWidening(point, &backedge, .{
        .apply_widening = true,
        .widening_key = WideningKey.init(point, &backedge),
    });
    owns_backedge = backedge_result.caller_should_deinit;

    // The header state is at least as general as the backedge state in every
    // other respect, so absorbing the backedge there is exactly the merge that
    // loses the transfer.
    try testing.expect(backedge_result.is_new);
    try testing.expect(backedge_result.index != header_result.index);
    try testing.expectEqual(@as(usize, 2), graph.nodeCount());

    // The aggregate takes the payload's resources with it at the exit, so the
    // owned node reports nothing.
    const owned_node = graph.getNode(backedge_result.index) orelse return error.TestUnexpectedResult;
    var owned_exit = try owned_node.state.clone(allocator);
    defer owned_exit.deinit();
    try owned_exit.trackEscapeOwned(out);
    try owned_exit.trackLeaks();
    try testing.expectEqual(@as(usize, 0), owned_exit.getStoreViolations().len);

    // The header node never made the transfer, so the same exit leaks the
    // payload it was still holding.
    const header_node = graph.getNode(header_result.index) orelse return error.TestUnexpectedResult;
    var header_exit = try header_node.state.clone(allocator);
    defer header_exit.deinit();
    try header_exit.trackEscapeOwned(out);
    try header_exit.trackLeaks();
    try testing.expectEqual(@as(usize, 1), header_exit.getStoreViolations().len);
    try testing.expectEqual(store_mod.StoreViolationKind.resource_leak, header_exit.getStoreViolations()[0].kind);
    try testing.expectEqual(bytes, header_exit.getStoreViolations()[0].region);

    // The next pass has no cursor left to say, so the chain widens: the value
    // goes, the transfer stays.
    var repeat = try owned_node.state.clone(allocator);
    var owns_repeat = true;
    defer if (owns_repeat) repeat.deinit();
    try repeat.setVar(counter, .unknown);
    const repeat_result = try graph.getOrCreateNodeWithWidening(point, &repeat, .{
        .apply_widening = true,
        .widening_key = WideningKey.init(point, &repeat),
    });
    owns_repeat = repeat_result.caller_should_deinit;
    try testing.expect(repeat_result.is_new);
    try testing.expect(repeat_result.widening_applied);
    try testing.expect(!repeat_result.converged);
    try testing.expectEqual(@as(usize, 3), graph.nodeCount());

    const widened_node = graph.getNode(repeat_result.index) orelse return error.TestUnexpectedResult;
    const widened_counter = widened_node.state.getVar(counter) orelse return error.TestUnexpectedResult;
    try testing.expect(widened_counter.eql(.unknown));
    try testing.expect(widened_node.state.hasOwnedResources(out));
    try testing.expectEqual(store_mod.ResourceState.allocated, widened_node.state.getRegionState(bytes).?);

    // An equal repeat converges onto the same node, which still holds the
    // transfer, so nothing about the aggregate is lost at convergence.
    var again = try widened_node.state.clone(allocator);
    var owns_again = true;
    defer if (owns_again) again.deinit();
    const again_result = try graph.getOrCreateNodeWithWidening(point, &again, .{
        .apply_widening = true,
        .widening_key = WideningKey.init(point, &again),
    });
    owns_again = again_result.caller_should_deinit;
    try testing.expect(!again_result.is_new);
    try testing.expect(again_result.converged);
    try testing.expectEqual(repeat_result.index, again_result.index);
    try testing.expectEqual(@as(usize, 3), graph.nodeCount());
    try testing.expectEqual(@as(u32, 1), graph.getWideningConvergedCount());

    const converged_node = graph.getNode(again_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(converged_node.state.hasOwnedResources(out));
    var converged_exit = try converged_node.state.clone(allocator);
    defer converged_exit.deinit();
    try converged_exit.trackEscapeOwned(out);
    try converged_exit.trackLeaks();
    try testing.expectEqual(@as(usize, 0), converged_exit.getStoreViolations().len);
}

test "ExplodedGraph cap one refuses an ownership difference without moving either state" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const bytes = ids.varId(20);
    const out = ids.varId(21);
    const counter = ids.varId(22);

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();
    graph.setMaxStatesPerPoint(1);

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var initial = ProgramState.init(allocator);
    var owns_initial = true;
    defer if (owns_initial) initial.deinit();
    try initial.setVar(counter, .{ .concrete_int = 1 });
    try initial.trackAllocation(bytes);
    const initial_result = try graph.getOrCreateNode(point, &initial);
    owns_initial = initial_result.caller_should_deinit;

    // Same point, same context, same allocation, but the payload is in the
    // aggregate by now: widening the stored state with this one would drop the
    // transfer instead of reporting it.
    var incoming = ProgramState.init(allocator);
    defer incoming.deinit();
    try incoming.setVar(counter, .{ .concrete_int = 2 });
    try incoming.trackAllocation(bytes);
    try incoming.trackOwnership(bytes, out);

    try testing.expectError(error.AnalysisLimitExceeded, graph.getOrCreateNodeWithWidening(point, &incoming, .{}));

    // Neither side moved: the limit is reported before anything is widened.
    try testing.expectEqual(@as(usize, 1), graph.nodeCount());
    const stored = graph.getNode(initial_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(!stored.state.hasOwnedResources(out));
    try testing.expectEqual(store_mod.ResourceState.allocated, stored.state.getRegionState(bytes).?);
    const stored_counter = stored.state.getVar(counter) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(i64, 1), stored_counter.concrete_int);
    try testing.expect(incoming.hasOwnedResources(out));
    try testing.expectEqual(store_mod.ResourceState.allocated, incoming.getRegionState(bytes).?);
    const incoming_counter = incoming.getVar(counter) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(i64, 2), incoming_counter.concrete_int);
}

test "ExplodedGraph cap one refuses to widen an owner-free state into an owned one" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const bytes = ids.varId(20);
    const out = ids.varId(21);
    const counter = ids.varId(22);

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();
    graph.setMaxStatesPerPoint(1);

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    var initial = ProgramState.init(allocator);
    var owns_initial = true;
    defer if (owns_initial) initial.deinit();
    try initial.setVar(counter, .{ .concrete_int = 1 });
    try initial.trackAllocation(bytes);
    try initial.trackOwnership(bytes, out);
    const initial_result = try graph.getOrCreateNode(point, &initial);
    owns_initial = initial_result.caller_should_deinit;

    // The path that never made the transfer is the mirror image of the one
    // above: widening this into the stored state would erase the stored
    // transfer, and absorbing it would erase this path's payload at the exit.
    var incoming = ProgramState.init(allocator);
    defer incoming.deinit();
    try incoming.setVar(counter, .{ .concrete_int = 2 });
    try incoming.trackAllocation(bytes);

    try testing.expectError(error.AnalysisLimitExceeded, graph.getOrCreateNodeWithWidening(point, &incoming, .{}));

    try testing.expectEqual(@as(usize, 1), graph.nodeCount());
    const stored = graph.getNode(initial_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(stored.state.hasOwnedResources(out));
    try testing.expectEqual(store_mod.ResourceState.allocated, stored.state.getRegionState(bytes).?);
    const stored_counter = stored.state.getVar(counter) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(i64, 1), stored_counter.concrete_int);
    try testing.expect(!incoming.hasOwnedResources(out));
    try testing.expectEqual(store_mod.ResourceState.allocated, incoming.getRegionState(bytes).?);
}

test "ExplodedGraph cap widening picks the node whose ownership matches" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const bytes = ids.varId(20);
    const out_a = ids.varId(21);
    const out_b = ids.varId(22);
    const counter = ids.varId(23);

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();
    graph.setMaxStatesPerPoint(2);

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    // Two paths reach the header with the same allocation handed to two
    // different aggregates, so the transfer is the only thing telling them
    // apart and both have to be kept.
    var first = ProgramState.init(allocator);
    var owns_first = true;
    defer if (owns_first) first.deinit();
    try first.setVar(counter, .{ .concrete_int = 1 });
    try first.trackAllocation(bytes);
    try first.trackOwnership(bytes, out_a);
    const first_result = try graph.getOrCreateNode(point, &first);
    owns_first = first_result.caller_should_deinit;
    try testing.expect(first_result.is_new);

    var second = ProgramState.init(allocator);
    var owns_second = true;
    defer if (owns_second) second.deinit();
    try second.setVar(counter, .{ .concrete_int = 2 });
    try second.trackAllocation(bytes);
    try second.trackOwnership(bytes, out_b);
    const second_result = try graph.getOrCreateNode(point, &second);
    owns_second = second_result.caller_should_deinit;
    try testing.expect(second_result.is_new);
    try testing.expectEqual(@as(usize, 2), graph.nodeCount());

    // At the cap a state may only widen into the node that holds the same
    // transfer, never into the first candidate that merely looks alike.
    var incoming = ProgramState.init(allocator);
    var owns_incoming = true;
    defer if (owns_incoming) incoming.deinit();
    try incoming.setVar(counter, .{ .concrete_int = 3 });
    try incoming.trackAllocation(bytes);
    try incoming.trackOwnership(bytes, out_b);
    const result = try graph.getOrCreateNodeWithWidening(point, &incoming, .{});
    owns_incoming = result.caller_should_deinit;
    try testing.expect(!result.is_new);
    try testing.expect(result.widening_applied);
    try testing.expect(result.state_updated);
    try testing.expectEqual(second_result.index, result.index);
    try testing.expectEqual(@as(usize, 2), graph.nodeCount());

    const widened = graph.getNode(second_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(widened.state.hasOwnedResources(out_b));
    try testing.expect(!widened.state.hasOwnedResources(out_a));
    try testing.expectEqual(store_mod.ResourceState.allocated, widened.state.getRegionState(bytes).?);

    const untouched = graph.getNode(first_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(untouched.state.hasOwnedResources(out_a));
    try testing.expect(!untouched.state.hasOwnedResources(out_b));
    const untouched_counter = untouched.state.getVar(counter) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(i64, 1), untouched_counter.concrete_int);

    // Releasing the aggregate this path did not hand the payload to still
    // leaks it; releasing the one it did carries the payload away.
    var wrong_aggregate = try widened.state.clone(allocator);
    defer wrong_aggregate.deinit();
    try wrong_aggregate.trackEscapeOwned(out_a);
    try wrong_aggregate.trackLeaks();
    try testing.expectEqual(@as(usize, 1), wrong_aggregate.getStoreViolations().len);
    try testing.expectEqual(store_mod.StoreViolationKind.resource_leak, wrong_aggregate.getStoreViolations()[0].kind);
    try testing.expectEqual(bytes, wrong_aggregate.getStoreViolations()[0].region);

    var right_aggregate = try widened.state.clone(allocator);
    defer right_aggregate.deinit();
    try right_aggregate.trackEscapeOwned(out_b);
    try right_aggregate.trackLeaks();
    try testing.expectEqual(@as(usize, 0), right_aggregate.getStoreViolations().len);
}

test "ExplodedGraph keeps the spilled catch-arm partition beside the ownership one" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const bytes = ids.varId(30);
    const out = ids.varId(31);
    const other_out = ids.varId(32);
    const counter = ids.varId(33);

    var cfg = Cfg.init(allocator);
    defer cfg.deinit();
    _ = try cfg.addNode(IrNode.init(.loop_header));

    var graph = ExplodedGraph.init(allocator, &cfg);
    defer graph.deinit();
    graph.setMaxStatesPerPoint(2);

    const point = ProgramPoint.initPre(ids.cfgId(0), &cfg);

    // A handler chain deeper than a state holds inline: arms 5 to 7 spill.
    // Both states below carry that chain, and they differ only in whether the
    // payload reached the aggregate.
    var header = ProgramState.init(allocator);
    var owns_header = true;
    defer if (owns_header) header.deinit();
    try header.setVar(counter, .{ .concrete_int = 1 });
    try header.trackAllocation(bytes);
    var arm_node: u32 = 1;
    while (arm_node <= 7) : (arm_node += 1) {
        try header.pushCatchArm(arm_node, if (arm_node % 2 == 0) .success else .failure);
    }
    try testing.expect(header.catch_arms.spilled != null);
    const header_result = try graph.getOrCreateNode(point, &header);
    owns_header = header_result.caller_should_deinit;
    try testing.expect(header_result.is_new);

    var owned = ProgramState.init(allocator);
    var owns_owned = true;
    defer if (owns_owned) owned.deinit();
    try owned.setVar(counter, .{ .concrete_int = 1 });
    try owned.trackAllocation(bytes);
    try owned.trackOwnership(bytes, out);
    arm_node = 1;
    while (arm_node <= 7) : (arm_node += 1) {
        try owned.pushCatchArm(arm_node, if (arm_node % 2 == 0) .success else .failure);
    }
    const owned_result = try graph.getOrCreateNode(point, &owned);
    owns_owned = owned_result.caller_should_deinit;

    // Same arm chain, same cursor, same allocation: only the transfer tells
    // them apart, so the owner-free state may not absorb the owned one.
    try testing.expect(owned_result.is_new);
    try testing.expect(owned_result.index != header_result.index);
    try testing.expectEqual(@as(usize, 2), graph.nodeCount());

    // The cap holds both partitions: a spilled arm that disagrees is still a
    // different arm chain, and no merge happens even though the two states
    // own the payload identically.
    var flipped_arm = ProgramState.init(allocator);
    defer flipped_arm.deinit();
    try flipped_arm.setVar(counter, .{ .concrete_int = 1 });
    try flipped_arm.trackAllocation(bytes);
    try flipped_arm.trackOwnership(bytes, out);
    arm_node = 1;
    while (arm_node <= 7) : (arm_node += 1) {
        const arm: state_mod.CatchArm = if (arm_node == 7)
            .success
        else if (arm_node % 2 == 0) .success else .failure;
        try flipped_arm.pushCatchArm(arm_node, arm);
    }
    try testing.expectError(error.AnalysisLimitExceeded, graph.getOrCreateNodeWithWidening(point, &flipped_arm, .{}));
    try testing.expectEqual(@as(usize, 2), graph.nodeCount());
    try testing.expectEqual(@as(usize, 7), flipped_arm.catch_arms.len());
    try testing.expectEqual(state_mod.CatchArm.success, flipped_arm.getCatchArm(7).?);
    try testing.expect(flipped_arm.hasOwnedResources(out));

    // The same chain with the payload in a different aggregate is a different
    // transfer, so it is a limit rather than a merge.
    var other_owner = ProgramState.init(allocator);
    defer other_owner.deinit();
    try other_owner.setVar(counter, .{ .concrete_int = 1 });
    try other_owner.trackAllocation(bytes);
    try other_owner.trackOwnership(bytes, other_out);
    arm_node = 1;
    while (arm_node <= 7) : (arm_node += 1) {
        try other_owner.pushCatchArm(arm_node, if (arm_node % 2 == 0) .success else .failure);
    }
    try testing.expectError(error.AnalysisLimitExceeded, graph.getOrCreateNodeWithWidening(point, &other_owner, .{}));
    try testing.expectEqual(@as(usize, 2), graph.nodeCount());
    try testing.expect(other_owner.hasOwnedResources(other_out));
    try testing.expectEqual(@as(usize, 7), other_owner.catch_arms.len());

    // Neither rejected state cost the graph an arm: both stored nodes still
    // carry the whole chain, inline and spilled alike.
    const header_node = graph.getNode(header_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(!header_node.state.hasOwnedResources(out));
    try testing.expectEqual(@as(usize, 7), header_node.state.catch_arms.len());
    try testing.expect(header_node.state.catch_arms.spilled != null);
    arm_node = 1;
    while (arm_node <= 7) : (arm_node += 1) {
        const arm: state_mod.CatchArm = if (arm_node % 2 == 0) .success else .failure;
        try testing.expectEqual(arm, header_node.state.getCatchArm(arm_node).?);
    }

    const owned_node = graph.getNode(owned_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(owned_node.state.hasOwnedResources(out));
    try testing.expectEqual(@as(usize, 7), owned_node.state.catch_arms.len());
    try testing.expect(owned_node.state.catch_arms.spilled != null);

    // A state that agrees on both partitions widens into the owned node, and
    // the widened node keeps every arm and the transfer.
    var widen_in = ProgramState.init(allocator);
    var owns_widen_in = true;
    defer if (owns_widen_in) widen_in.deinit();
    try widen_in.setVar(counter, .{ .concrete_int = 2 });
    try widen_in.trackAllocation(bytes);
    try widen_in.trackOwnership(bytes, out);
    arm_node = 1;
    while (arm_node <= 7) : (arm_node += 1) {
        try widen_in.pushCatchArm(arm_node, if (arm_node % 2 == 0) .success else .failure);
    }
    const widen_result = try graph.getOrCreateNodeWithWidening(point, &widen_in, .{});
    owns_widen_in = widen_result.caller_should_deinit;
    try testing.expect(!widen_result.is_new);
    try testing.expect(widen_result.widening_applied);
    try testing.expect(widen_result.state_updated);
    try testing.expectEqual(owned_result.index, widen_result.index);
    try testing.expectEqual(@as(usize, 2), graph.nodeCount());

    const widened = graph.getNode(widen_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(widened.state.hasOwnedResources(out));
    try testing.expect(!widened.state.hasOwnedResources(other_out));
    try testing.expectEqual(store_mod.ResourceState.allocated, widened.state.getRegionState(bytes).?);
    try testing.expectEqual(@as(usize, 7), widened.state.catch_arms.len());
    try testing.expect(widened.state.catch_arms.spilled != null);
    arm_node = 1;
    while (arm_node <= 7) : (arm_node += 1) {
        const arm: state_mod.CatchArm = if (arm_node % 2 == 0) .success else .failure;
        try testing.expectEqual(arm, widened.state.getCatchArm(arm_node).?);
    }

    // The header node was not the widening target, so it still owns nothing.
    const kept_header = graph.getNode(header_result.index) orelse return error.TestUnexpectedResult;
    try testing.expect(!kept_header.state.hasOwnedResources(out));
    const kept_header_counter = kept_header.state.getVar(counter) orelse return error.TestUnexpectedResult;
    try testing.expectEqual(@as(i64, 1), kept_header_counter.concrete_int);
    try testing.expectEqual(@as(usize, 7), kept_header.state.catch_arms.len());

    // The exit check still reads the transfer the widened node kept: releasing
    // the aggregate it named carries the payload away, releasing the other one
    // leaves it leaked, and the owner-free header keeps leaking it either way.
    var owned_exit = try widened.state.clone(allocator);
    defer owned_exit.deinit();
    try owned_exit.trackEscapeOwned(out);
    try owned_exit.trackLeaks();
    try testing.expectEqual(@as(usize, 0), owned_exit.getStoreViolations().len);

    var other_aggregate = try widened.state.clone(allocator);
    defer other_aggregate.deinit();
    try other_aggregate.trackEscapeOwned(other_out);
    try other_aggregate.trackLeaks();
    try testing.expectEqual(@as(usize, 1), other_aggregate.getStoreViolations().len);
    try testing.expectEqual(store_mod.StoreViolationKind.resource_leak, other_aggregate.getStoreViolations()[0].kind);
    try testing.expectEqual(bytes, other_aggregate.getStoreViolations()[0].region);

    var header_exit = try kept_header.state.clone(allocator);
    defer header_exit.deinit();
    try header_exit.trackEscapeOwned(out);
    try header_exit.trackLeaks();
    try testing.expectEqual(@as(usize, 1), header_exit.getStoreViolations().len);
    try testing.expectEqual(store_mod.StoreViolationKind.resource_leak, header_exit.getStoreViolations()[0].kind);
    try testing.expectEqual(bytes, header_exit.getStoreViolations()[0].region);
}
