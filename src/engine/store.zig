const std = @import("std");
const builtin = @import("builtin");
const compat = @import("../compat.zig");
const ast_walk = @import("../ast_walk.zig");
const ids = @import("../ids.zig");

const VarId = ids.VarId;

pub const ResourceState = enum {
    unknown,
    allocated,
    freed,
    non_allocated,
    open,
    closed,
};

/// True for the states that mean "the program still holds this resource".
/// These are the states the leak check is derived from, which makes them the
/// ones a wider state must not absorb.
fn isHeldResource(state: ResourceState) bool {
    return state == .allocated or state == .open;
}

pub const StoreViolationKind = enum {
    double_free,
    free_without_alloc,
    double_close,
    close_without_open,
    use_after_free,
    use_after_close,
    resource_leak,
    /// A resource with a queued deferred free was passed into a container
    /// declared in a scope that outlives the defer. When the defer fires
    /// at block exit the container is left holding a freed slice.
    defer_frees_escapee,
};

const DeferredAction = enum {
    free,
    close,
    free_owned,
};

const DeferredEntry = struct {
    action: DeferredAction,
    /// AST node of the lexical block that owns the defer. When that block
    /// exits the action fires; this is what makes "container outlives defer"
    /// decidable at the moment of escape.
    scope_node: ?u32,
    /// The binding this schedule was written for. Entries are recorded per
    /// canonical region, so without this a store into the binding cannot tell
    /// the schedule it owns from one a saved alias owns, and would hand the
    /// binding's own release to that alias.
    binding: VarId,
};

fn deferredEntryEql(lhs: DeferredEntry, rhs: DeferredEntry) bool {
    return lhs.action == rhs.action and
        lhs.scope_node == rhs.scope_node and
        lhs.binding == rhs.binding;
}

const ErrdeferAction = struct {
    action: DeferredAction,
    call_token: ?u32,
    scope_node: ?u32,
    /// The binding this schedule was written for, for the same reason a
    /// `defer` records it.
    binding: VarId,
};

fn errdeferActionEql(lhs: ErrdeferAction, rhs: ErrdeferAction) bool {
    return lhs.action == rhs.action and
        lhs.call_token == rhs.call_token and
        lhs.scope_node == rhs.scope_node and
        lhs.binding == rhs.binding;
}

pub const StoreViolation = struct {
    region: VarId,
    kind: StoreViolationKind,
    call_token: ?u32,

    pub fn eql(self: StoreViolation, other: StoreViolation) bool {
        return self.region == other.region and self.kind == other.kind and self.call_token == other.call_token;
    }

    pub fn hash(self: StoreViolation) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const region_index = ids.varIndex(self.region);
        const kind: u8 = @intFromEnum(self.kind);
        hasher.update(std.mem.asBytes(&region_index));
        hasher.update(std.mem.asBytes(&kind));
        const has_token: u8 = if (self.call_token) |_| 1 else 0;
        hasher.update(std.mem.asBytes(&has_token));
        if (self.call_token) |token| {
            hasher.update(std.mem.asBytes(&token));
        }
        return hasher.final();
    }
};

/// What a store into a binding hands it.
///
/// The engine settles this from the right-hand side before the old value is
/// released, because a binding only loses what it held once the store puts
/// something else in it, and a resize of the very block the binding already
/// holds releases that block rather than losing it.
pub const BindingReplacement = union(enum) {
    /// The binding is handed a resource of its own.
    different,
    /// The binding keeps the resource this region names.
    same_resource: VarId,
    /// The right-hand side is a resize that consumed this block.
    realloc_source: VarId,
};

/// The schedules a store into a binding took out of it, handed back once the
/// value it stores is in place.
///
/// A schedule belongs to the binding that wrote it: its body re-reads that
/// binding when the block exits, so it releases whatever the binding holds
/// next. Taking it out is what keeps a store from crediting the value the
/// binding already held, and handing it back is what keeps the new value
/// released.
pub const BindingReleases = struct {
    /// The `defer` queued for the overwritten binding itself.
    deferred: ?DeferredEntry = null,
    /// The `errdefer` queued for the overwritten binding itself.
    errdeferred: ?ErrdeferAction = null,

    /// Nothing was taken out.
    pub const empty: BindingReleases = .{};
};

/// A resource a binding handed to an owner that outlives the store into it.
///
/// The binding no longer names the block, but the transfer really happened and
/// whoever received it may still return or release it, so the acquisition stays
/// on record until that owner settles instead of being reported lost at once.
/// One entry per whole tuple bounds a binding that is overwritten repeatedly:
/// the same allocation site cannot pile up duplicate obligations.
pub const OwnedResource = struct {
    /// The canonical region the block had when the binding was overwritten.
    /// This stays the region that acquired it: a leak is reported where the
    /// acquisition happened, not wherever the resource moved afterwards.
    origin: VarId,
    /// The state it was left in. Only a held state is an outstanding
    /// acquisition.
    state: ResourceState,
    /// The owner that actually received it.
    owner: VarId,

    pub fn eql(self: OwnedResource, other: OwnedResource) bool {
        return self.origin == other.origin and
            self.state == other.state and
            self.owner == other.owner;
    }

    /// Hashed field by field: the tuple carries padding, and hashing its raw
    /// bytes would hash whatever that padding happened to hold.
    pub fn hash(self: OwnedResource) u64 {
        var hasher = std.hash.Wyhash.init(0);
        const origin = ids.varIndex(self.origin);
        const owner = ids.varIndex(self.owner);
        const state: u8 = @intFromEnum(self.state);
        hasher.update(std.mem.asBytes(&origin));
        hasher.update(std.mem.asBytes(&owner));
        hasher.update(std.mem.asBytes(&state));
        return hasher.final();
    }
};

/// Outstanding obligations, keyed by the whole tuple.
const retained_map = switch (compat.frontend) {
    .zig_0_15 => std.ArrayHashMapUnmanaged(OwnedResource, void, OwnedResourceContext, true),
    .zig_0_16 => std.array_hash_map.Custom(OwnedResource, void, OwnedResourceContext, true),
};

const OwnedResourceContext = struct {
    pub fn hash(_: @This(), obligation: OwnedResource) u32 {
        return @truncate(obligation.hash());
    }

    pub fn eql(_: @This(), lhs: OwnedResource, rhs: OwnedResource, _: usize) bool {
        return lhs.eql(rhs);
    }
};

/// Insertion-ordered set. Shared histories are immutable until a writer detaches.
/// Like the enclosing Store, each history and its clones are thread-confined.
const ViolationSet = struct {
    shared: ?*Shared,

    const empty: ViolationSet = .{ .shared = null };
    const Map: type = switch (compat.frontend) {
        .zig_0_15 => std.ArrayHashMapUnmanaged(StoreViolation, void, Context, true),
        .zig_0_16 => std.array_hash_map.Custom(StoreViolation, void, Context, true),
    };
    const Context = struct {
        pub fn hash(_: @This(), violation: StoreViolation) u32 {
            return @truncate(violation.hash());
        }

        pub fn eql(_: @This(), lhs: StoreViolation, rhs: StoreViolation, _: usize) bool {
            return lhs.eql(rhs);
        }
    };
    const Shared = struct {
        allocator: std.mem.Allocator,
        entries: Map,
        references: u32,
        hash: u64,
    };

    fn deinit(self: *ViolationSet) void {
        if (self.shared) |shared| {
            std.debug.assert(shared.references > 0);
            shared.references -= 1;
            if (shared.references == 0) {
                const allocator = shared.allocator;
                shared.entries.deinit(allocator);
                allocator.destroy(shared);
            }
        }
        self.* = .empty;
    }

    fn clone(self: ViolationSet, allocator: std.mem.Allocator) std.mem.Allocator.Error!ViolationSet {
        const shared = self.shared orelse return .empty;
        std.debug.assert(shared.references > 0);
        if (sameAllocator(shared.allocator, allocator)) {
            if (shared.references < std.math.maxInt(u32)) {
                shared.references += 1;
                return self;
            }
        }
        // A saturated reference count takes the independent-copy path as well.
        return .{ .shared = try self.copyWithCapacity(allocator, self.count()) };
    }

    fn items(self: ViolationSet) []const StoreViolation {
        return if (self.shared) |shared| shared.entries.keys() else &.{};
    }

    fn count(self: ViolationSet) usize {
        return if (self.shared) |shared| shared.entries.count() else 0;
    }

    fn computeHash(self: ViolationSet) u64 {
        return if (self.shared) |shared| shared.hash else 0;
    }

    fn contains(self: ViolationSet, violation: StoreViolation) bool {
        return if (self.shared) |shared| shared.entries.contains(violation) else false;
    }

    fn containsAll(self: ViolationSet, other: ViolationSet) bool {
        if (self.shared == other.shared) return true;
        if (self.count() < other.count()) return false;
        for (other.items()) |violation| {
            if (!self.contains(violation)) return false;
        }
        return true;
    }

    fn eql(self: ViolationSet, other: ViolationSet) bool {
        if (self.shared == other.shared) return true;
        if (self.count() != other.count()) return false;
        if (self.computeHash() != other.computeHash()) return false;
        return self.containsAll(other);
    }

    fn insert(self: *ViolationSet, allocator: std.mem.Allocator, violation: StoreViolation) std.mem.Allocator.Error!void {
        if (self.contains(violation)) return;
        const new_count = std.math.add(usize, self.count(), 1) catch return error.OutOfMemory;
        const shared = try self.ensureUniqueCapacity(allocator, new_count);
        shared.entries.putAssumeCapacityNoClobber(violation, {});
        shared.hash ^= violation.hash();
    }

    fn merge(self: ViolationSet, other: ViolationSet, allocator: std.mem.Allocator) std.mem.Allocator.Error!ViolationSet {
        if (self.shared == other.shared or other.count() == 0) return self.clone(allocator);
        if (self.count() == 0) return other.clone(allocator);

        var new_count = self.count();
        for (other.items()) |violation| {
            if (!self.contains(violation)) {
                new_count = std.math.add(usize, new_count, 1) catch return error.OutOfMemory;
            }
        }
        if (new_count == self.count()) return self.clone(allocator);

        const shared = try self.copyWithCapacity(allocator, new_count);
        for (other.items()) |violation| {
            if (!self.contains(violation)) {
                shared.entries.putAssumeCapacityNoClobber(violation, {});
                shared.hash ^= violation.hash();
            }
        }
        return .{ .shared = shared };
    }

    fn ensureUniqueCapacity(self: *ViolationSet, allocator: std.mem.Allocator, capacity: usize) std.mem.Allocator.Error!*Shared {
        if (self.shared) |shared| {
            std.debug.assert(shared.references > 0);
            if (shared.references == 1 and shared.entries.capacity() >= capacity) return shared;
        }
        // Build before publishing: even a failed index allocation keeps borrowed slices valid.
        const replacement = try self.copyWithCapacity(allocator, capacity);
        self.deinit();
        self.shared = replacement;
        return replacement;
    }

    fn copyWithCapacity(self: ViolationSet, allocator: std.mem.Allocator, capacity: usize) std.mem.Allocator.Error!*Shared {
        std.debug.assert(capacity >= self.count());
        std.debug.assert(capacity > 0);
        const shared = try allocator.create(Shared);
        shared.* = .{
            .allocator = allocator,
            .entries = .empty,
            .references = 1,
            .hash = self.computeHash(),
        };
        errdefer {
            shared.entries.deinit(allocator);
            allocator.destroy(shared);
        }
        try shared.entries.ensureTotalCapacity(allocator, capacity);
        for (self.items()) |violation| {
            shared.entries.putAssumeCapacityNoClobber(violation, {});
        }
        return shared;
    }

    fn sameAllocator(lhs: std.mem.Allocator, rhs: std.mem.Allocator) bool {
        if (lhs.vtable != rhs.vtable) return false;
        // Standard stateless allocators leave their context pointer undefined.
        const page_vtable = if (builtin.cpu.arch.isWasm())
            &std.heap.WasmAllocator.vtable
        else if (compat.frontend == .zig_0_15 and builtin.os.tag == .plan9)
            &std.heap.SbrkAllocator(std.os.plan9.sbrk).vtable
        else
            &std.heap.PageAllocator.vtable;
        if (lhs.vtable == page_vtable) return true;
        if (!builtin.single_threaded) {
            if (lhs.vtable == std.heap.smp_allocator.vtable) return true;
        }
        if (builtin.link_libc) {
            if (lhs.vtable == std.heap.c_allocator.vtable) return true;
            if (compat.frontend == .zig_0_15) {
                if (lhs.vtable == std.heap.raw_c_allocator.vtable) return true;
            }
        }
        if (compat.frontend == .zig_0_16 and builtin.single_threaded and
            (builtin.os.tag == .linux or builtin.cpu.arch.isWasm()))
        {
            if (lhs.vtable == std.heap.brk_allocator.vtable) return true;
        }
        return lhs.ptr == rhs.ptr;
    }
};

pub const Store = struct {
    resources: std.AutoHashMap(VarId, ResourceState),
    violations: ViolationSet,
    aliases: std.AutoHashMap(VarId, VarId),
    deferred: std.AutoHashMap(VarId, DeferredEntry),
    errdeferred: std.AutoHashMap(VarId, ErrdeferAction),
    owners: std.AutoHashMap(VarId, VarId),
    /// Acquisitions an overwritten binding handed to an owner that may still
    /// release them. Independent of the current resource states: the same
    /// origin may hold a new acquisition while an older one is still owed.
    retained: retained_map,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Store {
        return .{
            .resources = std.AutoHashMap(VarId, ResourceState).init(allocator),
            .violations = .empty,
            .aliases = std.AutoHashMap(VarId, VarId).init(allocator),
            .deferred = std.AutoHashMap(VarId, DeferredEntry).init(allocator),
            .errdeferred = std.AutoHashMap(VarId, ErrdeferAction).init(allocator),
            .owners = std.AutoHashMap(VarId, VarId).init(allocator),
            .retained = .empty,
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Store) void {
        self.resources.deinit();
        self.violations.deinit();
        self.aliases.deinit();
        self.deferred.deinit();
        self.errdeferred.deinit();
        self.owners.deinit();
        self.retained.deinit(self.allocator);
    }

    pub fn clone(self: *const Store, allocator: std.mem.Allocator) !Store {
        var new_store = Store.init(allocator);
        errdefer new_store.deinit();

        // The six value maps own no nested allocations. Copy each map without
        // repeated insertion and growth. Violations keep their existing
        // reference-counted copy-on-write policy.
        new_store.resources = try self.resources.cloneWithAllocator(allocator);
        new_store.violations = try self.violations.clone(allocator);
        new_store.aliases = try self.aliases.cloneWithAllocator(allocator);
        new_store.deferred = try self.deferred.cloneWithAllocator(allocator);
        new_store.errdeferred = try self.errdeferred.cloneWithAllocator(allocator);
        new_store.owners = try self.owners.cloneWithAllocator(allocator);
        new_store.retained = try self.retained.clone(allocator);

        return new_store;
    }

    pub fn eql(self: *const Store, other: *const Store) bool {
        if (self.resources.count() != other.resources.count()) return false;
        var iter = self.resources.iterator();
        while (iter.next()) |entry| {
            if (other.resources.get(entry.key_ptr.*)) |other_state| {
                if (entry.value_ptr.* != other_state) return false;
            } else {
                return false;
            }
        }

        if (!self.violations.eql(other.violations)) return false;

        if (self.aliases.count() != other.aliases.count()) return false;
        var alias_iter = self.aliases.iterator();
        while (alias_iter.next()) |entry| {
            if (other.aliases.get(entry.key_ptr.*)) |other_target| {
                if (entry.value_ptr.* != other_target) return false;
            } else {
                return false;
            }
        }

        if (self.deferred.count() != other.deferred.count()) return false;
        var deferred_iter = self.deferred.iterator();
        while (deferred_iter.next()) |entry| {
            if (other.deferred.get(entry.key_ptr.*)) |other_entry| {
                if (!deferredEntryEql(entry.value_ptr.*, other_entry)) return false;
            } else {
                return false;
            }
        }

        if (self.errdeferred.count() != other.errdeferred.count()) return false;
        var errdeferred_iter = self.errdeferred.iterator();
        while (errdeferred_iter.next()) |entry| {
            if (other.errdeferred.get(entry.key_ptr.*)) |other_action| {
                if (!errdeferActionEql(entry.value_ptr.*, other_action)) return false;
            } else {
                return false;
            }
        }

        return self.ownershipEql(other);
    }

    /// Executed ownership edges, compared without depending on map order.
    /// Absence is significant: that path never transferred the resource.
    ///
    /// Obligations a binding overwrite left behind are part of the same
    /// question: an acquisition still owed to an owner is an executed
    /// transfer, and dropping it invents a leak while keeping one on a path
    /// that never received it hides one.
    pub fn ownershipEql(self: *const Store, other: *const Store) bool {
        if (self.owners.count() != other.owners.count()) return false;
        var iter = self.owners.iterator();
        while (iter.next()) |entry| {
            const owner = other.owners.get(entry.key_ptr.*) orelse return false;
            if (entry.value_ptr.* != owner) return false;
        }

        if (self.retained.count() != other.retained.count()) return false;
        var obligations_iter = self.retained.iterator();
        while (obligations_iter.next()) |entry| {
            if (!other.retained.contains(entry.key_ptr.*)) return false;
        }
        return true;
    }

    /// Hash the stored edges as they stand, not re-canonicalized aliases,
    /// and the obligations an overwrite left behind with the owners that hold
    /// them. This is the ownership partition used at state convergence.
    pub fn ownershipHash(self: *const Store) u64 {
        var edges_hash: u64 = 0;
        var iter = self.owners.iterator();
        while (iter.next()) |entry| {
            var edge_hasher = std.hash.Wyhash.init(0);
            const resource = ids.varIndex(entry.key_ptr.*);
            const owner = ids.varIndex(entry.value_ptr.*);
            edge_hasher.update(std.mem.asBytes(&resource));
            edge_hasher.update(std.mem.asBytes(&owner));
            edges_hash ^= edge_hasher.final();
        }

        var obligations_hash: u64 = 0;
        var obligations_iter = self.retained.iterator();
        while (obligations_iter.next()) |entry| {
            obligations_hash ^= entry.key_ptr.*.hash();
        }

        var hasher = std.hash.Wyhash.init(0);
        const count = self.owners.count();
        const obligations = self.retained.count();
        hasher.update(std.mem.asBytes(&edges_hash));
        hasher.update(std.mem.asBytes(&obligations_hash));
        hasher.update(std.mem.asBytes(&count));
        hasher.update(std.mem.asBytes(&obligations));
        return hasher.final();
    }

    pub fn computeHash(self: *const Store) u64 {
        var resources_hash: u64 = 0;

        var iter = self.resources.iterator();
        while (iter.next()) |entry| {
            var hasher = std.hash.Wyhash.init(0);
            const key = ids.varIndex(entry.key_ptr.*);
            hasher.update(std.mem.asBytes(&key));
            hasher.update(std.mem.asBytes(&entry.value_ptr.*));
            resources_hash ^= hasher.final();
        }

        const violations_hash = self.violations.computeHash();

        var aliases_hash: u64 = 0;
        var alias_iter = self.aliases.iterator();
        while (alias_iter.next()) |entry| {
            var hasher = std.hash.Wyhash.init(0);
            const key = ids.varIndex(entry.key_ptr.*);
            const value = ids.varIndex(entry.value_ptr.*);
            hasher.update(std.mem.asBytes(&key));
            hasher.update(std.mem.asBytes(&value));
            aliases_hash ^= hasher.final();
        }

        var deferred_hash: u64 = 0;
        var deferred_iter = self.deferred.iterator();
        while (deferred_iter.next()) |entry| {
            var hasher = std.hash.Wyhash.init(0);
            const key = ids.varIndex(entry.key_ptr.*);
            hasher.update(std.mem.asBytes(&key));
            const action = entry.value_ptr.*.action;
            hasher.update(std.mem.asBytes(&action));
            const has_scope: u8 = if (entry.value_ptr.*.scope_node) |_| 1 else 0;
            hasher.update(std.mem.asBytes(&has_scope));
            if (entry.value_ptr.*.scope_node) |scope| {
                hasher.update(std.mem.asBytes(&scope));
            }
            // Which binding the schedule was written for is part of what the
            // schedule is.
            const binding = ids.varIndex(entry.value_ptr.*.binding);
            hasher.update(std.mem.asBytes(&binding));
            deferred_hash ^= hasher.final();
        }

        var errdeferred_hash: u64 = 0;
        var errdeferred_iter = self.errdeferred.iterator();
        while (errdeferred_iter.next()) |entry| {
            var hasher = std.hash.Wyhash.init(0);
            const key = ids.varIndex(entry.key_ptr.*);
            const action = entry.value_ptr.*.action;
            const call_token = entry.value_ptr.*.call_token;
            const scope_node = entry.value_ptr.*.scope_node;
            const has_call_token: u8 = if (call_token) |_| 1 else 0;
            const has_scope_node: u8 = if (scope_node) |_| 1 else 0;
            hasher.update(std.mem.asBytes(&key));
            hasher.update(std.mem.asBytes(&action));
            hasher.update(std.mem.asBytes(&has_call_token));
            if (call_token) |token| {
                hasher.update(std.mem.asBytes(&token));
            }
            hasher.update(std.mem.asBytes(&has_scope_node));
            if (scope_node) |scope| {
                hasher.update(std.mem.asBytes(&scope));
            }
            const binding = ids.varIndex(entry.value_ptr.*.binding);
            hasher.update(std.mem.asBytes(&binding));
            errdeferred_hash ^= hasher.final();
        }

        const owners_hash = self.ownershipHash();

        var hasher = std.hash.Wyhash.init(0);
        const resources_count = self.resources.count();
        const violations_len = self.violations.count();
        hasher.update(std.mem.asBytes(&resources_hash));
        hasher.update(std.mem.asBytes(&violations_hash));
        hasher.update(std.mem.asBytes(&aliases_hash));
        hasher.update(std.mem.asBytes(&deferred_hash));
        hasher.update(std.mem.asBytes(&errdeferred_hash));
        hasher.update(std.mem.asBytes(&owners_hash));
        hasher.update(std.mem.asBytes(&resources_count));
        hasher.update(std.mem.asBytes(&violations_len));
        const aliases_count = self.aliases.count();
        const deferred_count = self.deferred.count();
        const errdeferred_count = self.errdeferred.count();
        hasher.update(std.mem.asBytes(&aliases_count));
        hasher.update(std.mem.asBytes(&deferred_count));
        hasher.update(std.mem.asBytes(&errdeferred_count));

        return hasher.final();
    }

    pub fn getState(self: *const Store, region: VarId) ?ResourceState {
        const root = self.canonical(region);
        return self.resources.get(root);
    }

    pub fn recordOwnership(self: *Store, resource: VarId, container: VarId) !void {
        const resource_root = self.canonical(resource);
        const container_root = self.canonical(container);
        if (resource_root == container_root) return;
        try self.owners.put(resource_root, container_root);
    }

    fn removeOwnershipFor(self: *Store, region: VarId) void {
        const root = self.canonical(region);
        _ = self.owners.remove(root);

        var iter = self.owners.iterator();
        while (iter.next()) |entry| {
            if (entry.value_ptr.* == root) {
                self.owners.removeByPtr(entry.key_ptr);
            }
        }
    }

    /// Escape every resource reachable from `container` through ownership.
    ///
    /// Ownership nests: an aggregate holds the payloads stored in it and a
    /// payload holds the resources of its own fields, so a container that
    /// leaves the function takes everything below it with it. Resources the
    /// container never owned stay exactly where they were.
    ///
    /// The closure is gathered before anything is mutated, so an allocation
    /// failure leaves the ownership graph exactly as it was. The collected
    /// list doubles as the traversal queue, and a container with no owned
    /// descendants allocates nothing at all.
    pub fn escapeOwned(self: *Store, container: VarId) std.mem.Allocator.Error!void {
        const container_root = self.canonical(container);
        var closure: std.ArrayList(VarId) = .empty;
        defer closure.deinit(self.allocator);

        // `closure` holds the visited set: index 0 starts at the container
        // itself, so seeding the walk costs no append.
        var depth: usize = 0;
        while (depth <= closure.items.len) : (depth += 1) {
            const current: VarId = if (depth == 0) container_root else closure.items[depth - 1];
            var iter = self.owners.iterator();
            while (iter.next()) |entry| {
                if (entry.value_ptr.* != current) continue;
                if (std.mem.indexOfScalar(VarId, closure.items, entry.key_ptr.*) != null) continue;
                try closure.append(self.allocator, entry.key_ptr.*);
            }
        }

        // Obligations the container owed leave with it: the owner that would
        // have released them escaped, so nothing holds them now. This covers
        // what it owes itself, which no edge in the ownership graph names.
        self.dropObligations(container_root, closure.items);

        for (closure.items) |resource| {
            self.escapeRegion(resource);
        }
    }

    /// Move ownership of everything `payload` owns onto `container`.
    ///
    /// Storing a container into an aggregate (`models[i] = model`) hands the
    /// payload's contents to that aggregate, so the resources the payload
    /// holds travel with it and belong to the aggregate from then on. Only
    /// resources that already name `payload` as their owner move: a plain
    /// value stored into an aggregate keeps its own ownership, so a genuine
    /// leak is still reported against the value that leaked it.
    pub fn adoptOwnedResources(self: *Store, payload: VarId, container: VarId) void {
        const payload_root = self.canonical(payload);
        const container_root = self.canonical(container);
        if (payload_root == container_root) return;
        var iter = self.owners.iterator();
        while (iter.next()) |entry| {
            if (entry.value_ptr.* == payload_root) entry.value_ptr.* = container_root;
        }

        // Obligations the payload owed move with the resources it hands over.
        self.reparentObligations(payload_root, container_root);
    }

    /// True when `container` owns at least one resource, counting the
    /// acquisitions it is still owed: a payload the binding holding it was
    /// overwritten away from is that owner's to release all the same, and the
    /// owner guarding an adoption has to see it.
    pub fn hasOwnedResources(self: *const Store, container: VarId) bool {
        const root = self.canonical(container);
        var iter = self.owners.iterator();
        while (iter.next()) |entry| {
            if (entry.value_ptr.* == root) return true;
        }
        var obligations_iter = self.retained.iterator();
        while (obligations_iter.next()) |entry| {
            if (entry.key_ptr.*.owner == root) return true;
        }
        return false;
    }

    pub fn markAllocated(self: *Store, region: VarId) !void {
        _ = self.aliases.remove(region);
        _ = self.deferred.remove(region);
        _ = self.errdeferred.remove(region);
        self.removeOwnershipFor(region);
        try self.resources.put(region, .allocated);
    }

    pub fn markOpened(self: *Store, region: VarId) !void {
        _ = self.aliases.remove(region);
        _ = self.deferred.remove(region);
        _ = self.errdeferred.remove(region);
        self.removeOwnershipFor(region);
        try self.resources.put(region, .open);
    }

    pub fn markNonAllocated(self: *Store, region: VarId) !void {
        _ = self.aliases.remove(region);
        _ = self.deferred.remove(region);
        _ = self.errdeferred.remove(region);
        self.removeOwnershipFor(region);
        try self.resources.put(region, .non_allocated);
    }

    /// Drop everything recorded for `region`, keeping what a saved alias still
    /// names: a store into one of several names for a value releases the name,
    /// not the value.
    pub fn resetRegion(self: *Store, region: VarId) void {
        if (self.aliases.get(region)) |_| {
            _ = self.aliases.remove(region);
            return;
        }
        self.removeOwnershipFor(region);
        const new_root = self.survivingAlias(region, region) orelse {
            _ = self.resources.remove(region);
            _ = self.deferred.remove(region);
            _ = self.errdeferred.remove(region);
            return;
        };

        self.carryResource(region, new_root);
        self.carryDeferred(region, new_root, region);
        self.carryErrdeferred(region, new_root, region);
        // The obligations the vacated region owed belong to the alias that
        // takes its place.
        self.reparentObligations(region, new_root);

        var update_iter = self.aliases.iterator();
        while (update_iter.next()) |entry| {
            if (entry.value_ptr.* == region) {
                entry.value_ptr.* = new_root;
            }
        }
        _ = self.aliases.remove(new_root);
    }

    pub fn escapeRegion(self: *Store, region: VarId) void {
        const root = self.canonical(region);
        self.removeOwnershipFor(root);
        _ = self.resources.remove(root);
        _ = self.deferred.remove(root);
        _ = self.errdeferred.remove(root);
        _ = self.aliases.remove(region);
    }

    pub fn escapeByName(self: *Store, tree: *const std.zig.Ast, name: []const u8) std.mem.Allocator.Error!void {
        var to_remove: std.ArrayList(VarId) = .empty;
        defer to_remove.deinit(self.allocator);

        const token_tags = tree.tokens.items(.tag);
        var iter = self.resources.iterator();
        while (iter.next()) |entry| {
            const token = ids.varIndex(entry.key_ptr.*);
            if (token >= token_tags.len or token_tags[token] != .identifier) continue;
            if (std.mem.eql(u8, tree.tokenSlice(token), name)) {
                try to_remove.append(self.allocator, entry.key_ptr.*);
            }
        }

        for (to_remove.items) |key| {
            _ = self.resources.remove(key);
            _ = self.deferred.remove(key);
            _ = self.errdeferred.remove(key);
            _ = self.aliases.remove(key);
            self.removeOwnershipFor(key);
        }
    }

    pub fn markFreed(self: *Store, region: VarId, call_token: ?u32) !void {
        const root = self.canonical(region);
        if (self.deferred.get(root)) |entry| {
            if (entry.action == .free) {
                try self.recordViolation(root, .double_free, call_token);
            }
        }
        if (self.resources.get(root)) |state| {
            switch (state) {
                .freed => try self.recordViolation(root, .double_free, call_token),
                .non_allocated => try self.recordViolation(root, .free_without_alloc, call_token),
                .open, .closed => try self.recordViolation(root, .free_without_alloc, call_token),
                .allocated => {},
                else => {},
            }
            try self.resources.put(root, .freed);
        } else {
            try self.resources.put(root, .freed);
        }
        _ = self.deferred.remove(root);
        self.removeOwnershipFor(root);
    }

    pub fn markClosed(self: *Store, region: VarId, call_token: ?u32) !void {
        const root = self.canonical(region);
        if (self.deferred.get(root)) |entry| {
            if (entry.action == .close) {
                try self.recordViolation(root, .double_close, call_token);
            }
        }
        if (self.resources.get(root)) |state| {
            switch (state) {
                .closed => try self.recordViolation(root, .double_close, call_token),
                .open => {},
                .non_allocated, .allocated, .freed => try self.recordViolation(root, .close_without_open, call_token),
                else => {},
            }
            try self.resources.put(root, .closed);
        } else {
            try self.resources.put(root, .closed);
        }
        _ = self.deferred.remove(root);
        self.removeOwnershipFor(root);
    }

    pub fn markUsed(self: *Store, region: VarId, call_token: ?u32) !void {
        const root = self.canonical(region);
        if (self.resources.get(root)) |state| {
            switch (state) {
                .freed => try self.recordViolation(root, .use_after_free, call_token),
                .closed => try self.recordViolation(root, .use_after_close, call_token),
                else => {},
            }
        }
    }

    pub fn markFreeOwned(self: *Store, container: VarId, call_token: ?u32) !void {
        const container_root = self.canonical(container);
        var owned: std.ArrayList(VarId) = .empty;
        defer owned.deinit(self.allocator);

        var iter = self.owners.iterator();
        while (iter.next()) |entry| {
            if (entry.value_ptr.* == container_root) {
                try owned.append(self.allocator, entry.key_ptr.*);
            }
        }

        for (owned.items) |resource| {
            try self.markFreed(resource, call_token);
        }
        // A retained obligation names the owner that received the overwritten
        // value. Freeing everything that owner holds settles those obligations
        // the same way an escape does: the block is gone, so nothing is owed.
        // This matches `escapeOwned`, which drops them when the owner leaves.
        self.dropObligations(container_root, null);
    }

    pub fn markDeferredFree(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.deferred.get(root)) |entry| {
            if (entry.action == .free) {
                try self.recordViolation(root, .double_free, call_token);
            }
        }
        if (self.resources.get(root)) |state| {
            if (state == .non_allocated) {
                try self.recordViolation(root, .free_without_alloc, call_token);
            }
        }
        try self.deferred.put(root, .{ .action = .free, .scope_node = scope_node, .binding = region });
    }

    pub fn markDeferredFreeOwned(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.deferred.get(root)) |entry| {
            if (entry.action == .free_owned) {
                try self.recordViolation(root, .double_free, call_token);
            }
        }
        try self.deferred.put(root, .{ .action = .free_owned, .scope_node = scope_node, .binding = region });
    }

    pub fn markDeferredClose(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.deferred.get(root)) |entry| {
            if (entry.action == .close) {
                try self.recordViolation(root, .double_close, call_token);
            }
        }
        if (self.resources.get(root)) |state| {
            if (state != .open) {
                try self.recordViolation(root, .close_without_open, call_token);
            }
        }
        try self.deferred.put(root, .{ .action = .close, .scope_node = scope_node, .binding = region });
    }

    pub fn markErrdeferredFree(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.errdeferred.get(root)) |action| {
            if (action.action == .free) {
                try self.recordViolation(root, .double_free, call_token);
            }
        }
        try self.errdeferred.put(root, .{ .action = .free, .call_token = call_token, .scope_node = scope_node, .binding = region });
    }

    pub fn markErrdeferredFreeOwned(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.errdeferred.get(root)) |action| {
            if (action.action == .free_owned) {
                try self.recordViolation(root, .double_free, call_token);
            }
        }
        try self.errdeferred.put(root, .{ .action = .free_owned, .call_token = call_token, .scope_node = scope_node, .binding = region });
    }

    pub fn markErrdeferredClose(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.errdeferred.get(root)) |action| {
            if (action.action == .close) {
                try self.recordViolation(root, .double_close, call_token);
            }
        }
        try self.errdeferred.put(root, .{ .action = .close, .call_token = call_token, .scope_node = scope_node, .binding = region });
    }

    pub fn applyErrdeferredReleases(self: *Store, return_node: u32, parent_map: []const u32) !void {
        var pending: std.ArrayList(struct {
            region: VarId,
            action: ErrdeferAction,
        }) = .empty;
        defer pending.deinit(self.allocator);

        var iter = self.errdeferred.iterator();
        while (iter.next()) |entry| {
            if (entry.value_ptr.*.scope_node) |scope_node| {
                if (!ast_walk.isAncestor(scope_node, return_node, parent_map)) {
                    continue;
                }
            }
            try pending.append(self.allocator, .{
                .region = entry.key_ptr.*,
                .action = entry.value_ptr.*,
            });
        }

        for (pending.items) |entry| {
            switch (entry.action.action) {
                .free => try self.markFreed(entry.region, entry.action.call_token),
                .free_owned => try self.markFreeOwned(entry.region, entry.action.call_token),
                .close => try self.markClosed(entry.region, entry.action.call_token),
            }
            _ = self.errdeferred.remove(entry.region);
        }
    }

    pub fn recordLeaks(self: *Store, error_path: bool) !void {
        var iter = self.resources.iterator();
        while (iter.next()) |entry| {
            switch (entry.value_ptr.*) {
                .allocated => {
                    if (self.deferred.get(entry.key_ptr.*)) |deferred_entry| {
                        if (deferred_entry.action == .free) continue;
                    }
                    if (self.ownerHasDeferredFreeOwned(entry.key_ptr.*, error_path)) {
                        continue;
                    }
                    if (error_path) {
                        if (self.errdeferred.get(entry.key_ptr.*)) |action| {
                            if (action.action == .free) continue;
                        }
                    }
                    try self.recordViolation(entry.key_ptr.*, .resource_leak, ids.varIndex(entry.key_ptr.*));
                },
                .open => {
                    if (self.deferred.get(entry.key_ptr.*)) |deferred_entry| {
                        if (deferred_entry.action == .close) continue;
                    }
                    if (self.ownerHasDeferredFreeOwned(entry.key_ptr.*, error_path)) {
                        continue;
                    }
                    if (error_path) {
                        if (self.errdeferred.get(entry.key_ptr.*)) |action| {
                            if (action.action == .close) continue;
                        }
                    }
                    try self.recordViolation(entry.key_ptr.*, .resource_leak, ids.varIndex(entry.key_ptr.*));
                },
                else => {},
            }
        }

        // Obligations a binding overwrite handed to an owner that may still
        // release them: the same question as a live resource, asked about the
        // owner that will eventually settle them.
        var obligations_iter = self.retained.iterator();
        while (obligations_iter.next()) |entry| {
            const obligation = entry.key_ptr.*;
            if (self.ownerHasScheduledRelease(obligation.owner, error_path)) continue;
            try self.recordViolation(obligation.origin, .resource_leak, ids.varIndex(obligation.origin));
        }
    }

    /// True when the owner of `region` has a queued cleanup that releases
    /// everything it owns.
    fn ownerHasDeferredFreeOwned(self: *const Store, region: VarId, error_path: bool) bool {
        const root = self.canonical(region);
        const owner = self.owners.get(root) orelse return false;
        return self.ownerHasScheduledRelease(owner, error_path);
    }

    /// True when `owner` itself has a queued cleanup that releases everything
    /// it owns.
    ///
    /// This asks about the owner named, not about whatever owns it: an
    /// acquisition already handed over is owed to that owner, so its own queue
    /// is the one that settles it.
    fn ownerHasScheduledRelease(self: *const Store, owner: VarId, error_path: bool) bool {
        if (self.deferred.get(owner)) |entry| {
            if (entry.action == .free_owned) return true;
        }
        if (error_path) {
            if (self.errdeferred.get(owner)) |action| {
                if (action.action == .free_owned) return true;
            }
        }
        return false;
    }

    pub fn violationCount(self: *const Store) usize {
        return self.violations.count();
    }

    /// Borrowed insertion-order view; valid until violations change or this Store is deinitialized.
    pub fn getViolations(self: *const Store) []const StoreViolation {
        return self.violations.items();
    }

    /// Return the AST node of the lexical scope owning the pending defer-free
    /// for `region`, if any is queued and the scope was recorded.
    pub fn pendingDeferredFreeScope(self: *const Store, region: VarId) ?u32 {
        const root = self.canonical(region);
        const entry = self.deferred.get(root) orelse return null;
        if (entry.action != .free and entry.action != .free_owned) return null;
        return entry.scope_node;
    }

    /// Record that `resource` was just appended into a container declared in a
    /// scope that outlives the defer-free queued on `resource`. The defer will
    /// fire at block exit, leaving the container holding a dangling slice.
    pub fn recordDeferFreesEscapee(self: *Store, resource: VarId, call_token: ?u32) !void {
        const root = self.canonical(resource);
        try self.recordViolation(root, .defer_frees_escapee, call_token);
    }

    fn recordViolation(self: *Store, region: VarId, kind: StoreViolationKind, call_token: ?u32) !void {
        const violation = StoreViolation{
            .region = region,
            .kind = kind,
            .call_token = call_token,
        };
        try self.violations.insert(self.allocator, violation);
    }

    fn canonical(self: *const Store, region: VarId) VarId {
        var current = region;
        var next_opt = self.aliases.get(current);
        while (next_opt) |next| : (next_opt = self.aliases.get(current)) {
            if (next == current) break;
            current = next;
        }
        return current;
    }

    pub fn aliasRegion(self: *Store, alias: VarId, target: VarId) !void {
        const root = self.canonical(target);
        try self.aliases.put(alias, root);
        _ = self.resources.remove(alias);
        _ = self.deferred.remove(alias);
        _ = self.errdeferred.remove(alias);
        _ = self.owners.remove(alias);
    }

    /// True when two bindings name the same resource, directly or through a
    /// saved alias.
    pub fn sameResource(self: *const Store, lhs: VarId, rhs: VarId) bool {
        return self.canonical(lhs) == self.canonical(rhs);
    }

    /// Account for the value a store into `region` takes away.
    ///
    /// A binding does not lose what it holds the moment it is written to: it
    /// loses it once nothing names it and no owner holds it. That is what this
    /// decides, for every kind of value:
    ///
    /// - A value nothing else names is lost at once. A schedule of its own
    ///   settles it; the schedule the binding itself queued does not, because
    ///   its body re-reads the binding and fires on what lands there next.
    /// - A value an owner received is that owner's to release, so it stays on
    ///   record as an obligation until the owner settles it.
    /// - A value a saved alias still names keeps its state, its schedules and
    ///   the transfers that were executed into it, under the alias that
    ///   survives.
    /// - A resize that consumed the slot's own block released it.
    ///
    /// What the old value owned follows the same question. An owner that
    /// outlived it still reaches those resources, so their transfers are
    /// reparented to it; with no such owner, only the edge into the container
    /// is dropped, leaving each resource to the binding it has of its own for
    /// the exit check to settle.
    ///
    /// The schedules the slot itself queued are taken out and returned, because
    /// the value leaving them behind is not one they release.
    /// `restoreBindingReleases` puts them back once the new value is in place.
    ///
    /// Every outcome is decided before anything changes, and the room for the
    /// violations and obligations is reserved before the first removal, so a
    /// failed call leaves the store exactly as it was.
    pub fn replaceRegionForBinding(self: *Store, region: VarId, replacement: BindingReplacement) !BindingReleases {
        const root = self.canonical(region);

        // A store that hands the binding back the resource it already holds
        // takes nothing away: there is no old value to account for, and no
        // schedule to hand back.
        const keeps_its_resource = switch (replacement) {
            .same_resource => |value| self.canonical(value) == root,
            .different, .realloc_source => false,
        };
        if (keeps_its_resource) return .empty;

        // A resize of the slot's own block freed it; that store is not losing a
        // resource the call already released.
        const consumed = switch (replacement) {
            .realloc_source => |value| self.canonical(value) == root,
            else => false,
        };

        // The schedules written for the slot itself come out first. They
        // belong to whatever lands in the binding next, so the value they were
        // queued for is not one they release.
        var releases: BindingReleases = .empty;
        if (self.deferred.get(root)) |entry| {
            if (entry.binding == region) releases.deferred = entry;
        }
        if (self.errdeferred.get(root)) |action| {
            if (action.binding == region) releases.errdeferred = action;
        }

        // The binding may be one of several names for a value that keeps its
        // own root; dropping that name loses nothing.
        const named_elsewhere = self.aliases.contains(region);
        const promoted: ?VarId = if (named_elsewhere) null else self.survivingAlias(root, region);

        // The owner that outlives what the binding is losing, if any. Its
        // resources stay reachable through it; a resize that freed the block
        // leaves nothing behind to reach them.
        const surviving_owner: ?VarId = if (consumed) null else (promoted orelse self.owners.get(root));

        var held: ?ResourceState = null;
        if (self.resources.get(root)) |state| {
            if (isHeldResource(state)) held = state;
        }

        // Everything below the value the binding is losing, gathered while the
        // ownership graph still says who holds what. An empty list costs
        // nothing: only a container that owns something reaches an append.
        var owned: std.ArrayList(VarId) = .empty;
        defer owned.deinit(self.allocator);
        if (promoted == null and !named_elsewhere) {
            var iter = self.owners.iterator();
            while (iter.next()) |entry| {
                const descendant = entry.key_ptr.*;
                if (descendant == root) continue;
                if (!self.ownedBelow(root, descendant)) continue;
                try owned.append(self.allocator, descendant);
            }
        }

        // Obligations the value owed as an owner, counted before anything
        // moves: with no owner left to release them, they are lost.
        var lost_obligations: usize = 0;
        if (!named_elsewhere and surviving_owner == null and self.retained.count() != 0) {
            var iter = self.retained.iterator();
            while (iter.next()) |entry| {
                if (entry.key_ptr.*.owner == root) lost_obligations += 1;
            }
        }

        // Room for the outcome, reserved before the first removal: past this
        // point nothing can fail.
        var new_violations: usize = lost_obligations;
        var new_obligations: usize = 0;
        if (!named_elsewhere and promoted == null and !consumed and held != null) {
            if (surviving_owner != null) new_obligations += 1 else new_violations += 1;
        }
        if (new_violations != 0) {
            _ = try self.violations.ensureUniqueCapacity(self.allocator, self.violations.count() + new_violations);
        }
        if (new_obligations != 0) {
            try self.retained.ensureUnusedCapacity(self.allocator, new_obligations);
        }

        // The value itself. A binding that was one of several names for a live
        // root is not losing that root, and none of this is about it.
        if (!named_elsewhere and promoted == null and !consumed) {
            if (held) |state| {
                if (surviving_owner) |owner| {
                    self.retained.putAssumeCapacity(.{ .origin = root, .state = state, .owner = owner }, {});
                } else {
                    try self.recordViolation(root, .resource_leak, ids.varIndex(root));
                }
            }
        }

        // What it owned: an owner that outlived it still reaches those
        // resources, and one that did not leaves each of them to the binding it
        // has of its own.
        for (owned.items) |descendant| {
            if (surviving_owner) |owner| {
                if (descendant != owner) self.owners.putAssumeCapacity(descendant, owner);
            } else {
                _ = self.owners.remove(descendant);
            }
        }

        // Obligations the value owed travel with whatever outlived it; when
        // nothing does, they are lost with it and reported where they were
        // acquired.
        if (!named_elsewhere and surviving_owner != null) {
            self.reparentObligations(root, surviving_owner.?);
        } else if (!named_elsewhere and lost_obligations != 0) {
            var index = self.retained.keys().len;
            while (index != 0) {
                index -= 1;
                const obligation = self.retained.keys()[index];
                if (obligation.owner != root) continue;
                self.retained.swapRemoveAt(index);
                try self.recordViolation(obligation.origin, .resource_leak, ids.varIndex(obligation.origin));
            }
        }

        // The binding stops naming the old value, and the schedules it owned
        // leave with it.
        _ = self.aliases.remove(region);
        if (releases.deferred != null) _ = self.deferred.remove(root);
        if (releases.errdeferred != null) _ = self.errdeferred.remove(root);

        if (promoted) |new_root| {
            self.promoteRoot(root, new_root, region);
        } else if (!named_elsewhere) {
            self.removeOwnershipFor(root);
            _ = self.resources.remove(root);
            _ = self.deferred.remove(root);
            _ = self.errdeferred.remove(root);
        }

        return releases;
    }

    /// Put the schedules a store into a binding took out back on that binding,
    /// once the value it stores is in place.
    ///
    /// The binding may have taken an alias in the meantime, so the schedules
    /// land on whatever region answers for it now while staying written for
    /// the binding itself.
    pub fn restoreBindingReleases(self: *Store, region: VarId, releases: BindingReleases) !void {
        if (releases.deferred == null and releases.errdeferred == null) return;
        const root = self.canonical(region);
        if (releases.deferred) |entry| {
            try self.deferred.put(root, .{
                .action = entry.action,
                .scope_node = entry.scope_node,
                .binding = region,
            });
        }
        if (releases.errdeferred) |action| {
            try self.errdeferred.put(root, .{
                .action = action.action,
                .call_token = action.call_token,
                .scope_node = action.scope_node,
                .binding = region,
            });
        }
    }

    /// The name the store still answers for `source` once `region` has been
    /// overwritten.
    ///
    /// A resize consumes the block it was given and stores the new one in the
    /// binding, so the name the source expression resolved to is not always the
    /// name that holds the block afterwards: an overwritten alias leaves the
    /// value under its root, and an overwritten root hands it to the saved
    /// alias that survives. This is what the consumed allocation is released
    /// under, asked before the write so it is read off the very state the
    /// write acts on.
    ///
    /// A source the write does not touch is that source. When the source is the
    /// overwritten name itself, the value lives under its root, under the saved
    /// alias that outlives it, or, with nothing else naming it, under no name at
    /// all - and then the name it had is the only one left to answer for it.
    ///
    /// Nothing here is written: the answer is read off the alias map alone, so
    /// asking costs no allocation and leaves the store as it was.
    pub fn reallocSourceAfterReplacement(self: *const Store, region: VarId, source: VarId) VarId {
        if (source != region) return source;
        const root = self.canonical(region);
        if (root != region) return root;
        return self.survivingAlias(root, region) orelse source;
    }

    /// The saved alias that still names `root` once `slot` stops naming it.
    /// The lowest index wins, so the same names always promote the same one.
    fn survivingAlias(self: *const Store, root: VarId, slot: VarId) ?VarId {
        var found: ?VarId = null;
        var iter = self.aliases.iterator();
        while (iter.next()) |entry| {
            if (entry.value_ptr.* != root or entry.key_ptr.* == slot) continue;
            const alias = entry.key_ptr.*;
            if (found) |current| {
                if (ids.varIndex(alias) < ids.varIndex(current)) found = alias;
            } else {
                found = alias;
            }
        }
        return found;
    }

    /// True when `region` sits below `root` in the executed ownership graph.
    fn ownedBelow(self: *const Store, root: VarId, region: VarId) bool {
        var current: ?VarId = self.owners.get(region);
        while (current) |container| {
            if (container == root) return true;
            if (container == region) return false;
            current = self.owners.get(container);
        }
        return false;
    }

    /// Drop every obligation `owner` is recorded as holding, along with every
    /// one whose owner sits in `closure` when a closure is given.
    ///
    /// The entries are walked from the end and swapped out where they stand:
    /// dropping one moves the map's last entry into its place, and a walk that
    /// only ever moves downwards never has to look at that entry again.
    fn dropObligations(self: *Store, owner: VarId, closure: ?[]const VarId) void {
        var index = self.retained.keys().len;
        while (index != 0) {
            index -= 1;
            const obligation = self.retained.keys()[index];
            var escaped = obligation.owner == owner;
            if (!escaped) {
                if (closure) |owned| {
                    escaped = std.mem.indexOfScalar(VarId, owned, obligation.owner) != null;
                }
            }
            if (escaped) self.retained.swapRemoveAt(index);
        }
    }

    /// Move every obligation `from` owes to `to`.
    ///
    /// The owner is part of the key, so a moved obligation is a new entry: it
    /// is swapped out and recorded again under its new owner, the same way.
    /// One that lands on a tuple already recorded merges with it instead of
    /// counting twice, so the set never grows and this needs no capacity of its
    /// own.
    fn reparentObligations(self: *Store, from: VarId, to: VarId) void {
        if (from == to) return;
        var index = self.retained.keys().len;
        while (index != 0) {
            index -= 1;
            var obligation = self.retained.keys()[index];
            if (obligation.owner != from) continue;
            self.retained.swapRemoveAt(index);
            obligation.owner = to;
            self.retained.putAssumeCapacity(obligation, {});
        }
    }

    /// Hand everything recorded under `root` to the saved alias that survives,
    /// so a value that is still named keeps its state, its schedules and the
    /// transfers that were executed into it.
    fn promoteRoot(self: *Store, root: VarId, new_root: VarId, slot: VarId) void {
        self.carryResource(root, new_root);
        self.carryDeferred(root, new_root, slot);
        self.carryErrdeferred(root, new_root, slot);

        // The container the transfers were executed into is the one that
        // survives, under its new name.
        if (self.owners.fetchRemove(root)) |entry| {
            _ = self.owners.remove(new_root);
            self.owners.putAssumeCapacity(new_root, entry.value);
        }
        var owners_iter = self.owners.iterator();
        while (owners_iter.next()) |entry| {
            if (entry.value_ptr.* == root) entry.value_ptr.* = new_root;
        }

        // Obligations the old container owed are owed by the one that is left.
        self.reparentObligations(root, new_root);

        var alias_iter = self.aliases.iterator();
        while (alias_iter.next()) |entry| {
            if (entry.value_ptr.* == root) entry.value_ptr.* = new_root;
        }
        _ = self.aliases.remove(new_root);
    }

    /// Move a value's state onto the alias that still names it.
    fn carryResource(self: *Store, root: VarId, new_root: VarId) void {
        const state = self.resources.get(root);
        _ = self.resources.remove(root);
        _ = self.resources.remove(new_root);
        if (state) |held| self.resources.putAssumeCapacity(new_root, held);
    }

    /// Move a saved binding's `defer` onto the alias that survives it.
    ///
    /// A schedule written for the binding being replaced is not one of them: it
    /// was taken out with the value it named, and the body it runs re-reads
    /// that binding.
    fn carryDeferred(self: *Store, root: VarId, new_root: VarId, slot: VarId) void {
        var carried: ?DeferredEntry = null;
        if (self.deferred.get(root)) |entry| {
            if (entry.binding != slot) carried = entry;
        }
        _ = self.deferred.remove(root);
        _ = self.deferred.remove(new_root);
        if (carried) |entry| self.deferred.putAssumeCapacity(new_root, entry);
    }

    /// Move a saved binding's `errdefer` onto the alias that survives it, on
    /// the same terms as a `defer`.
    fn carryErrdeferred(self: *Store, root: VarId, new_root: VarId, slot: VarId) void {
        var carried: ?ErrdeferAction = null;
        if (self.errdeferred.get(root)) |action| {
            if (action.binding != slot) carried = action;
        }
        _ = self.errdeferred.remove(root);
        _ = self.errdeferred.remove(new_root);
        if (carried) |action| self.errdeferred.putAssumeCapacity(new_root, action);
    }

    /// Widening operator for stores.
    /// Used at widening points to ensure convergence.
    /// - Resources: keep only if both agree, else set to `unknown`.
    /// - Aliases/owners/deferred/errdeferred/retained: keep only if both
    ///   agree, else drop.
    /// - Violations: union with dedup (never lose observed violations).
    pub fn widen(self: *const Store, other: *const Store, allocator: std.mem.Allocator) !Store {
        var result = Store.init(allocator);
        errdefer result.deinit();

        // Resources: keep if both agree, else set to unknown
        var self_res_iter = self.resources.iterator();
        while (self_res_iter.next()) |entry| {
            const region = entry.key_ptr.*;
            const self_state = entry.value_ptr.*;

            if (other.resources.get(region)) |other_state| {
                if (self_state == other_state) {
                    try result.resources.put(region, self_state);
                } else {
                    try result.resources.put(region, .unknown);
                }
            } else {
                // Region only in self: set to unknown
                try result.resources.put(region, .unknown);
            }
        }

        // Add resources only in other as unknown
        var other_res_iter = other.resources.iterator();
        while (other_res_iter.next()) |entry| {
            const region = entry.key_ptr.*;
            if (!self.resources.contains(region)) {
                try result.resources.put(region, .unknown);
            }
        }

        // Aliases: keep only if both agree
        var self_alias_iter = self.aliases.iterator();
        while (self_alias_iter.next()) |entry| {
            const alias = entry.key_ptr.*;
            const self_target = entry.value_ptr.*;

            if (other.aliases.get(alias)) |other_target| {
                if (self_target == other_target) {
                    try result.aliases.put(alias, self_target);
                }
            }
        }

        // Deferred: keep only if both agree
        var self_def_iter = self.deferred.iterator();
        while (self_def_iter.next()) |entry| {
            const region = entry.key_ptr.*;
            const self_entry = entry.value_ptr.*;

            if (other.deferred.get(region)) |other_entry| {
                if (deferredEntryEql(self_entry, other_entry)) {
                    try result.deferred.put(region, self_entry);
                }
            }
        }

        // Errdeferred: keep only if both agree
        var self_errdef_iter = self.errdeferred.iterator();
        while (self_errdef_iter.next()) |entry| {
            const region = entry.key_ptr.*;
            const self_action = entry.value_ptr.*;

            if (other.errdeferred.get(region)) |other_action| {
                if (errdeferActionEql(self_action, other_action)) {
                    try result.errdeferred.put(region, self_action);
                }
            }
        }

        // Owners: keep only if both agree
        var self_owners_iter = self.owners.iterator();
        while (self_owners_iter.next()) |entry| {
            const resource = entry.key_ptr.*;
            const self_owner = entry.value_ptr.*;

            if (other.owners.get(resource)) |other_owner| {
                if (self_owner == other_owner) {
                    try result.owners.put(resource, self_owner);
                }
            }
        }

        // Outstanding obligations: keep only if both agree. An obligation one
        // side has and the other lost would report a leak the wider store does
        // not know about, and dropping one both keep would hide it.
        var self_obligations_iter = self.retained.iterator();
        while (self_obligations_iter.next()) |entry| {
            const obligation = entry.key_ptr.*;
            if (other.retained.contains(obligation)) {
                try result.retained.put(allocator, obligation, {});
            }
        }

        result.violations = try self.violations.merge(other.violations, allocator);

        return result;
    }

    /// Returns true if `self` is at least as general as `other`.
    /// Missing entries in `self` are treated as unknown/no-info, except for
    /// resources that `other` is known to still hold. Leak reporting is derived
    /// from `.allocated` and `.open` alone, so neither absence nor `unknown` in
    /// `self` may stand in for them: absorbing a held resource drops the state
    /// that carries it and the leak goes with it.
    /// Ownership must match exactly: losing an executed transfer invents a
    /// leak, while keeping one on a path that never stored it hides a leak.
    pub fn subsumes(self: *const Store, other: *const Store) bool {
        var res_iter = self.resources.iterator();
        while (res_iter.next()) |entry| {
            const region = entry.key_ptr.*;
            const self_state = entry.value_ptr.*;
            const other_state = other.resources.get(region) orelse .unknown;
            if (self_state != .unknown and self_state != other_state) return false;
        }

        var held_iter = other.resources.iterator();
        while (held_iter.next()) |entry| {
            if (!isHeldResource(entry.value_ptr.*)) continue;
            const self_state = self.resources.get(entry.key_ptr.*) orelse return false;
            if (self_state != entry.value_ptr.*) return false;
        }

        var alias_iter = self.aliases.iterator();
        while (alias_iter.next()) |entry| {
            const alias = entry.key_ptr.*;
            const self_target = entry.value_ptr.*;
            const other_target = other.aliases.get(alias) orelse return false;
            if (self_target != other_target) return false;
        }

        var deferred_iter = self.deferred.iterator();
        while (deferred_iter.next()) |entry| {
            const region = entry.key_ptr.*;
            const self_entry = entry.value_ptr.*;
            const other_entry = other.deferred.get(region) orelse return false;
            if (!deferredEntryEql(self_entry, other_entry)) return false;
        }

        var errdeferred_iter = self.errdeferred.iterator();
        while (errdeferred_iter.next()) |entry| {
            const region = entry.key_ptr.*;
            const self_action = entry.value_ptr.*;
            const other_action = other.errdeferred.get(region) orelse return false;
            if (!errdeferActionEql(self_action, other_action)) return false;
        }

        if (!self.ownershipEql(other)) return false;

        return self.violations.containsAll(other.violations);
    }
};

test "Store tracks allocation/free transitions" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store = Store.init(allocator);
    defer store.deinit();

    const region = ids.varId(10);

    try store.markAllocated(region);
    try testing.expectEqual(ResourceState.allocated, store.getState(region).?);

    try store.markFreed(region, 1);
    try testing.expectEqual(ResourceState.freed, store.getState(region).?);
    try testing.expectEqual(@as(usize, 0), store.violationCount());
}

test "Store records double free violations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store = Store.init(allocator);
    defer store.deinit();

    const region = ids.varId(11);

    try store.markAllocated(region);
    try store.markFreed(region, 1);
    try store.markFreed(region, 2);

    try testing.expectEqual(ResourceState.freed, store.getState(region).?);
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.double_free, store.getViolations()[0].kind);
}

test "Store records free without alloc violations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store = Store.init(allocator);
    defer store.deinit();

    const region = ids.varId(13);

    try store.markNonAllocated(region);
    try store.markFreed(region, 1);

    try testing.expectEqual(ResourceState.freed, store.getState(region).?);
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.free_without_alloc, store.getViolations()[0].kind);
}

test "Store records close without open violations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store = Store.init(allocator);
    defer store.deinit();

    const region = ids.varId(14);

    try store.markNonAllocated(region);
    try store.markClosed(region, 1);

    try testing.expectEqual(ResourceState.closed, store.getState(region).?);
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.close_without_open, store.getViolations()[0].kind);
}

test "Store records use after free violations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store = Store.init(allocator);
    defer store.deinit();

    const region = ids.varId(15);

    try store.markAllocated(region);
    try store.markFreed(region, 1);
    try store.markUsed(region, 2);

    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.use_after_free, store.getViolations()[0].kind);
}

test "Store preserves alias state when resetting root" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store = Store.init(allocator);
    defer store.deinit();

    const root = ids.varId(21);
    const alias_a = ids.varId(22);
    const alias_b = ids.varId(23);

    try store.markAllocated(root);
    try store.aliasRegion(alias_a, root);
    try store.aliasRegion(alias_b, root);

    store.resetRegion(root);

    try testing.expectEqual(ResourceState.allocated, store.getState(alias_a).?);
    try testing.expectEqual(ResourceState.allocated, store.getState(alias_b).?);
    try testing.expect(store.getState(root) == null);
}

test "Store records leaks for allocated resources" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store = Store.init(allocator);
    defer store.deinit();

    const region = ids.varId(16);

    try store.markAllocated(region);
    try store.recordLeaks(false);

    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, store.getViolations()[0].kind);
}

test "Store hash accounts for repeated violations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store = Store.init(allocator);
    defer store.deinit();

    const region = ids.varId(12);

    try store.markAllocated(region);
    try store.markFreed(region, 1);
    try store.markFreed(region, 2);
    const hash_after_double = store.computeHash();

    try store.markFreed(region, 3);
    const hash_after_triple = store.computeHash();

    try testing.expect(hash_after_double != hash_after_triple);
}

test "Store widen resources agreement" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store1 = Store.init(allocator);
    defer store1.deinit();

    var store2 = Store.init(allocator);
    defer store2.deinit();

    const region1 = ids.varId(30);
    const region2 = ids.varId(31);
    const region3 = ids.varId(32);

    // Same state in both
    try store1.markAllocated(region1);
    try store2.markAllocated(region1);

    // Different states
    try store1.markAllocated(region2);
    try store2.markFreed(region2, 1);

    // Only in store1
    try store1.markOpened(region3);

    var widened = try store1.widen(&store2, allocator);
    defer widened.deinit();

    // region1: both agree -> allocated
    try testing.expectEqual(ResourceState.allocated, widened.getState(region1).?);

    // region2: disagree -> unknown
    try testing.expectEqual(ResourceState.unknown, widened.getState(region2).?);

    // region3: only in store1 -> unknown
    try testing.expectEqual(ResourceState.unknown, widened.getState(region3).?);
}

test "Store widen violations union" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store1 = Store.init(allocator);
    defer store1.deinit();

    var store2 = Store.init(allocator);
    defer store2.deinit();

    const region1 = ids.varId(40);
    const region2 = ids.varId(41);

    // Violation in store1
    try store1.markAllocated(region1);
    try store1.markFreed(region1, 1);
    try store1.markFreed(region1, 2); // double_free

    // Different violation in store2
    try store2.markAllocated(region2);
    try store2.markFreed(region2, 3);
    try store2.markUsed(region2, 4); // use_after_free

    try testing.expectEqual(@as(usize, 1), store1.violationCount());
    try testing.expectEqual(@as(usize, 1), store2.violationCount());

    var widened = try store1.widen(&store2, allocator);
    defer widened.deinit();

    // Both violations should be present
    try testing.expectEqual(@as(usize, 2), widened.violationCount());
}

test "Store widen aliases keep only agreement" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store1 = Store.init(allocator);
    defer store1.deinit();

    var store2 = Store.init(allocator);
    defer store2.deinit();

    const root1 = ids.varId(50);
    const root2 = ids.varId(51);
    const alias1 = ids.varId(52);
    const alias2 = ids.varId(53);

    // Same alias in both
    try store1.markAllocated(root1);
    try store2.markAllocated(root1);
    try store1.aliasRegion(alias1, root1);
    try store2.aliasRegion(alias1, root1);

    // Different alias targets
    try store1.markAllocated(root2);
    try store2.markAllocated(root2);
    try store1.aliasRegion(alias2, root1);
    try store2.aliasRegion(alias2, root2);

    var widened = try store1.widen(&store2, allocator);
    defer widened.deinit();

    // alias1 should be preserved (same target)
    try testing.expectEqual(root1, widened.aliases.get(alias1).?);

    // alias2 should be dropped (different targets)
    try testing.expect(widened.aliases.get(alias2) == null);
}

test "Store widen empty stores" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var store1 = Store.init(allocator);
    defer store1.deinit();

    var store2 = Store.init(allocator);
    defer store2.deinit();

    var widened = try store1.widen(&store2, allocator);
    defer widened.deinit();

    try testing.expectEqual(@as(usize, 0), widened.resources.count());
    try testing.expectEqual(@as(usize, 0), widened.aliases.count());
    try testing.expectEqual(@as(usize, 0), widened.violationCount());
}

test "Store subsumes preserves violations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var general = Store.init(allocator);
    defer general.deinit();

    var specific = Store.init(allocator);
    defer specific.deinit();

    const region = ids.varId(99);
    try specific.markAllocated(region);

    // A state that does not know about the allocation cannot stand in for one
    // that does: the leak is only ever reported from a held resource.
    try testing.expect(!general.subsumes(&specific));

    try specific.markFreed(region, 1);
    try specific.markFreed(region, 2);

    try testing.expect(!general.subsumes(&specific));

    try general.markAllocated(region);
    try general.markFreed(region, 1);
    try general.markFreed(region, 2);

    try testing.expect(general.subsumes(&specific));
}

test "Store subsumes keeps held resources on the more precise side" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const region = ids.varId(7);
    const other = ids.varId(8);

    // An unknown entry stands in for a released or never-taken resource, which
    // is the only reason a missing entry may stand in for anything at all.
    var released = Store.init(allocator);
    defer released.deinit();
    try released.markFreed(region, 1);
    var empty = Store.init(allocator);
    defer empty.deinit();
    try testing.expect(empty.subsumes(&released));

    // Widening is where `.unknown` resource states come from.
    var allocated = Store.init(allocator);
    defer allocated.deinit();
    try allocated.markAllocated(region);
    var never_allocated = Store.init(allocator);
    defer never_allocated.deinit();
    try never_allocated.markNonAllocated(region);
    var widened = try allocated.widen(&never_allocated, allocator);
    defer widened.deinit();
    try testing.expectEqual(ResourceState.unknown, widened.getState(region).?);
    var holding = Store.init(allocator);
    defer holding.deinit();
    try holding.markAllocated(region);

    // Neither absence nor `unknown` absorbs a resource that is still held.
    try testing.expect(!empty.subsumes(&holding));
    try testing.expect(!widened.subsumes(&holding));

    // The same holds for an open handle, the other state leaks are reported from.
    var opened = Store.init(allocator);
    defer opened.deinit();
    try opened.markOpened(region);
    try testing.expect(!empty.subsumes(&opened));
    try testing.expect(!widened.subsumes(&opened));

    // The held resource must match exactly: a different region is a leak.
    var other_region = Store.init(allocator);
    defer other_region.deinit();
    try other_region.markAllocated(other);
    try testing.expect(!other_region.subsumes(&holding));

    var matching = Store.init(allocator);
    defer matching.deinit();
    try matching.markAllocated(region);
    try testing.expect(matching.subsumes(&holding));
}

test "Store subsumption preserves executed ownership on both paths" {
    const testing = std.testing;
    const bytes = ids.varId(201);
    const out = ids.varId(202);
    const other_out = ids.varId(203);

    var unstored = Store.init(testing.allocator);
    defer unstored.deinit();
    try unstored.markAllocated(bytes);
    var stored = try unstored.clone(testing.allocator);
    defer stored.deinit();
    try stored.recordOwnership(bytes, out);

    try testing.expect(!unstored.subsumes(&stored));
    try testing.expect(!stored.subsumes(&unstored));

    var different_owner = try unstored.clone(testing.allocator);
    defer different_owner.deinit();
    try different_owner.recordOwnership(bytes, other_out);
    try testing.expect(!stored.subsumes(&different_owner));
    try testing.expect(!different_owner.subsumes(&stored));

    var same_owner = try stored.clone(testing.allocator);
    defer same_owner.deinit();
    try testing.expect(stored.subsumes(&same_owner));
    try testing.expect(same_owner.subsumes(&stored));

    // Joining a path that never stored the payload must not invent a transfer.
    var joined = try stored.widen(&unstored, testing.allocator);
    defer joined.deinit();
    try joined.escapeOwned(out);
    try joined.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), joined.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, joined.getViolations()[0].kind);
    try testing.expectEqual(bytes, joined.getViolations()[0].region);
}

test "Store violation clones isolate branches without allocating unchanged history" {
    const testing = std.testing;
    var failing = testing.FailingAllocator.init(testing.allocator, .{});
    const allocator = failing.allocator();
    var original = Store.init(allocator);
    defer original.deinit();
    for (0..64) |index| {
        try original.recordDeferFreesEscapee(ids.varId(@intCast(index)), @intCast(index));
    }
    const original_hash = original.computeHash();

    failing.fail_index = failing.alloc_index;
    failing.resize_fail_index = failing.resize_index;
    var branch = try original.clone(allocator);
    defer branch.deinit();
    var unchanged = try original.widen(&branch, allocator);
    defer unchanged.deinit();
    try branch.recordDeferFreesEscapee(ids.varId(0), 0);
    try testing.expect(original.eql(&branch));
    try testing.expectEqual(original_hash, branch.computeHash());
    try testing.expectError(error.OutOfMemory, branch.recordDeferFreesEscapee(ids.varId(64), 64));
    try testing.expect(original.eql(&branch));
    try testing.expectEqual(original_hash, branch.computeHash());

    failing.fail_index = std.math.maxInt(usize);
    failing.resize_fail_index = std.math.maxInt(usize);
    try branch.recordDeferFreesEscapee(ids.varId(64), 64);
    try original.recordDeferFreesEscapee(ids.varId(65), 65);
    try testing.expectEqual(@as(usize, 65), original.violationCount());
    try testing.expectEqual(@as(usize, 65), branch.violationCount());
    try testing.expect(!original.subsumes(&branch));
    try testing.expect(!branch.subsumes(&original));
    try testing.expectEqual(@as(usize, 64), unchanged.violationCount());
    try testing.expectEqual(original_hash, unchanged.computeHash());
}

test "Store violation clone copies when its reference count is saturated" {
    const testing = std.testing;
    var failing = testing.FailingAllocator.init(testing.allocator, .{});
    const allocator = failing.allocator();
    var original = Store.init(allocator);
    defer original.deinit();
    try original.recordDeferFreesEscapee(ids.varId(1), null);
    const shared = original.violations.shared orelse return error.TestUnexpectedResult;
    shared.references = std.math.maxInt(u32);
    defer shared.references = 1;

    failing.fail_index = failing.alloc_index;
    try testing.expectError(error.OutOfMemory, original.clone(allocator));
    try testing.expectEqual(std.math.maxInt(u32), shared.references);
    failing.fail_index = std.math.maxInt(usize);
    var cloned = try original.clone(allocator);
    defer cloned.deinit();
    try testing.expectEqual(std.math.maxInt(u32), shared.references);
    try testing.expect(original.eql(&cloned));
    try testing.expectEqual(original.computeHash(), cloned.computeHash());
    try cloned.recordDeferFreesEscapee(ids.varId(2), 0);
    try testing.expectEqual(@as(usize, 1), original.violationCount());
    try testing.expectEqual(@as(usize, 2), cloned.violationCount());
}

test "Store violation clones support a stateless allocator" {
    const testing = std.testing;
    const allocator = std.heap.page_allocator;
    var survivor = Store.init(allocator);
    defer survivor.deinit();
    {
        var source = Store.init(allocator);
        defer source.deinit();
        try source.recordDeferFreesEscapee(ids.varId(1), null);
        survivor = try source.clone(allocator);
    }
    try testing.expectEqual(@as(usize, 1), survivor.violationCount());
    try testing.expectEqualDeep(StoreViolation{
        .region = ids.varId(1),
        .kind = .defer_frees_escapee,
        .call_token = null,
    }, survivor.getViolations()[0]);
    try survivor.recordDeferFreesEscapee(ids.varId(2), 0);
    try testing.expectEqual(@as(usize, 2), survivor.violationCount());
}

test "Store violation storage survives either clone deinit order" {
    const testing = std.testing;
    var survivor = Store.init(testing.allocator);
    defer survivor.deinit();
    {
        var original = Store.init(testing.allocator);
        defer original.deinit();
        try original.recordDeferFreesEscapee(ids.varId(9), null);
        {
            var first = try original.clone(testing.allocator);
            defer first.deinit();
            survivor = try first.clone(testing.allocator);
        }
        try testing.expect(original.eql(&survivor));
    }
    try testing.expectEqual(@as(usize, 1), survivor.violationCount());
    try testing.expectEqualDeep(StoreViolation{
        .region = ids.varId(9),
        .kind = .defer_frees_escapee,
        .call_token = null,
    }, survivor.getViolations()[0]);
    try survivor.recordDeferFreesEscapee(ids.varId(10), 0);
    try testing.expectEqual(@as(usize, 2), survivor.violationCount());
}

test "Store violations distinguish every tuple and ignore insertion order" {
    const testing = std.testing;
    const violations = [_]StoreViolation{
        .{ .region = ids.varId(0), .kind = .double_free, .call_token = null },
        .{ .region = ids.varId(0), .kind = .double_free, .call_token = 0 },
        .{ .region = ids.varId(0), .kind = .double_free, .call_token = std.math.maxInt(u32) },
        .{ .region = ids.varId(0), .kind = .use_after_free, .call_token = 0 },
        .{ .region = ids.varId(std.math.maxInt(u32)), .kind = .double_free, .call_token = 0 },
    };
    var forward = Store.init(testing.allocator);
    defer forward.deinit();
    var reverse = Store.init(testing.allocator);
    defer reverse.deinit();
    for (violations, 0..) |violation, index| {
        try forward.recordViolation(violation.region, violation.kind, violation.call_token);
        const reversed = violations[violations.len - 1 - index];
        try reverse.recordViolation(reversed.region, reversed.kind, reversed.call_token);
    }
    for (violations) |violation| {
        try forward.recordViolation(violation.region, violation.kind, violation.call_token);
    }
    try testing.expectEqual(violations.len, forward.violationCount());
    try testing.expect(forward.eql(&reverse));
    try testing.expectEqual(forward.computeHash(), reverse.computeHash());
    try testing.expect(forward.subsumes(&reverse));
    try testing.expect(reverse.subsumes(&forward));
    var widened = try forward.widen(&reverse, testing.allocator);
    defer widened.deinit();
    try testing.expect(widened.eql(&forward));
    try testing.expectEqual(widened.computeHash(), forward.computeHash());
}

test "Store violation unions retain overlapping large histories" {
    const testing = std.testing;
    var left = Store.init(testing.allocator);
    defer left.deinit();
    var right = Store.init(testing.allocator);
    defer right.deinit();
    for (0..256) |index| {
        try left.recordDeferFreesEscapee(ids.varId(@intCast(index)), @intCast(index));
        const reversed: u32 = @intCast(383 - index);
        try right.recordDeferFreesEscapee(ids.varId(reversed), reversed);
    }
    var widened = try left.widen(&right, testing.allocator);
    defer widened.deinit();
    var reversed = try right.widen(&left, testing.allocator);
    defer reversed.deinit();
    try testing.expectEqual(@as(usize, 384), widened.violationCount());
    try testing.expect(widened.eql(&reversed));
    try testing.expectEqual(widened.computeHash(), reversed.computeHash());
    var observed = [_]bool{false} ** 384;
    for (widened.getViolations()) |violation| {
        const region = ids.varIndex(violation.region);
        try testing.expect(region < observed.len);
        try testing.expect(!observed[region]);
        try testing.expectEqual(StoreViolationKind.defer_frees_escapee, violation.kind);
        try testing.expectEqual(@as(?u32, region), violation.call_token);
        observed[region] = true;
    }
    for (observed) |present| try testing.expect(present);
    try testing.expect(widened.subsumes(&left));
    try testing.expect(widened.subsumes(&right));
    try testing.expect(!left.subsumes(&widened));
    try testing.expectEqual(@as(usize, 256), left.violationCount());
    try testing.expectEqual(@as(usize, 256), right.violationCount());
}

test "Store violation clones and unions outlive their source allocator" {
    const testing = std.testing;
    var destination = std.heap.ArenaAllocator.init(testing.allocator);
    defer destination.deinit();
    const allocator = destination.allocator();
    var cloned = Store.init(allocator);
    defer cloned.deinit();
    var widened = Store.init(allocator);
    defer widened.deinit();
    {
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        var source = Store.init(arena.allocator());
        defer source.deinit();
        for (0..64) |index| {
            try source.recordDeferFreesEscapee(ids.varId(@intCast(index)), @intCast(index));
        }
        cloned = try source.clone(allocator);
        widened = try source.widen(&source, allocator);
    }
    try testing.expect(cloned.eql(&widened));
    try testing.expectEqual(@as(usize, 64), cloned.violationCount());
    try testing.expectEqual(cloned.computeHash(), widened.computeHash());
    try cloned.recordDeferFreesEscapee(ids.varId(64), null);
    try widened.recordDeferFreesEscapee(ids.varId(65), 0);
    try testing.expect(!cloned.subsumes(&widened));
    try testing.expect(!widened.subsumes(&cloned));
}

test "Store violation changes preserve both inputs on allocation failure" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testViolationAllocationFailures, .{});
}

fn testViolationAllocationFailures(allocator: std.mem.Allocator) !void {
    const testing = std.testing;
    var source = Store.init(allocator);
    defer source.deinit();
    for (0..32) |index| {
        const previous_hash = source.computeHash();
        const previous_items = source.getViolations();
        source.recordDeferFreesEscapee(ids.varId(@intCast(index)), @intCast(index)) catch |err| {
            try testing.expectEqual(index, source.violationCount());
            try testing.expectEqual(previous_hash, source.computeHash());
            if (previous_items.len != 0) {
                try testing.expect(previous_items.ptr == source.getViolations().ptr);
                for (previous_items, 0..) |violation, expected| {
                    try testing.expectEqualDeep(StoreViolation{
                        .region = ids.varId(@intCast(expected)),
                        .kind = .defer_frees_escapee,
                        .call_token = @intCast(expected),
                    }, violation);
                }
            }
            return err;
        };
    }
    try source.aliasRegion(ids.varId(1000), ids.varId(0));
    const source_hash = source.computeHash();
    var branch = source.clone(allocator) catch |err| {
        try testing.expectEqual(source_hash, source.computeHash());
        try testing.expectEqual(@as(usize, 32), source.violationCount());
        return err;
    };
    defer branch.deinit();
    branch.recordDeferFreesEscapee(ids.varId(32), 32) catch |err| {
        try testing.expect(branch.eql(&source));
        try testing.expectEqual(@as(usize, 32), source.violationCount());
        try testing.expectEqual(@as(usize, 32), branch.violationCount());
        try testing.expectEqual(source_hash, source.computeHash());
        try testing.expectEqual(source_hash, branch.computeHash());
        return err;
    };
    try testing.expectEqual(@as(usize, 32), source.violationCount());
    try testing.expectEqual(source_hash, source.computeHash());
    try source.recordDeferFreesEscapee(ids.varId(33), 33);
    const before_union = source.computeHash();
    const branch_hash = branch.computeHash();
    var widened = source.widen(&branch, allocator) catch |err| {
        try testing.expectEqual(before_union, source.computeHash());
        try testing.expectEqual(branch_hash, branch.computeHash());
        try testing.expectEqual(@as(usize, 33), source.violationCount());
        try testing.expectEqual(@as(usize, 33), branch.violationCount());
        return err;
    };
    defer widened.deinit();
    try testing.expectEqual(@as(usize, 34), widened.violationCount());
    try testing.expect(widened.subsumes(&source));
    try testing.expect(widened.subsumes(&branch));
}

test "Store cross-allocator violation clone cleans up allocation failures" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testViolationCloneFailures, .{});
}

fn testViolationCloneFailures(allocator: std.mem.Allocator) !void {
    const testing = std.testing;
    var source = Store.init(testing.allocator);
    defer source.deinit();
    for (0..64) |index| {
        try source.recordDeferFreesEscapee(ids.varId(@intCast(index)), @intCast(index));
    }
    try source.aliasRegion(ids.varId(1000), ids.varId(0));
    const source_hash = source.computeHash();
    var cloned = source.clone(allocator) catch |err| {
        try testing.expectEqual(@as(usize, 64), source.violationCount());
        try testing.expectEqual(source_hash, source.computeHash());
        return err;
    };
    defer cloned.deinit();
    try testing.expect(source.eql(&cloned));
    try testing.expectEqual(source_hash, cloned.computeHash());
}

test "Store clone copies every map it owns and cleans up on allocation failure" {
    // HashMap.put can recover from failed growth when the key already exists.
    // Sweep clone allocations separately from those legitimate mutation paths.
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testStoreCloneFailures, .{false});
    try testStoreCloneFailures(std.testing.allocator, true);
}

fn testStoreCloneFailures(allocator: std.mem.Allocator, mutate_clone: bool) !void {
    const testing = std.testing;
    var source = Store.init(testing.allocator);
    defer source.deinit();

    // Populate all five value maps so the sweep reaches their clone allocations.
    try source.markAllocated(ids.varId(10));
    try source.markOpened(ids.varId(11));
    try source.aliasRegion(ids.varId(12), ids.varId(11));
    try source.markDeferredFree(ids.varId(10), 3, 4);
    try source.markErrdeferredFree(ids.varId(11), 5, 6);
    try source.recordOwnership(ids.varId(11), ids.varId(20));

    const source_hash = source.computeHash();
    var cloned = source.clone(allocator) catch |err| {
        // A failed clone leaves the source exactly as it was.
        try testing.expectEqual(source_hash, source.computeHash());
        try testing.expectEqual(ResourceState.allocated, source.getState(ids.varId(10)).?);
        return err;
    };
    defer cloned.deinit();

    try testing.expect(source.eql(&cloned));
    try testing.expectEqual(source_hash, cloned.computeHash());
    if (!mutate_clone) return;

    // Each copied map is independently mutable: a violation and a resource
    // transition recorded on the clone must not reach the source.
    try cloned.markFreed(ids.varId(10), 7);
    try cloned.markErrdeferredFree(ids.varId(11), 8, 9);
    try testing.expectEqual(ResourceState.freed, cloned.getState(ids.varId(10)).?);
    try testing.expectEqual(ResourceState.allocated, source.getState(ids.varId(10)).?);
    const expected_violations = [_]StoreViolation{
        .{ .region = ids.varId(10), .kind = .double_free, .call_token = 7 },
        .{ .region = ids.varId(11), .kind = .double_free, .call_token = 8 },
    };
    try testing.expectEqualDeep(@as([]const StoreViolation, &expected_violations), cloned.getViolations());
    try testing.expectEqual(@as(usize, 0), source.violationCount());
    try testing.expectEqual(source_hash, source.computeHash());
    try testing.expect(!source.eql(&cloned));
}

test "Store overwrite of a held binding reports the lost resource" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const held = ids.varId(300);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(held);
    // The slot queued nothing, so nothing has to be handed back.
    try testing.expectEqual(BindingReleases.empty, try store.replaceRegionForBinding(held, .different));

    // Whatever lands in the slot next is released in its own time.
    try store.markOpened(held);
    try store.markClosed(held, null);
    try store.recordLeaks(false);

    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, store.getViolations()[0].kind);
    try testing.expectEqual(held, store.getViolations()[0].region);
    try testing.expectEqual(@as(?u32, ids.varIndex(held)), store.getViolations()[0].call_token);
}

test "Store overwrite that keeps the same resource takes no schedule" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const held = ids.varId(301);
    const alias = ids.varId(302);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(held);
    try store.aliasRegion(alias, held);
    try testing.expect(store.sameResource(alias, held));

    // `x = x` hands the binding back what it already holds, under either name.
    var releases = try store.replaceRegionForBinding(held, .{ .same_resource = alias });
    try testing.expectEqual(BindingReleases.empty, releases);
    try store.restoreBindingReleases(held, releases);
    releases = try store.replaceRegionForBinding(alias, .{ .same_resource = held });
    try testing.expectEqual(BindingReleases.empty, releases);
    try testing.expectEqual(@as(usize, 1), store.aliases.count());
    try testing.expectEqual(@as(usize, 0), store.violationCount());

    // A schedule the binding already had stays where it is, and stays once.
    try store.markDeferredClose(held, 5, 6);
    releases = try store.replaceRegionForBinding(held, .{ .same_resource = held });
    try store.restoreBindingReleases(held, releases);
    try testing.expectEqual(@as(usize, 1), store.deferred.count());
    try testing.expectEqual(held, store.deferred.get(held).?.binding);

    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), store.violationCount());
    try testing.expectEqual(@as(usize, 0), store.retained.count());
}

test "Store overwrite promotes the alias that still names the old resource" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(304);
    const saved = ids.varId(305);
    const payload = ids.varId(306);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(slot);
    try store.aliasRegion(saved, slot);
    try store.markAllocated(payload);
    try store.recordOwnership(payload, slot);
    // The saved alias holds the handle and closes it in its own time.
    try store.markDeferredClose(saved, 7, 8);

    try testing.expectEqual(BindingReleases.empty, try store.replaceRegionForBinding(slot, .different));

    // The old handle survives under the alias that still names it, with the
    // transfer that was really executed into it.
    try testing.expectEqual(ResourceState.open, store.getState(saved).?);
    try testing.expect(store.getState(slot) == null);
    try testing.expectEqual(saved, store.owners.get(payload).?);
    try testing.expect(store.hasOwnedResources(saved));
    try testing.expectEqual(saved, store.deferred.get(saved).?.binding);

    // The old handle is released by the schedule the saved alias wrote.
    try store.markOpened(slot);
    try store.restoreBindingReleases(slot, .empty);
    try store.markClosed(slot, 10);
    try store.recordLeaks(false);
    // The payload the container owned is still allocated with no release
    // queued for it: the close settles the handle, not the bytes it owns.
    // The sibling test below pins the same outcome for a container whose
    // owner outlives it.
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, store.getViolations()[0].kind);
    try testing.expectEqual(payload, store.getViolations()[0].region);
}

test "Store overwrite does not lend the slot's schedule to the alias that survives" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(304);
    const saved = ids.varId(305);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(slot);
    try store.aliasRegion(saved, slot);
    // `defer close(slot)` re-reads the binding when it fires, so it belongs to
    // whatever lands in the slot next.
    try store.markDeferredClose(slot, 11, 12);

    const releases = try store.replaceRegionForBinding(slot, .different);
    try testing.expect(releases.deferred != null);
    try testing.expectEqual(slot, releases.deferred.?.binding);
    // It left the old root with the slot instead of being carried to the
    // alias that survived it.
    try testing.expect(store.deferred.get(saved) == null);
    try testing.expect(store.deferred.get(slot) == null);

    try store.markOpened(slot);
    try store.restoreBindingReleases(slot, releases);
    try testing.expectEqual(slot, store.deferred.get(slot).?.binding);

    try store.recordLeaks(false);
    // Only the handle the alias still names, and nothing closes it.
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, store.getViolations()[0].kind);
    try testing.expectEqual(saved, store.getViolations()[0].region);
}

test "Store overwrite keeps an owned resource until its owner releases it" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(307);
    const owner = ids.varId(308);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(slot);
    try store.recordOwnership(slot, owner);
    const releases = try store.replaceRegionForBinding(slot, .different);
    // The value that lands in the slot is released on its own schedule.
    try store.markAllocated(slot);
    try store.markDeferredFree(slot, 13, 14);
    try store.restoreBindingReleases(slot, releases);

    try testing.expectEqual(@as(usize, 1), store.retained.count());
    try testing.expectEqual(OwnedResource{ .origin = slot, .state = .allocated, .owner = owner }, store.retained.keys()[0]);
    try testing.expect(!store.owners.contains(slot));

    // An owner that hands the block back settles the obligation.
    var returned = try store.clone(allocator);
    defer returned.deinit();
    try returned.markFreeOwned(owner, 15);
    try testing.expectEqual(@as(usize, 0), returned.retained.count());
    try returned.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), returned.violationCount());

    // An owner that never releases it leaves exactly that one leak.
    var dropped = try store.clone(allocator);
    defer dropped.deinit();
    try dropped.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), dropped.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, dropped.getViolations()[0].kind);
    try testing.expectEqual(slot, dropped.getViolations()[0].region);

    // The slot leaving the frame takes what it holds now, not the acquisition
    // that shares its region and is still owed to the owner.
    var escaped_slot = try store.clone(allocator);
    defer escaped_slot.deinit();
    escaped_slot.escapeRegion(slot);
    try testing.expectEqual(@as(usize, 1), escaped_slot.retained.count());
    try escaped_slot.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), escaped_slot.violationCount());
    try testing.expectEqual(slot, escaped_slot.getViolations()[0].region);

    // An owner that leaves the frame takes the obligation with it.
    var escaped = try store.clone(allocator);
    defer escaped.deinit();
    try escaped.escapeOwned(owner);
    try testing.expectEqual(@as(usize, 0), escaped.retained.count());
    try escaped.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), escaped.violationCount());
}

test "Store overwrite loses the subtree of a container nothing else holds" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const container = ids.varId(309);
    const owned = ids.varId(310);
    const released = ids.varId(311);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(container);
    try store.markAllocated(owned);
    try store.recordOwnership(owned, container);
    // One payload is released in its own time and never leaks.
    try store.markAllocated(released);
    try store.recordOwnership(released, container);
    try store.markDeferredFree(released, 17, 18);

    try testing.expectEqual(BindingReleases.empty, try store.replaceRegionForBinding(container, .different));

    // The lost container is reported at once. Its payloads keep their own
    // bindings, so what happens to them is settled on their own terms.
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, store.getViolations()[0].kind);
    try testing.expectEqual(container, store.getViolations()[0].region);
    try testing.expectEqual(ResourceState.allocated, store.getState(owned).?);
    try testing.expectEqual(ResourceState.allocated, store.getState(released).?);
    try testing.expectEqual(@as(usize, 0), store.owners.count());
    try testing.expectEqual(@as(usize, 0), store.retained.count());

    try store.markOpened(container);
    try store.markClosed(container, 19);
    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 2), store.violationCount());
    try testing.expect(hasResourceLeak(&store, container));
    try testing.expect(hasResourceLeak(&store, owned));
    try testing.expect(!hasResourceLeak(&store, released));
}

test "Store overwrite hands a container's payloads to the owner that outlives it" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const container = ids.varId(312);
    const owned = ids.varId(313);
    const owner = ids.varId(314);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(container);
    try store.markAllocated(owned);
    try store.recordOwnership(owned, container);
    try store.recordOwnership(container, owner);

    const releases = try store.replaceRegionForBinding(container, .different);
    // The slot now holds a fresh block; the scenario releases it so the checks
    // below read only the old value's accounting, not the replacement's.
    try store.markOpened(container);
    try store.restoreBindingReleases(container, releases);
    try store.markClosed(container, 21);
    // The container the owner received is owed to it. Its payload stays
    // reachable through that same owner instead of becoming a second copy of
    // an acquisition whose own binding is still live.
    try testing.expectEqual(@as(usize, 1), store.retained.count());
    try testing.expectEqual(owner, store.owners.get(owned).?);
    try testing.expect(!store.owners.contains(container));

    var leaked = try store.clone(allocator);
    defer leaked.deinit();
    try leaked.recordLeaks(false);
    try testing.expectEqual(@as(usize, 2), leaked.violationCount());
    try testing.expect(hasResourceLeak(&leaked, container));
    try testing.expect(hasResourceLeak(&leaked, owned));

    var returned = try store.clone(allocator);
    defer returned.deinit();
    try returned.markFreeOwned(owner, 20);
    try returned.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), returned.violationCount());
    try testing.expectEqual(@as(usize, 0), returned.retained.count());
}

test "Store overwrite of a resized binding consumes the block it was given" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(315);
    const owner = ids.varId(316);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(slot);
    try store.recordOwnership(slot, owner);
    try store.markDeferredFree(slot, 21, 22);

    // `slot = realloc(slot, n)` freed the block the resize was handed.
    const releases = try store.replaceRegionForBinding(slot, .{ .realloc_source = slot });
    try testing.expect(releases.deferred != null);
    try testing.expectEqual(@as(usize, 0), store.retained.count());
    try testing.expectEqual(@as(usize, 0), store.violationCount());

    // The resized block is the slot's new value, and the schedule the slot's
    // own defer left behind is the one that releases it.
    try store.markAllocated(slot);
    try store.restoreBindingReleases(slot, releases);
    try testing.expectEqual(@as(usize, 1), store.deferred.count());
    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), store.violationCount());
}

test "Store overwrite credits no value the slot does not already hold" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(317);
    const other = ids.varId(318);
    const unrelated = ids.varId(319);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(slot);
    // A resize of some other block leaves this one lost.
    _ = try store.replaceRegionForBinding(slot, .{ .realloc_source = other });
    try store.markOpened(slot);
    try store.markClosed(slot, 14);
    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, store.getViolations()[0].kind);
    try testing.expectEqual(slot, store.getViolations()[0].region);

    // Naming a resource the slot never held is not naming the one it did.
    var named = Store.init(allocator);
    defer named.deinit();
    try named.markOpened(slot);
    _ = try named.replaceRegionForBinding(slot, .{ .same_resource = unrelated });
    try named.markOpened(slot);
    try named.markClosed(slot, 15);
    try named.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), named.violationCount());
    try testing.expectEqual(slot, named.getViolations()[0].region);
}

test "Store overwrite hands the slot's own defer and errdefer to the new value" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(320);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(slot);
    try store.markDeferredClose(slot, 24, 25);
    try store.markErrdeferredFree(slot, 26, 27);

    const releases = try store.replaceRegionForBinding(slot, .different);
    try testing.expect(releases.deferred != null);
    try testing.expect(releases.errdeferred != null);
    try testing.expectEqual(slot, releases.deferred.?.binding);
    try testing.expectEqual(slot, releases.errdeferred.?.binding);
    // The block exit re-reads the binding, so the schedule leaving with the
    // slot never releases the value the slot already held.
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(StoreViolationKind.resource_leak, store.getViolations()[0].kind);
    try testing.expectEqual(slot, store.getViolations()[0].region);

    try store.markOpened(slot);
    try store.restoreBindingReleases(slot, releases);
    try testing.expectEqual(slot, store.deferred.get(slot).?.binding);
    try testing.expectEqual(slot, store.errdeferred.get(slot).?.binding);

    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(slot, store.getViolations()[0].region);
}

test "Store retained obligations partition state like ownership edges" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const y = ids.varId(340);
    const z = ids.varId(341);
    const owner = ids.varId(342);
    const other_owner = ids.varId(343);

    var forward = Store.init(allocator);
    defer forward.deinit();
    var reverse = Store.init(allocator);
    defer reverse.deinit();

    try handToOwnerAndOverwrite(&forward, y, owner, .allocated);
    try handToOwnerAndOverwrite(&forward, z, owner, .open);
    try handToOwnerAndOverwrite(&reverse, z, owner, .open);
    try handToOwnerAndOverwrite(&reverse, y, owner, .allocated);

    try testing.expectEqual(@as(usize, 2), forward.retained.count());
    try testing.expect(forward.retained.contains(.{ .origin = y, .state = .allocated, .owner = owner }));
    try testing.expect(forward.retained.contains(.{ .origin = z, .state = .open, .owner = owner }));

    try testing.expect(forward.ownershipEql(&reverse));
    try testing.expectEqual(forward.ownershipHash(), reverse.ownershipHash());
    try testing.expectEqual(forward.computeHash(), reverse.computeHash());
    try testing.expect(forward.eql(&reverse));
    try testing.expect(forward.subsumes(&reverse));
    try testing.expect(reverse.subsumes(&forward));

    // The state the block was left in is part of the obligation.
    var swapped = Store.init(allocator);
    defer swapped.deinit();
    try handToOwnerAndOverwrite(&swapped, y, owner, .open);
    try handToOwnerAndOverwrite(&swapped, z, owner, .allocated);
    try testing.expect(forward.ownershipHash() != swapped.ownershipHash());
    try testing.expect(!forward.ownershipEql(&swapped));

    // A different owner is a different transfer, not a wider one.
    var reparented = try forward.clone(allocator);
    defer reparented.deinit();
    reparented.adoptOwnedResources(owner, other_owner);
    try testing.expect(!forward.ownershipEql(&reparented));
    try testing.expect(forward.ownershipHash() != reparented.ownershipHash());
    try testing.expect(!forward.subsumes(&reparented));
    try testing.expect(!reparented.subsumes(&forward));
    var narrowed = try forward.widen(&reparented, allocator);
    defer narrowed.deinit();
    try testing.expectEqual(@as(usize, 0), narrowed.retained.count());

    var same = try forward.clone(allocator);
    defer same.deinit();
    var joined = try forward.widen(&same, allocator);
    defer joined.deinit();
    try testing.expectEqual(@as(usize, 2), joined.retained.count());
    try testing.expect(joined.ownershipEql(&forward));
    try testing.expectEqual(joined.ownershipHash(), forward.ownershipHash());
    try testing.expectEqual(joined.computeHash(), forward.computeHash());
}

/// Allocate `region`, hand it to `owner`, and then overwrite the binding, so
/// what the owner was given outlives the binding that stored it.
fn handToOwnerAndOverwrite(store: *Store, region: VarId, owner: VarId, state: ResourceState) !void {
    switch (state) {
        .allocated => try store.markAllocated(region),
        .open => try store.markOpened(region),
        else => return error.TestUnexpectedResult,
    }
    try store.recordOwnership(region, owner);
    _ = try store.replaceRegionForBinding(region, .different);
    try store.markNonAllocated(region);
}

/// True when `region` is reported as a lost resource.
fn hasResourceLeak(store: *const Store, region: VarId) bool {
    for (store.getViolations()) |violation| {
        if (violation.kind == .resource_leak and violation.region == region) return true;
    }
    return false;
}

test "Store overwrite changes survive allocation failure" {
    try std.testing.checkAllAllocationFailures(std.testing.allocator, testOverwriteAllocationFailures, .{});
}

fn testOverwriteAllocationFailures(allocator: std.mem.Allocator) !void {
    const testing = std.testing;

    const container = ids.varId(350);
    const payload = ids.varId(351);
    const owner = ids.varId(352);
    const owned = ids.varId(353);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(container);
    try store.markAllocated(payload);
    try store.recordOwnership(payload, container);
    try store.markDeferredClose(container, 41, 42);

    const baseline_hash = store.computeHash();
    const baseline_items = store.getViolations();

    _ = store.replaceRegionForBinding(container, .different) catch |err| {
        // A failed overwrite leaves the store, and the violation view a caller
        // borrowed from it, exactly as they were.
        try testing.expectEqual(baseline_hash, store.computeHash());
        try testing.expectEqual(@as(usize, 0), store.violationCount());
        try testing.expect(baseline_items.ptr == store.getViolations().ptr);
        try testing.expectEqual(@as(usize, 1), store.owners.count());
        try testing.expectEqual(@as(usize, 0), store.retained.count());
        try testing.expectEqual(ResourceState.open, store.getState(container).?);
        return err;
    };

    // The lost container is reported once, its payload keeps its own binding.
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(container, store.getViolations()[0].region);
    try testing.expectEqual(@as(usize, 0), store.owners.count());
    try testing.expectEqual(@as(usize, 0), store.retained.count());

    // A binding whose value an owner still holds records an obligation.
    try store.markOpened(owned);
    try store.recordOwnership(owned, owner);
    const before_owned = store.computeHash();
    _ = store.replaceRegionForBinding(owned, .different) catch |err| {
        try testing.expectEqual(before_owned, store.computeHash());
        try testing.expectEqual(@as(usize, 0), store.retained.count());
        try testing.expectEqual(ResourceState.open, store.getState(owned).?);
        return err;
    };
    try testing.expectEqual(@as(usize, 1), store.retained.count());
}

test "Store overwrite of a saved name keeps the resource its root names" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const root = ids.varId(360);
    const alias = ids.varId(361);
    const owner = ids.varId(362);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(root);
    try store.aliasRegion(alias, root);
    try store.recordOwnership(root, owner);
    try store.markDeferredClose(alias, 30, 31);

    const releases = try store.replaceRegionForBinding(alias, .different);
    // The schedule the saved name wrote is the slot's own, so it comes back
    // for the name; the root keeps everything else.
    try testing.expect(releases.deferred != null);
    try testing.expectEqual(alias, releases.deferred.?.binding);
    try testing.expectEqual(ResourceState.open, store.getState(root).?);
    try testing.expectEqual(owner, store.owners.get(root).?);
    try testing.expectEqual(@as(usize, 0), store.aliases.count());
    try testing.expectEqual(@as(usize, 0), store.violationCount());
    try testing.expectEqual(@as(usize, 0), store.retained.count());

    // The schedule follows the name, not the value that left with it. The new
    // acquisition is tracked before the schedule is handed back - the order
    // `applyIdentifierStore` uses - so the open does not wipe what restore
    // puts back.
    try store.markOpened(alias);
    try store.restoreBindingReleases(alias, releases);
    try testing.expectEqual(alias, store.deferred.get(alias).?.binding);
    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(root, store.getViolations()[0].region);
}

test "Store overwrite detaches every resource below a large container" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const container = ids.varId(363);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markOpened(container);
    for (0..12) |index| {
        const payload = ids.varId(@intCast(400 + index));
        try store.markAllocated(payload);
        try store.recordOwnership(payload, container);
    }
    try testing.expectEqual(@as(usize, 12), store.owners.count());

    _ = try store.replaceRegionForBinding(container, .different);
    // Every payload keeps its own binding and loses only the container, so the
    // exit check is what settles them.
    try testing.expectEqual(@as(usize, 0), store.owners.count());
    try testing.expectEqual(@as(usize, 1), store.violationCount());
    try testing.expectEqual(container, store.getViolations()[0].region);

    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 13), store.violationCount());
}

test "Store moves every acquisition an owner holds, merging what collides" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const first = ids.varId(364);
    const second = ids.varId(365);
    const third = ids.varId(366);
    const owner = ids.varId(367);
    const other_owner = ids.varId(368);

    var store = Store.init(allocator);
    defer store.deinit();

    for ([_]VarId{ first, second, third }) |region| {
        try store.markAllocated(region);
        try store.recordOwnership(region, owner);
        _ = try store.replaceRegionForBinding(region, .different);
        try store.markNonAllocated(region);
    }
    try testing.expectEqual(@as(usize, 3), store.retained.count());

    // Handing an owner to itself moves nothing.
    store.adoptOwnedResources(owner, owner);
    try testing.expectEqual(@as(usize, 3), store.retained.count());

    // The same acquisition reaches a second owner, so the two records of it
    // are one record.
    try store.markAllocated(first);
    try store.recordOwnership(first, other_owner);
    _ = try store.replaceRegionForBinding(first, .different);
    try store.markNonAllocated(first);
    try testing.expectEqual(@as(usize, 4), store.retained.count());

    // Storing the first owner into the second moves all three, and the one
    // that lands on a tuple already recorded merges with it.
    store.adoptOwnedResources(owner, other_owner);
    try testing.expectEqual(@as(usize, 3), store.retained.count());
    try testing.expect(store.retained.contains(.{ .origin = first, .state = .allocated, .owner = other_owner }));
    try testing.expect(store.retained.contains(.{ .origin = second, .state = .allocated, .owner = other_owner }));
    try testing.expect(store.retained.contains(.{ .origin = third, .state = .allocated, .owner = other_owner }));

    // Freeing that owner settles every record it holds at once.
    try store.markFreeOwned(other_owner, 41);
    try testing.expectEqual(@as(usize, 0), store.retained.count());
    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), store.violationCount());
}

test "Store obligation is settled by its owner's own cleanup" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(369);
    const owner = ids.varId(370);
    const holder = ids.varId(371);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(slot);
    try store.recordOwnership(slot, owner);
    _ = try store.replaceRegionForBinding(slot, .different);
    try store.markNonAllocated(slot);
    try testing.expectEqual(@as(usize, 1), store.retained.count());

    // A queue that frees everything the owner owns settles the obligation.
    try store.markDeferredFreeOwned(owner, 32, 33);
    try store.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), store.violationCount());

    // An error path that only frees on the way out settles nothing on the
    // normal one.
    var error_path = try store.clone(allocator);
    defer error_path.deinit();
    _ = error_path.deferred.remove(owner);
    try error_path.markErrdeferredFreeOwned(owner, 34, 35);
    try error_path.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), error_path.violationCount());
    try testing.expectEqual(slot, error_path.getViolations()[0].region);

    // The cleanup has to be the owner's own: a queue on whatever owns the
    // owner is one level too far out.
    var nested = try store.clone(allocator);
    defer nested.deinit();
    _ = nested.deferred.remove(owner);
    try nested.recordOwnership(owner, holder);
    try nested.markDeferredFreeOwned(holder, 36, 37);
    try nested.recordLeaks(false);
    try testing.expectEqual(@as(usize, 1), nested.violationCount());
    try testing.expectEqual(slot, nested.getViolations()[0].region);
}

test "Store reports an owner that holds only an overwritten acquisition" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(372);
    const owner = ids.varId(373);
    const aggregate = ids.varId(374);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(slot);
    try store.recordOwnership(slot, owner);
    _ = try store.replaceRegionForBinding(slot, .different);
    try store.markNonAllocated(slot);

    // No active edge names the block any more: the owner holds only the
    // acquisition, which is what guards an adoption.
    try testing.expect(!store.owners.contains(slot));
    try testing.expect(store.hasOwnedResources(owner));

    var stored = try store.clone(allocator);
    defer stored.deinit();
    // The aggregate is a pure vessel here: adoption reads the ownership and
    // obligation maps, not a resource of its own, so opening one would only
    // add an unrelated handle the test never closes.
    stored.adoptOwnedResources(owner, aggregate);
    try testing.expectEqual(@as(usize, 1), stored.retained.count());
    try testing.expect(stored.retained.contains(.{ .origin = slot, .state = .allocated, .owner = aggregate }));
    try testing.expect(stored.hasOwnedResources(aggregate));

    // Freeing the aggregate settles what it was handed.
    try stored.markFreeOwned(aggregate, 38);
    try testing.expectEqual(@as(usize, 0), stored.retained.count());
    try stored.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), stored.violationCount());
}

test "Store realloc source query keeps a source the replacement does not touch" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(400);
    const saved = ids.varId(401);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(slot);
    try store.aliasRegion(saved, slot);

    // The write takes the slot's name, not the name the resize was handed:
    // a block another binding names is named by it still.
    try testing.expectEqual(saved, store.reallocSourceAfterReplacement(slot, saved));
}

test "Store realloc source query follows an overwritten root onto its saved alias" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const root = ids.varId(402);
    const first = ids.varId(403);
    const second = ids.varId(404);
    const elsewhere = ids.varId(405);
    const distractor = ids.varId(406);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(root);
    try store.markAllocated(elsewhere);
    // The names are saved out of order, and one of them names another block.
    try store.aliasRegion(second, root);
    try store.aliasRegion(first, root);
    try store.aliasRegion(distractor, elsewhere);

    const before = store.computeHash();
    // The lowest saved name is the one the overwrite promotes to root, and it
    // is the same one every time the question is asked.
    try testing.expectEqual(first, store.reallocSourceAfterReplacement(root, root));
    try testing.expectEqual(first, store.reallocSourceAfterReplacement(root, root));

    // Asking leaves the store exactly as it was.
    try testing.expectEqual(before, store.computeHash());
    try testing.expectEqual(@as(usize, 3), store.aliases.count());
}

test "Store realloc source query follows an overwritten alias onto its root" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(407);
    const root = ids.varId(408);
    const saved = ids.varId(409);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(root);
    try store.aliasRegion(slot, root);
    try store.aliasRegion(saved, root);

    // The overwritten name only ever named the block; the root holds it, so
    // the root is what the consumed allocation is released under.
    try testing.expectEqual(root, store.reallocSourceAfterReplacement(slot, slot));
}

test "Store realloc source query leaves a root nothing else names as the source" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const slot = ids.varId(410);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(slot);
    try store.markDeferredFree(slot, 40, 41);

    // No saved name outlives the write, so the source is the only name left to
    // answer for the block.
    try testing.expectEqual(slot, store.reallocSourceAfterReplacement(slot, slot));
}

test "Store realloc replacement frees the consumed block under the name that survives" {
    const testing = std.testing;
    const allocator = testing.allocator;

    const saved = ids.varId(411);
    const later = ids.varId(412);
    const slot = ids.varId(413);

    var store = Store.init(allocator);
    defer store.deinit();

    try store.markAllocated(slot);
    try store.aliasRegion(later, slot);
    try store.aliasRegion(saved, slot);
    // `defer free(slot)` re-reads the binding when it fires, so it belongs to
    // whatever lands in the slot next.
    try store.markDeferredFree(slot, 42, 43);

    // The resize was handed the root, but the overwrite hands that root to the
    // saved name that survives it.
    try testing.expectEqual(saved, store.reallocSourceAfterReplacement(slot, slot));

    const releases = try store.replaceRegionForBinding(slot, .{ .realloc_source = slot });
    try testing.expect(releases.deferred != null);
    try testing.expectEqual(slot, releases.deferred.?.binding);
    try testing.expectEqual(ResourceState.allocated, store.getState(saved).?);
    try testing.expectEqual(@as(usize, 0), store.violationCount());

    // The resize released the block it consumed, under the name that survived
    // the write and that every remaining name answers through.
    try store.markFreed(saved, 44);
    try testing.expectEqual(ResourceState.freed, store.getState(saved).?);
    try testing.expectEqual(ResourceState.freed, store.getState(later).?);
    try testing.expectEqual(@as(usize, 0), store.violationCount());

    // The block the resize returns lands in the slot, and the marker the
    // slot's own defer left behind is the release that settles it.
    try store.markAllocated(slot);
    try store.restoreBindingReleases(slot, releases);
    try testing.expectEqual(slot, store.deferred.get(slot).?.binding);
    try testing.expectEqual(@as(?u32, 43), store.pendingDeferredFreeScope(slot));
    try testing.expectEqual(ResourceState.allocated, store.getState(slot).?);

    try store.recordLeaks(false);
    // The old block was released under the name that held it, and the new one
    // is released by the slot's own marker: neither is left behind.
    try testing.expectEqual(@as(usize, 0), store.violationCount());
    try testing.expect(!hasResourceLeak(&store, saved));
    try testing.expect(!hasResourceLeak(&store, slot));

    // The same resize written through a saved name: the block is held by the
    // root, and overwriting the alias leaves the root alone.
    const root = ids.varId(414);
    const aliased = ids.varId(415);

    var named = Store.init(allocator);
    defer named.deinit();

    try named.markAllocated(root);
    try named.aliasRegion(aliased, root);
    try named.markDeferredFree(aliased, 45, 46);

    try testing.expectEqual(root, named.reallocSourceAfterReplacement(aliased, aliased));

    const aliased_releases = try named.replaceRegionForBinding(aliased, .{ .realloc_source = aliased });
    try testing.expect(aliased_releases.deferred != null);
    try testing.expectEqual(aliased, aliased_releases.deferred.?.binding);
    try testing.expectEqual(ResourceState.allocated, named.getState(root).?);
    try testing.expectEqual(@as(usize, 0), named.aliases.count());
    try testing.expectEqual(@as(usize, 0), named.violationCount());

    // The consumed block is released under the root that still holds it.
    try named.markFreed(root, 47);
    try testing.expectEqual(ResourceState.freed, named.getState(root).?);
    try testing.expectEqual(@as(usize, 0), named.violationCount());

    // The block the resize returns lands in the overwritten name, under the
    // marker its own defer left behind.
    try named.markAllocated(aliased);
    try named.restoreBindingReleases(aliased, aliased_releases);
    try testing.expectEqual(aliased, named.deferred.get(aliased).?.binding);
    try testing.expectEqual(@as(?u32, 46), named.pendingDeferredFreeScope(aliased));

    try named.recordLeaks(false);
    try testing.expectEqual(@as(usize, 0), named.violationCount());
    try testing.expect(!hasResourceLeak(&named, root));
    try testing.expect(!hasResourceLeak(&named, aliased));
}
