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
};

fn deferredEntryEql(lhs: DeferredEntry, rhs: DeferredEntry) bool {
    return lhs.action == rhs.action and lhs.scope_node == rhs.scope_node;
}

const ErrdeferAction = struct {
    action: DeferredAction,
    call_token: ?u32,
    scope_node: ?u32,
};

fn errdeferActionEql(lhs: ErrdeferAction, rhs: ErrdeferAction) bool {
    return lhs.action == rhs.action and
        lhs.call_token == rhs.call_token and
        lhs.scope_node == rhs.scope_node;
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
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Store {
        return .{
            .resources = std.AutoHashMap(VarId, ResourceState).init(allocator),
            .violations = .empty,
            .aliases = std.AutoHashMap(VarId, VarId).init(allocator),
            .deferred = std.AutoHashMap(VarId, DeferredEntry).init(allocator),
            .errdeferred = std.AutoHashMap(VarId, ErrdeferAction).init(allocator),
            .owners = std.AutoHashMap(VarId, VarId).init(allocator),
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
    }

    pub fn clone(self: *const Store, allocator: std.mem.Allocator) !Store {
        var new_store = Store.init(allocator);
        errdefer new_store.deinit();

        var iter = self.resources.iterator();
        while (iter.next()) |entry| {
            try new_store.resources.put(entry.key_ptr.*, entry.value_ptr.*);
        }

        new_store.violations = try self.violations.clone(allocator);

        var alias_iter = self.aliases.iterator();
        while (alias_iter.next()) |entry| {
            try new_store.aliases.put(entry.key_ptr.*, entry.value_ptr.*);
        }

        var deferred_iter = self.deferred.iterator();
        while (deferred_iter.next()) |entry| {
            try new_store.deferred.put(entry.key_ptr.*, entry.value_ptr.*);
        }

        var errdeferred_iter = self.errdeferred.iterator();
        while (errdeferred_iter.next()) |entry| {
            try new_store.errdeferred.put(entry.key_ptr.*, entry.value_ptr.*);
        }

        var owners_iter = self.owners.iterator();
        while (owners_iter.next()) |entry| {
            try new_store.owners.put(entry.key_ptr.*, entry.value_ptr.*);
        }

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

        if (self.owners.count() != other.owners.count()) return false;
        var owners_iter = self.owners.iterator();
        while (owners_iter.next()) |entry| {
            if (other.owners.get(entry.key_ptr.*)) |other_owner| {
                if (entry.value_ptr.* != other_owner) return false;
            } else {
                return false;
            }
        }

        return true;
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
            errdeferred_hash ^= hasher.final();
        }

        var owners_hash: u64 = 0;
        var owners_iter = self.owners.iterator();
        while (owners_iter.next()) |entry| {
            var hasher = std.hash.Wyhash.init(0);
            const key = ids.varIndex(entry.key_ptr.*);
            const value = ids.varIndex(entry.value_ptr.*);
            hasher.update(std.mem.asBytes(&key));
            hasher.update(std.mem.asBytes(&value));
            owners_hash ^= hasher.final();
        }

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
        const owners_count = self.owners.count();
        hasher.update(std.mem.asBytes(&aliases_count));
        hasher.update(std.mem.asBytes(&deferred_count));
        hasher.update(std.mem.asBytes(&errdeferred_count));
        hasher.update(std.mem.asBytes(&owners_count));

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

    pub fn escapeOwned(self: *Store, container: VarId) std.mem.Allocator.Error!void {
        const container_root = self.canonical(container);
        var to_escape: std.ArrayList(VarId) = .empty;
        defer to_escape.deinit(self.allocator);

        var iter = self.owners.iterator();
        while (iter.next()) |entry| {
            if (entry.value_ptr.* == container_root) {
                try to_escape.append(self.allocator, entry.key_ptr.*);
            }
        }

        for (to_escape.items) |resource| {
            self.escapeRegion(resource);
        }
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

    pub fn resetRegion(self: *Store, region: VarId) void {
        if (self.aliases.get(region)) |_| {
            _ = self.aliases.remove(region);
            return;
        }
        self.removeOwnershipFor(region);
        const root = self.canonical(region);
        var has_alias = false;
        var new_root: VarId = root;
        var iter = self.aliases.iterator();
        while (iter.next()) |entry| {
            if (entry.value_ptr.* == root) {
                if (!has_alias) {
                    has_alias = true;
                    new_root = entry.key_ptr.*;
                } else if (ids.varIndex(entry.key_ptr.*) < ids.varIndex(new_root)) {
                    new_root = entry.key_ptr.*;
                }
            }
        }

        if (!has_alias) {
            _ = self.resources.remove(root);
            _ = self.deferred.remove(root);
            _ = self.errdeferred.remove(root);
            return;
        }

        if (self.resources.get(root)) |state| {
            _ = self.resources.remove(root);
            _ = self.resources.remove(new_root);
            self.resources.put(new_root, state) catch {
                _ = self.resources.remove(new_root);
            };
        } else {
            _ = self.resources.remove(new_root);
        }

        if (self.deferred.get(root)) |action| {
            _ = self.deferred.remove(root);
            _ = self.deferred.remove(new_root);
            self.deferred.put(new_root, action) catch {
                _ = self.deferred.remove(new_root);
            };
        } else {
            _ = self.deferred.remove(new_root);
        }

        if (self.errdeferred.get(root)) |action| {
            _ = self.errdeferred.remove(root);
            _ = self.errdeferred.remove(new_root);
            self.errdeferred.put(new_root, action) catch {
                _ = self.errdeferred.remove(new_root);
            };
        } else {
            _ = self.errdeferred.remove(new_root);
        }

        var update_iter = self.aliases.iterator();
        while (update_iter.next()) |entry| {
            if (entry.value_ptr.* == root) {
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
        try self.deferred.put(root, .{ .action = .free, .scope_node = scope_node });
    }

    pub fn markDeferredFreeOwned(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.deferred.get(root)) |entry| {
            if (entry.action == .free_owned) {
                try self.recordViolation(root, .double_free, call_token);
            }
        }
        try self.deferred.put(root, .{ .action = .free_owned, .scope_node = scope_node });
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
        try self.deferred.put(root, .{ .action = .close, .scope_node = scope_node });
    }

    pub fn markErrdeferredFree(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.errdeferred.get(root)) |action| {
            if (action.action == .free) {
                try self.recordViolation(root, .double_free, call_token);
            }
        }
        try self.errdeferred.put(root, .{ .action = .free, .call_token = call_token, .scope_node = scope_node });
    }

    pub fn markErrdeferredFreeOwned(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.errdeferred.get(root)) |action| {
            if (action.action == .free_owned) {
                try self.recordViolation(root, .double_free, call_token);
            }
        }
        try self.errdeferred.put(root, .{ .action = .free_owned, .call_token = call_token, .scope_node = scope_node });
    }

    pub fn markErrdeferredClose(self: *Store, region: VarId, call_token: ?u32, scope_node: ?u32) !void {
        const root = self.canonical(region);
        if (self.errdeferred.get(root)) |action| {
            if (action.action == .close) {
                try self.recordViolation(root, .double_close, call_token);
            }
        }
        try self.errdeferred.put(root, .{ .action = .close, .call_token = call_token, .scope_node = scope_node });
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
    }

    fn ownerHasDeferredFreeOwned(self: *const Store, region: VarId, error_path: bool) bool {
        const root = self.canonical(region);
        const owner = self.owners.get(root) orelse return false;
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

    /// Widening operator for stores.
    /// Used at widening points to ensure convergence.
    /// - Resources: keep only if both agree, else set to `unknown`.
    /// - Aliases/owners/deferred/errdeferred: keep only if both agree, else drop.
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

        result.violations = try self.violations.merge(other.violations, allocator);

        return result;
    }

    /// Returns true if `self` is at least as general as `other`.
    /// Missing entries in `self` are treated as unknown/no-info.
    pub fn subsumes(self: *const Store, other: *const Store) bool {
        var res_iter = self.resources.iterator();
        while (res_iter.next()) |entry| {
            const region = entry.key_ptr.*;
            const self_state = entry.value_ptr.*;
            const other_state = other.resources.get(region) orelse .unknown;
            if (self_state != .unknown and self_state != other_state) return false;
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

        var owners_iter = self.owners.iterator();
        while (owners_iter.next()) |entry| {
            const resource = entry.key_ptr.*;
            const self_owner = entry.value_ptr.*;
            const other_owner = other.owners.get(resource) orelse return false;
            if (self_owner != other_owner) return false;
        }

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

    try testing.expect(general.subsumes(&specific));

    try specific.markFreed(region, 1);
    try specific.markFreed(region, 2);

    try testing.expect(!general.subsumes(&specific));

    try general.markAllocated(region);
    try general.markFreed(region, 1);
    try general.markFreed(region, 2);

    try testing.expect(general.subsumes(&specific));
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
