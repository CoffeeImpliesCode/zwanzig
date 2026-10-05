const std = @import("std");
const ids = @import("../ids.zig");
const AbstractValue = @import("value.zig").AbstractValue;
pub const VarId = ids.VarId;

/// Environment: mapping from variables to abstract values.
/// Represents the known values of variables at a program point.
pub const Environment = struct {
    /// Map from variable ID to abstract value
    bindings: std.AutoHashMap(VarId, AbstractValue),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Environment {
        return .{
            .bindings = std.AutoHashMap(VarId, AbstractValue).init(allocator),
            .allocator = allocator,
        };
    }

    pub fn deinit(self: *Environment) void {
        self.bindings.deinit();
    }

    /// Copy bindings into independent storage owned by allocator.
    pub fn clone(self: *const Environment, allocator: std.mem.Allocator) !Environment {
        return .{
            .bindings = try self.bindings.cloneWithAllocator(allocator),
            .allocator = allocator,
        };
    }

    pub fn get(self: *const Environment, var_id: VarId) ?AbstractValue {
        return self.bindings.get(var_id);
    }

    pub fn set(self: *Environment, var_id: VarId, value: AbstractValue) !void {
        try self.bindings.put(var_id, value);
    }

    pub fn remove(self: *Environment, var_id: VarId) void {
        _ = self.bindings.remove(var_id);
    }

    pub fn size(self: *const Environment) usize {
        return self.bindings.count();
    }

    pub fn eql(self: *const Environment, other: *const Environment) bool {
        if (self.bindings.count() != other.bindings.count()) return false;

        var iter = self.bindings.iterator();
        while (iter.next()) |entry| {
            if (other.bindings.get(entry.key_ptr.*)) |other_val| {
                if (!entry.value_ptr.*.eql(other_val)) return false;
            } else {
                return false;
            }
        }
        return true;
    }

    pub fn computeHash(self: *const Environment) u64 {
        // Use XOR-based hashing which is order-independent and requires no allocation
        var combined_hash: u64 = 0;

        var iter = self.bindings.iterator();
        while (iter.next()) |entry| {
            var hasher = std.hash.Wyhash.init(0);
            const key = ids.varIndex(entry.key_ptr.*);
            hasher.update(std.mem.asBytes(&key));
            const val_hash = entry.value_ptr.*.hash();
            hasher.update(std.mem.asBytes(&val_hash));
            combined_hash ^= hasher.final();
        }

        return combined_hash;
    }

    /// Widening operator for environments.
    /// Used at widening points to ensure convergence.
    /// - Union of variables from both environments.
    /// - For variables in both: widen the values.
    /// - For variables in only one side: set to `unknown`.
    pub fn widen(self: *const Environment, other: *const Environment) !Environment {
        var result = Environment.init(self.allocator);
        errdefer result.deinit();

        // Process variables from self
        var self_iter = self.bindings.iterator();
        while (self_iter.next()) |entry| {
            const var_id = entry.key_ptr.*;
            const self_val = entry.value_ptr.*;

            if (other.bindings.get(var_id)) |other_val| {
                // Variable exists in both: widen
                try result.bindings.put(var_id, self_val.widen(other_val));
            } else {
                // Variable only in self: widen to unknown
                try result.bindings.put(var_id, .unknown);
            }
        }

        // Process variables only in other (not in self)
        var other_iter = other.bindings.iterator();
        while (other_iter.next()) |entry| {
            const var_id = entry.key_ptr.*;
            if (!self.bindings.contains(var_id)) {
                // Variable only in other: set to unknown
                try result.bindings.put(var_id, .unknown);
            }
        }

        return result;
    }

    /// Returns true if `self` is at least as general as `other`.
    /// Missing bindings in `self` are treated as `unknown`.
    pub fn subsumes(self: *const Environment, other: *const Environment) bool {
        var iter = self.bindings.iterator();
        while (iter.next()) |entry| {
            const var_id = entry.key_ptr.*;
            const self_val = entry.value_ptr.*;
            const other_val = other.bindings.get(var_id) orelse .unknown;
            if (!self_val.subsumes(other_val)) return false;
        }
        return true;
    }
};

test "Environment operations" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var env = Environment.init(allocator);
    defer env.deinit();

    try testing.expectEqual(@as(usize, 0), env.size());
    try testing.expect(env.get(ids.varId(1)) == null);

    try env.set(ids.varId(1), .{ .concrete_int = 42 });
    try testing.expectEqual(@as(usize, 1), env.size());

    const val = env.get(ids.varId(1));
    try testing.expect(val != null);
    try testing.expect(val.?.eql(.{ .concrete_int = 42 }));

    try env.set(ids.varId(2), .non_null);
    try testing.expectEqual(@as(usize, 2), env.size());

    env.remove(ids.varId(1));
    try testing.expectEqual(@as(usize, 1), env.size());
    try testing.expect(env.get(ids.varId(1)) == null);
}

test "Environment equality and cloning" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var env1 = Environment.init(allocator);
    defer env1.deinit();

    try env1.set(ids.varId(1), .{ .concrete_int = 10 });
    try env1.set(ids.varId(2), .non_null);

    var env2 = try env1.clone(allocator);
    defer env2.deinit();

    try testing.expect(env1.eql(&env2));

    try env2.set(ids.varId(1), .{ .concrete_int = 20 });
    env2.remove(ids.varId(2));
    try env1.set(ids.varId(3), .{ .concrete_bool = true });
    try testing.expect(!env1.eql(&env2));
    try testing.expect(env1.get(ids.varId(1)).?.eql(.{ .concrete_int = 10 }));
    try testing.expect(env1.get(ids.varId(2)).?.eql(.non_null));
    try testing.expect(env2.get(ids.varId(3)) == null);
}

test "Environment clone outlives its source allocator" {
    const testing = std.testing;

    var copy = blk: {
        var arena = std.heap.ArenaAllocator.init(testing.allocator);
        defer arena.deinit();
        var source = Environment.init(arena.allocator());
        defer source.deinit();
        try source.set(ids.varId(1), .{ .int_range = .{ .min = -3, .max = 7 } });
        try source.set(ids.varId(2), .null_val);
        try source.set(ids.varId(3), .{ .concrete_bool = false });

        break :blk try source.clone(testing.allocator);
    };
    defer copy.deinit();

    try testing.expect(copy.get(ids.varId(1)).?.eql(.{ .int_range = .{ .min = -3, .max = 7 } }));
    try testing.expect(copy.get(ids.varId(2)).?.eql(.null_val));
    try testing.expect(copy.get(ids.varId(3)).?.eql(.{ .concrete_bool = false }));
    try copy.set(ids.varId(1), .{ .concrete_int = 5 });
    copy.remove(ids.varId(2));
    try testing.expect(copy.get(ids.varId(1)).?.eql(.{ .concrete_int = 5 }));
    try testing.expect(copy.get(ids.varId(2)) == null);
}

test "Environment cloning preserves its source on allocation failure" {
    const testing = std.testing;
    var source = Environment.init(testing.allocator);
    defer source.deinit();
    try source.set(ids.varId(1), .{ .concrete_int = 42 });
    try source.set(ids.varId(2), .non_null);
    const source_hash = source.computeHash();

    const Harness = struct {
        fn run(allocator: std.mem.Allocator, original: *const Environment) !void {
            var copy = try original.clone(allocator);
            defer copy.deinit();
            try std.testing.expect(original.eql(&copy));
        }
    };
    try testing.checkAllAllocationFailures(testing.allocator, Harness.run, .{&source});
    try testing.expectEqual(source_hash, source.computeHash());
    try testing.expect(source.get(ids.varId(1)).?.eql(.{ .concrete_int = 42 }));
}

test "Environment widen with disjoint variables" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var env1 = Environment.init(allocator);
    defer env1.deinit();

    var env2 = Environment.init(allocator);
    defer env2.deinit();

    // Variable only in env1
    try env1.set(ids.varId(1), .{ .concrete_int = 10 });

    // Variable only in env2
    try env2.set(ids.varId(2), .{ .concrete_int = 20 });

    var widened = try env1.widen(&env2);
    defer widened.deinit();

    // Both variables should be present but widened to unknown
    try testing.expectEqual(@as(usize, 2), widened.size());

    const val1 = widened.get(ids.varId(1));
    try testing.expect(val1 != null);
    try testing.expect(val1.?.isUnknown());

    const val2 = widened.get(ids.varId(2));
    try testing.expect(val2 != null);
    try testing.expect(val2.?.isUnknown());
}

test "Environment widen with overlapping variables" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var env1 = Environment.init(allocator);
    defer env1.deinit();

    var env2 = Environment.init(allocator);
    defer env2.deinit();

    // Both environments bind the same variables; only the second one differs.
    try env1.set(ids.varId(1), .{ .concrete_int = 10 });
    try env1.set(ids.varId(2), .{ .concrete_int = 20 });

    try env2.set(ids.varId(1), .{ .concrete_int = 10 }); // same
    try env2.set(ids.varId(2), .{ .concrete_int = 30 }); // different

    // var3 exists only in env2 and widens to unknown.
    try env2.set(ids.varId(3), .{ .concrete_bool = true });

    var widened = try env1.widen(&env2);
    defer widened.deinit();

    try testing.expectEqual(@as(usize, 3), widened.size());

    // The shared value survives untouched: `widen` returns `self` when both
    // sides are equal.
    const shared = widened.get(ids.varId(1));
    try testing.expect(shared != null);
    try testing.expect(shared.?.eql(.{ .concrete_int = 10 }));

    // The differing pair becomes the integer interval spanning them: the bound
    // that did not move is kept, the one that did is thrown to the end of the
    // `i64` domain.
    const differing = widened.get(ids.varId(2));
    try testing.expect(differing != null);
    try testing.expect(differing.?.eql(.{ .int_range = .{
        .min = 20,
        .max = std.math.maxInt(i64),
    } }));

    // A variable only in one side has no value to widen against, so it stays
    // unknown.
    const one_sided = widened.get(ids.varId(3));
    try testing.expect(one_sided != null);
    try testing.expect(one_sided.?.isUnknown());
}

test "Environment widen with empty environments" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var env1 = Environment.init(allocator);
    defer env1.deinit();

    var env2 = Environment.init(allocator);
    defer env2.deinit();

    // Both empty
    var widened1 = try env1.widen(&env2);
    defer widened1.deinit();
    try testing.expectEqual(@as(usize, 0), widened1.size());

    // One has values, one empty
    try env1.set(ids.varId(1), .{ .concrete_int = 10 });

    var widened2 = try env1.widen(&env2);
    defer widened2.deinit();

    try testing.expectEqual(@as(usize, 1), widened2.size());
    const val = widened2.get(ids.varId(1));
    try testing.expect(val != null);
    try testing.expect(val.?.isUnknown());
}

test "Environment subsumes respects missing bindings as unknown" {
    const testing = std.testing;
    const allocator = testing.allocator;

    var general = Environment.init(allocator);
    defer general.deinit();

    var specific = Environment.init(allocator);
    defer specific.deinit();

    try specific.set(ids.varId(1), .{ .concrete_int = 42 });

    try testing.expect(general.subsumes(&specific));
    try testing.expect(!specific.subsumes(&general));
}
