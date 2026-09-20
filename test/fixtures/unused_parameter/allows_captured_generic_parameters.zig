// EXPECT: none

const JobResult = struct {
    value: u32,
};

pub fn Batch(comptime Result: type) type {
    return struct {
        const Self = @This();

        current: Result,
        result_storage: []Result,

        pub fn init(current: Result, result_storage: []Result) Self {
            return .{
                .current = current,
                .result_storage = result_storage,
            };
        }

        pub fn store(self: *Self, result: Result) void {
            self.current = result;
            self.result_storage[0] = result;
        }

        pub fn first(self: *const Self) Result {
            return self.result_storage[0];
        }
    };
}

pub fn SegmentList(comptime T: type) type {
    return struct {
        const Self = @This();

        pointer: *T,
        items: []T,
        value: T,

        pub fn init(pointer: *T, items: []T, value: T) Self {
            return .{
                .pointer = pointer,
                .items = items,
                .value = value,
            };
        }

        pub fn set(self: *Self, value: T) void {
            self.pointer.* = value;
            self.value = value;
        }

        pub fn getPtr(self: *Self) *T {
            return self.pointer;
        }

        pub fn slice(self: *Self) []T {
            return self.items;
        }
    };
}

pub fn main() void {
    var results = [_]JobResult{
        .{ .value = 1 },
        .{ .value = 2 },
    };
    var batch = Batch(JobResult).init(results[0], results[0..]);
    batch.store(.{ .value = 3 });
    const first = batch.first();

    var values = [_]u16{ 4, 5 };
    var list = SegmentList(u16).init(&values[0], values[0..], values[0]);
    list.set(6);
    const pointer = list.getPtr();
    const items = list.slice();

    if (batch.current.value != first.value) unreachable;
    if (pointer.* != items[0]) unreachable;
    if (list.value != pointer.*) unreachable;
}
