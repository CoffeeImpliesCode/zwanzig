// EXPECT: none
const Adapter = @This();
const Mode = enum {
    idle,
    active,
};

mode: Mode,
limit: usize,
seed: usize,

fn recurse(self: *Adapter, remaining: usize) usize {
    if (remaining == 0) return self.seed;
    return self.recurse(remaining - 1);
}

fn route(self: *Adapter, remaining: usize) usize {
    return switch (self.mode) {
        .idle => self.recurse(remaining),
        .active => self.recurse(remaining / 2),
    };
}

fn walk(self: *Adapter, count: usize) usize {
    var total = self.seed;
    var index: usize = 0;
    while (index < count) : (index += 1) {
        total += self.route(count - index);
    }
    return total;
}

fn dispatch(self: *Adapter) usize {
    return switch (self.mode) {
        .idle => self.walk(self.limit),
        .active => self.route(self.limit),
    };
}

pub fn run(self: *Adapter) usize {
    return self.dispatch();
}
