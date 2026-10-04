// EXPECT: line=34 rule=optional-unwrap
// EXPECT: line=40 rule=optional-unwrap
// EXPECT: line=60 rule=optional-unwrap
// EXPECT: line=67 rule=optional-unwrap
//
// Only a `const` declaration whose initializer resolves to the real
// `std.debug.assert` proves anything. A same-named user function, an
// alias of a user `debug` namespace, a local that shadows the alias, and
// a `var` that is rebound to another function all keep the spelling
// without the effect.
const std = @import("std");

const lookalike = struct {
    pub fn check(_: bool) void {}
}.check;

const UserDebug = struct {
    pub fn assert(_: bool) void {}
};

const State = struct {
    value: ?u32 = null,

    fn init() State {
        return .{};
    }

    pub fn write(self: *State, value: u32) void {
        self.value = value;
    }

    pub fn takeUserFunction(self: *State) u32 {
        lookalike(self.value != null);
        return self.value.?; // user function named assert
    }

    pub fn takeUserNamespace(self: *State) u32 {
        const debug = UserDebug;
        debug.assert(self.value != null);
        return self.value.?; // user debug namespace
    }
};

const Shadowing = struct {
    value: ?u32 = null,

    fn init() Shadowing {
        return .{};
    }

    pub fn write(self: *Shadowing, value: u32) void {
        self.value = value;
    }

    pub fn takeShadowed(self: *Shadowing) u32 {
        {
            const assert = lookalike;
            assert(self.value != null);
        }
        return self.value.?; // local shadows the alias
    }

    pub fn takeRebound(self: *Shadowing) u32 {
        var guard = std.debug.assert;
        guard = lookalike;
        guard(self.value != null);
        return self.value.?; // rebound var
    }
};

const assert = std.debug.assert;

test "an unverified assert spelling proves nothing" {
    var a = State.init();
    a.write(1);
    _ = a.takeUserFunction();
    _ = a.takeUserNamespace();

    var b = Shadowing.init();
    b.write(1);
    _ = b.takeShadowed();
    _ = b.takeRebound();

    // The real alias is still trusted here, which is what makes it a control.
    var c = State.init();
    c.write(1);
    assert(c.value != null);
    _ = c.value.?;
}
