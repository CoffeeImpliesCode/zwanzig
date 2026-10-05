// EXPECT: line=34 rule=optional-unwrap
// EXPECT: line=40 rule=optional-unwrap
// EXPECT: line=64 rule=optional-unwrap
// EXPECT: line=71 rule=optional-unwrap
//
// Only a `const` declaration whose initializer resolves to the real
// `std.debug.assert` proves anything. A same-named user function, an
// alias of a user `debug` namespace, a second local that binds the
// alias's name, and a rebound `var` all keep the spelling without the
// effect: an alias is matched by the declaration it names, not by spelling.
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
            const assert = std.debug.assert;
            _ = assert;
        }
        {
            const assert = lookalike;
            assert(self.value != null);
        }
        return self.value.?; // second binding of the alias's name
    }

    pub fn takeRebound(self: *Shadowing) u32 {
        var guard: *const fn (bool) void = std.debug.assert;
        guard = lookalike;
        guard(self.value != null);
        return self.value.?; // rebound var
    }
};

test "an unverified assert spelling proves nothing" {
    const assert = std.debug.assert;

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
