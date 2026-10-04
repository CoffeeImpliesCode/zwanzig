// EXPECT: line=14 rule=optional-unwrap
// EXPECT: line=19 rule=optional-unwrap
// EXPECT: line=24 rule=optional-unwrap
// EXPECT: line=29 rule=optional-unwrap
// EXPECT: line=34 rule=optional-unwrap
// EXPECT: line=39 rule=optional-unwrap

pub const State = struct {
    value: ?u32 = null,
    fn reset(self: *State) void { self.value = null; }
    fn deferredReset(self: *State) !void { self.value = 1; defer self.value = null; }
    pub fn read_deferredReset(self: *State) u32 {
        self.deferredReset() catch return 0;
        return self.value.?; // deferredReset
    }
    fn deferredAliasReset(self: *State) !void { const alias = self; self.value = 1; defer alias.value = null; }
    pub fn read_deferredAliasReset(self: *State) u32 {
        self.deferredAliasReset() catch return 0;
        return self.value.?; // deferredAliasReset
    }
    fn deferredCallReset(self: *State) !void { self.value = 1; defer self.reset(); }
    pub fn read_deferredCallReset(self: *State) u32 {
        self.deferredCallReset() catch return 0;
        return self.value.?; // deferredCallReset
    }
    fn overwritten(self: *State) !void { self.value = 1; self.value = null; }
    pub fn read_overwritten(self: *State) u32 {
        self.overwritten() catch return 0;
        return self.value.?; // overwritten
    }
    fn conditional(self: *State, take: bool) !void { if (take) { self.value = 1; } }
    pub fn read_conditional(self: *State, take: bool) u32 {
        self.conditional(take) catch return 0;
        return self.value.?; // conditional
    }
    fn earlySuccess(self: *State, take: bool) !void { if (take) return; self.value = 1; }
    pub fn read_earlySuccess(self: *State, take: bool) u32 {
        self.earlySuccess(take) catch return 0;
        return self.value.?; // earlySuccess
    }
};
