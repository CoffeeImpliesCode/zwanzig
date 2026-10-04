// EXPECT: none

pub const State = struct {
    value: ?u32 = null,
    fn initialize(self: *State) !void { self.value = 1; }
    fn initializeBoth(self: *State, take: bool) !void {
        if (take) { self.value = 1; } else { self.value = 2; }
    }
    fn initializeOrError(self: *State, fail: bool) !void {
        if (fail) return error.Failed;
        self.value = 1;
    }
    fn errorOnlyReset(self: *State) !void {
        self.value = 1;
        errdefer self.value = null;
    }
    pub fn readPlain(self: *State) u32 {
        self.initialize() catch return 0;
        return self.value.?;
    }
    pub fn readBoth(self: *State, take: bool) u32 {
        self.initializeBoth(take) catch return 0;
        return self.value.?;
    }
    pub fn readOrError(self: *State, fail: bool) u32 {
        self.initializeOrError(fail) catch return 0;
        return self.value.?;
    }
    pub fn readErrorOnly(self: *State) u32 {
        self.errorOnlyReset() catch return 0;
        return self.value.?;
    }
};
