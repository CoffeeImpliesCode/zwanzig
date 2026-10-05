const std = @import("std");

const Vfs = struct {
    handle: std.Io.Dir,

    /// Same name as the borrowed std factory, but this one hands back an owned
    /// directory, so it keeps normal handling and the handle is tracked.
    fn cwd(self: *Vfs) std.Io.Dir {
        return self.handle;
    }
};

fn userOwnedFactoryIsStillAnOpen(vfs: *Vfs) void {
    const owned = vfs.cwd();
    _ = owned;
}

// EXPECT: line=14 rule=store-violations-engine severity=error message=resource leak
