// EXPECT: line=43 rule=optional-unwrap severity=warning
// EXPECT: line=48 rule=optional-unwrap severity=warning
// EXPECT: line=53 rule=optional-unwrap severity=warning
//
// A `type` annotation describes the type value an alias holds, not the
// instances that value names, so an alias annotated `?u32` still spells
// optional instances and a chain of aliases ending in one stays optional.
// Writing such a value into a field proves nothing, and reading a deref of
// a pointer to that alias proves nothing either. A real `u32`, a `*u32` and
// a struct still install the fact they are named after.
const std = @import("std");

// Every alias below ends in `?u32`, so none of them names a value the scan
// can rely on being present.
const NullableHeight: type = ?u32;
const NullableAlias: type = NullableHeight;
const NullableChain: type = NullableAlias;

// These name a type that cannot hold null.
const Height = u32;
const PlainHeight: type = u32;
const Band = struct {
    width: u16 = 80,
};

const App = struct {
    band: ?Height = null,

    fn installAnnotated(self: *App, height: NullableHeight) void {
        self.band = height;
    }

    fn installChained(self: *App, height: NullableChain) void {
        self.band = height;
    }

    fn installAnnotatedPointer(self: *App, height: *NullableAlias) void {
        self.band = height.*;
    }

    // The one caller stores an optional, so the read stays a warning.
    fn readAfterAnnotatedInstall(self: *App) Height {
        return self.band.?;
    }

    // The alias chain ends in `?u32` as well.
    fn readAfterChainedInstall(self: *App) Height {
        return self.band.?;
    }

    // A deref of a pointer to an annotated nullable alias is optional too.
    fn readAfterAnnotatedPointerInstall(self: *App) Height {
        return self.band.?;
    }
};

const Panel = struct {
    band: ?Height = null,
    aliased: ?Height = null,
    pointed: ?Height = null,
    shape: ?Band = null,

    fn installExplicit(self: *Panel, height: Height) void {
        self.band = height;
    }

    fn installAnnotatedNonNull(self: *Panel, height: PlainHeight) void {
        self.aliased = height;
    }

    fn installPointer(self: *Panel, height: *Height) void {
        self.pointed = height.*;
    }

    fn installStruct(self: *Panel, shape: Band) void {
        self.shape = shape;
    }

    fn readExplicit(self: *Panel) Height {
        return self.band.?;
    }

    fn readAnnotatedNonNull(self: *Panel) Height {
        return self.aliased.?;
    }

    fn readPointer(self: *Panel) Height {
        return self.pointed.?;
    }

    fn readStruct(self: *Panel) u16 {
        return self.shape.?.width;
    }
};

fn annotatedInstall() Height {
    var app: App = .{};
    const height: ?u32 = 24;
    app.installAnnotated(height);
    return app.readAfterAnnotatedInstall();
}

fn chainedInstall() Height {
    var app: App = .{};
    const height: ?u32 = 24;
    app.installChained(height);
    return app.readAfterChainedInstall();
}

fn annotatedPointerInstall() Height {
    var app: App = .{};
    var height: ?u32 = 24;
    app.installAnnotatedPointer(&height);
    return app.readAfterAnnotatedPointerInstall();
}

fn explicitInstall() Height {
    var panel: Panel = .{};
    panel.installExplicit(24);
    return panel.readExplicit();
}

fn annotatedNonNullInstall() Height {
    var panel: Panel = .{};
    panel.installAnnotatedNonNull(24);
    return panel.readAnnotatedNonNull();
}

fn pointerInstall() Height {
    var panel: Panel = .{};
    var height: Height = 24;
    panel.installPointer(&height);
    return panel.readPointer();
}

fn structInstall() u16 {
    var panel: Panel = .{};
    panel.installStruct(Band{});
    return panel.readStruct();
}

test "annotated nullable aliases: only the real installs are read" {
    try std.testing.expectEqual(@as(u32, 24), explicitInstall());
    try std.testing.expectEqual(@as(u32, 24), annotatedNonNullInstall());
    try std.testing.expectEqual(@as(u32, 24), pointerInstall());
    try std.testing.expectEqual(@as(u16, 80), structInstall());

    // The annotated aliases carry a value here, so these reads only miss the
    // proof; nothing in this file unwraps an absent value.
    _ = annotatedInstall;
    _ = chainedInstall;
    _ = annotatedPointerInstall;
}
