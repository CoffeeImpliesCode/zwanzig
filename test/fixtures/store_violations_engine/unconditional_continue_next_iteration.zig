const std = @import("std");

/// Both arms release the item and fall through to the same `continue`, so no
/// path out of this body does. The next pass is reachable only through that
/// transfer running the step first, and a pass past the first one releases its
/// item twice. Both frees name one allocation inside one pass, so the double
/// free below is real, not a release read across two iterations.
fn releasesTwiceOnSecondPass(gpa: std.mem.Allocator) !void {
    var index: u32 = 0;
    while (index < 2) : (index += 1) {
        const item = try std.fmt.allocPrint(gpa, "item-{d}", .{index});
        if (index == 0) {
            gpa.free(item);
        } else {
            gpa.free(item);
            gpa.free(item);
        }
        continue;
    }
}

/// One fresh allocation per pass, released once before the same
/// unconditional continue. The step now loops back, so both passes run, and
/// neither leaks nor releases twice: nothing here may be reported.
fn releasesOncePerPass(gpa: std.mem.Allocator) !void {
    var index: u32 = 0;
    while (index < 2) : (index += 1) {
        const item = try std.fmt.allocPrint(gpa, "item-{d}", .{index});
        gpa.free(item);
        continue;
    }
}

/// The step's right-hand side is a parameter, so the counter stops being a
/// number the moment the step runs and nothing after it can be decided from
/// it. Every pass still releases exactly what it allocated, so a counter that
/// went unknown must not turn one release into two, nor invent a pass the
/// loop never took.
fn releasesOnceWhenTheStepGoesUnknown(gpa: std.mem.Allocator, step: u32) !void {
    var index: u32 = 0;
    while (index < 2) : (index += step) {
        const item = try std.fmt.allocPrint(gpa, "item-{d}", .{index});
        gpa.free(item);
        continue;
    }
}

/// The step's right-hand side is a parameter, so it has no value to model, and
/// the body leaves the loop on its only pass, so the step never runs and no
/// second pass exists for an unknown counter to be invented in. The arm past
/// the single free stays unreachable.
fn onePassLeavesBeforeTheStep(gpa: std.mem.Allocator, step: u32) !void {
    var index: u32 = 0;
    while (index < 2) : (index += step) {
        const item = try std.fmt.allocPrint(gpa, "item-{d}", .{index});
        if (index == 0) {
            gpa.free(item);
        } else {
            gpa.free(item);
            gpa.free(item);
        }
        return;
    }
}

/// The same mutation written as a statement in the body instead of as the
/// loop's step, so nothing about it is special to a continuation: the pass
/// after the first still releases its item twice.
fn releasesTwiceWhenTheStepIsAPlainStatement(gpa: std.mem.Allocator) !void {
    var index: u32 = 0;
    while (index < 2) {
        const item = try std.fmt.allocPrint(gpa, "item-{d}", .{index});
        if (index == 0) {
            gpa.free(item);
        } else {
            gpa.free(item);
            gpa.free(item);
        }
        index += 1;
    }
}

/// A compound store reads both of its operands before it writes: the
/// counter is read where it stands, and the byte the release took away is
/// read on the right-hand side of the same operator. One allocation is
/// released once and read once, so that read is the only obligation this
/// function carries, and it is the right-hand side that carries it.
fn compoundRhsReadsReleasedBytes(gpa: std.mem.Allocator) !void {
    const bytes = try gpa.alloc(u8, 1);
    gpa.free(bytes);
    var offset: usize = 0;
    offset += bytes[0];
}

/// The left-hand side is an element rather than a binding, so this store
/// names nothing an identifier store could write. The operator changes
/// nothing about what the line does first: it reads the byte the released
/// block holds, and only then writes it back.
fn compoundElementReadsReleasedBytes(gpa: std.mem.Allocator) !void {
    const bytes = try gpa.alloc(u8, 1);
    gpa.free(bytes);
    bytes[0] += 1;
}

/// The same body once more, under a condition that admits one pass. The
/// step is a computed continuation and this loop does run it, so the
/// transfer is reached the ordinary way rather than through a return that
/// leaves before the step. The arm past the single release still needs a
/// second pass to be reached, and `index < 1` cannot take one.
fn onePassRunsTheStep(gpa: std.mem.Allocator) !void {
    var index: u32 = 0;
    while (index < 1) : (index += 1) {
        const item = try std.fmt.allocPrint(gpa, "item-{d}", .{index});
        if (index == 0) {
            gpa.free(item);
        } else {
            gpa.free(item);
            gpa.free(item);
        }
        continue;
    }
}

// Every control above that releases once per allocation releases once per
// allocation here, so these calls discharge what they take. The controls
// that release twice are left uncalled: running one would hand the same
// block back to the allocator a second time.
test "every pass releases what it allocated" {
    try releasesOncePerPass(std.testing.allocator);
    try releasesOnceWhenTheStepGoesUnknown(std.testing.allocator, 1);
    try onePassRunsTheStep(std.testing.allocator);
}

// EXPECT: line=16 rule=store-violations-engine severity=error message=double-free
// EXPECT: line=77 rule=store-violations-engine severity=error message=double-free
// EXPECT: line=92 rule=store-violations-engine severity=error message=use after free
// EXPECT: line=102 rule=store-violations-engine severity=error message=use after free
