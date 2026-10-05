const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    // The import names differ from every file name, so only the build script's
    // own module graph can resolve `@import("ztex_header")` and friends.
    const marker = b.createModule(.{
        .root_source_file = b.path("src/marker.zig"),
        .target = target,
        .optimize = optimize,
    });

    const seam = b.createModule(.{
        .root_source_file = b.path("src/seam.zig"),
        .target = target,
        .optimize = optimize,
    });

    const probe_seam = b.createModule(.{
        .root_source_file = b.path("src/probe_seam.zig"),
        .target = target,
        .optimize = optimize,
    });

    const abi_check = b.addObject(.{
        .name = "abi-check",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/checker.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "ztex_header", .module = marker },
                .{ .name = "abi_seam", .module = seam },
            },
        }),
    });

    b.getInstallStep().dependOn(&abi_check.step);
    b.step("check", "Compile the ABI checker object").dependOn(&abi_check.step);

    // Reachability probe: the abi_version comparison is deliberately wrong, so
    // this step must fail with "named-module probe reached the root checker"
    // and name the guarded call in src/probe_seam.zig as its comptime caller.
    const abi_probe = b.addObject(.{
        .name = "abi-probe",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/probe.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{
                .{ .name = "ztex_header", .module = marker },
                .{ .name = "abi_probe_seam", .module = probe_seam },
            },
        }),
    });

    b.step("probe", "Compile the deliberately failing ABI probe object").dependOn(&abi_probe.step);
}
