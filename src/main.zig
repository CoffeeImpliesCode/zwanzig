const std = @import("std");
const compat = @import("compat.zig");
const build_options = @import("build_options");
const cli_run = @import("cli/run.zig");
const args_mod = @import("cli/args.zig");

comptime {
    _ = @import("compat.zig");
}

pub const std_options = std.Options{
    .log_level = @enumFromInt(@intFromEnum(build_options.log_level)),
};

test {
    _ = @import("ir.zig");
    _ = @import("cfg.zig");
    _ = @import("checker.zig");
    _ = @import("zir_bridge.zig");
    _ = @import("engine.zig");
    _ = @import("checkers/empty_catch_engine.zig");
    _ = @import("checkers/swallowed_error.zig");
    _ = @import("checkers/unreachable_code_checker.zig");
    _ = @import("checkers/store_violations_engine.zig");
    _ = @import("checkers/optional_unwrap_engine.zig");
    _ = @import("rules/unused_decl.zig");
    _ = @import("rules/dupe_import.zig");
    _ = @import("rules/todo_comment.zig");
    _ = @import("rules/file_as_struct.zig");
    _ = @import("rules/unreachable_code.zig");
    _ = @import("rules/empty_defer.zig");
    _ = @import("rules/empty_errdefer.zig");
    _ = @import("rules/shadowed_variable.zig");
    _ = @import("rules/identifier_style.zig");
    _ = @import("rules/sentinel_alloc.zig");
    _ = @import("rules/unused_parameter.zig");
    _ = @import("rules/return_local_pointer.zig");
    _ = @import("rules/deinit_lifecycle.zig");
    _ = @import("checkers/stack_escape_engine.zig");
    _ = @import("checkers/divide_by_zero_engine.zig");
    _ = @import("checkers/slice_bounds_engine.zig");
    _ = @import("build_metadata.zig");
    _ = @import("config.zig");
    _ = @import("cache.zig");
    _ = @import("project_sources.zig");
    _ = @import("cli/args.zig");
    _ = @import("cli/config_merge.zig");
    _ = @import("cli/registry.zig");
    _ = @import("cli/run.zig");
    _ = @import("analysis/call_resolver.zig");
    _ = @import("analysis/import_resolver.zig");
}

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{ .thread_safe = true }){};
    defer _ = gpa.deinit();
    const allocator = gpa.allocator();

    const args = try std.process.argsAlloc(allocator);
    defer std.process.argsFree(allocator, args);

    const cli_args = cli_run.parseCliArgs(compat.defaultContext(), allocator, args);
    defer args_mod.freeCliArgs(allocator, cli_args);

    var io_context = try compat.Context.init(allocator, cli_args.thread_count);
    defer io_context.deinit();

    try cli_run.runParsed(allocator, cli_args, &io_context);
}
