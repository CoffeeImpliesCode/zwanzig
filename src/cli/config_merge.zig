const std = @import("std");
const compat = @import("../compat.zig");
const args_mod = @import("args.zig");
const config = @import("../config.zig");
const RuleFilter = @import("../rule_filter.zig").RuleFilter;

const CliArgs = args_mod.CliArgs;

pub const MergedConfig = struct {
    rule_filter: RuleFilter,
    max_worklist_steps: ?usize,
    max_states_per_point: ?u32,
    use_widening: ?bool,
    resource_models: []const config.ResourceModel = &.{},
    escape_models: []const config.EscapeModel = &.{},
    escape_max_depth: ?u32 = null,
    optional_unwrap_test_severity: ?@import("../diagnostic.zig").Severity = null,
};

fn defaultRuleFilter(allocator: std.mem.Allocator) !RuleFilter {
    var rule_names = try allocator.alloc([]const u8, 1);
    errdefer allocator.free(rule_names);
    rule_names[0] = try allocator.dupe(u8, "sentinel-alloc");
    return .{ .blocklist = rule_names };
}

pub fn mergeConfig(io_context: *compat.Context, allocator: std.mem.Allocator, cli_args: CliArgs) !MergedConfig {
    const config_path = cli_args.config_path orelse ".zwanzig.json";

    var loaded_config = config.loadConfig(io_context, allocator, config_path) catch |err| {
        if (err == config.ConfigError.FileNotFound and cli_args.config_path == null) {
            const rule_filter = switch (cli_args.rule_filter) {
                .none => try defaultRuleFilter(allocator),
                else => cli_args.rule_filter,
            };
            return .{
                .rule_filter = rule_filter,
                .max_worklist_steps = cli_args.max_worklist_steps,
                .max_states_per_point = cli_args.max_states_per_point,
                .use_widening = cli_args.use_widening orelse true,
                .escape_max_depth = null,
            };
        }
        return err;
    };
    const max_worklist_steps = cli_args.max_worklist_steps orelse loaded_config.max_worklist_steps;
    const max_states_per_point = cli_args.max_states_per_point orelse loaded_config.max_states_per_point;
    const use_widening = cli_args.use_widening orelse loaded_config.use_widening orelse true;
    const resource_models = loaded_config.resource_models;
    const escape_models = loaded_config.escape_models;
    const escape_max_depth = loaded_config.escape_max_depth;
    const optional_unwrap_test_severity = loaded_config.optional_unwrap_test_severity;

    switch (cli_args.rule_filter) {
        .none => {
            return .{
                .rule_filter = loaded_config.rule_filter,
                .max_worklist_steps = max_worklist_steps,
                .max_states_per_point = max_states_per_point,
                .use_widening = use_widening,
                .resource_models = resource_models,
                .escape_models = escape_models,
                .escape_max_depth = escape_max_depth,
                .optional_unwrap_test_severity = optional_unwrap_test_severity,
            };
        },
        .allowlist => {
            // Free only the rule_filter part, keep resource_models
            loaded_config.resource_models = &.{}; // Prevent deinit from freeing
            loaded_config.escape_models = &.{}; // Prevent deinit from freeing
            loaded_config.deinit(allocator);
            return .{
                .rule_filter = cli_args.rule_filter,
                .max_worklist_steps = max_worklist_steps,
                .max_states_per_point = max_states_per_point,
                .use_widening = use_widening,
                .resource_models = resource_models,
                .escape_models = escape_models,
                .escape_max_depth = escape_max_depth,
                .optional_unwrap_test_severity = optional_unwrap_test_severity,
            };
        },
        .blocklist => {
            // Free only the rule_filter part, keep resource_models
            loaded_config.resource_models = &.{}; // Prevent deinit from freeing
            loaded_config.escape_models = &.{}; // Prevent deinit from freeing
            loaded_config.deinit(allocator);
            return .{
                .rule_filter = cli_args.rule_filter,
                .max_worklist_steps = max_worklist_steps,
                .max_states_per_point = max_states_per_point,
                .use_widening = use_widening,
                .resource_models = resource_models,
                .escape_models = escape_models,
                .escape_max_depth = escape_max_depth,
                .optional_unwrap_test_severity = optional_unwrap_test_severity,
            };
        },
    }
}

pub fn freeMergedConfig(allocator: std.mem.Allocator, cli_args: CliArgs, merged: MergedConfig) void {
    switch (merged.rule_filter) {
        .allowlist => |list| {
            const should_free = switch (cli_args.rule_filter) {
                .allowlist => |cli_list| list.ptr != cli_list.ptr,
                else => true,
            };
            if (should_free) {
                for (list) |rule_name| {
                    allocator.free(rule_name);
                }
                allocator.free(list);
            }
        },
        .blocklist => |list| {
            const should_free = switch (cli_args.rule_filter) {
                .blocklist => |cli_list| list.ptr != cli_list.ptr,
                else => true,
            };
            if (should_free) {
                for (list) |rule_name| {
                    allocator.free(rule_name);
                }
                allocator.free(list);
            }
        },
        .none => {},
    }

    // `mergeConfig` hands the parsed lists over instead of letting
    // `Config.deinit` release them, so this is where a merged config's models
    // go. Releasing them through the shared helpers is what keeps a field
    // added to either model type from leaking on this path.
    config.freeResourceModels(allocator, merged.resource_models);
    config.freeEscapeModels(allocator, merged.escape_models);
}

test "mergeConfig: CLI overrides config allowlist" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    var tmp_dir = compat.TestDir.init();
    defer tmp_dir.cleanup();

    var tmp_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const tmp_path = try std.fmt.bufPrint(&tmp_path_buf, "{s}", .{tmp_dir.path()});

    var config_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const config_path = try std.fmt.bufPrint(&config_path_buf, "{s}/.zwanzig.json", .{tmp_path});

    const config_content =
        \\{
        \\  "enabled_rules": ["empty-catch"]
        \\}
    ;
    try tmp_dir.writeFile(".zwanzig.json", config_content);

    const cli_allowlist = [_][]const u8{"dupe-import"};
    const cli_args = CliArgs{
        .paths = &.{},
        .rule_filter = .{ .allowlist = &cli_allowlist },
        .build_metadata = null,
        .config_path = config_path,
        .output_format = .text,
        .use_cache = false,
        .max_worklist_steps = null,
        .max_states_per_point = null,
        .use_widening = null,
        .dump_cfg_dir = null,
        .dump_exploded_graph_dir = null,
        .dump_annotated_cfg_dir = null,
        .dump_path_trace_dir = null,
        .thread_count = 1,
    };

    const result = try mergeConfig(io_context, allocator, cli_args);
    defer freeMergedConfig(allocator, cli_args, result);

    switch (result.rule_filter) {
        .allowlist => |list| {
            try std.testing.expectEqual(@as(usize, 1), list.len);
            try std.testing.expectEqualStrings("dupe-import", list[0]);
        },
        else => return error.UnexpectedFilterType,
    }
}

test "mergeConfig: uses config when no CLI filter" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    var tmp_dir = compat.TestDir.init();
    defer tmp_dir.cleanup();

    var tmp_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const tmp_path = try std.fmt.bufPrint(&tmp_path_buf, "{s}", .{tmp_dir.path()});

    var config_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const config_path = try std.fmt.bufPrint(&config_path_buf, "{s}/.zwanzig.json", .{tmp_path});

    const config_content =
        \\{
        \\  "disabled_rules": ["todo"]
        \\}
    ;
    try tmp_dir.writeFile(".zwanzig.json", config_content);

    const cli_args = CliArgs{
        .paths = &.{},
        .rule_filter = .none,
        .build_metadata = null,
        .config_path = config_path,
        .output_format = .text,
        .use_cache = false,
        .max_worklist_steps = null,
        .max_states_per_point = null,
        .use_widening = null,
        .dump_cfg_dir = null,
        .dump_exploded_graph_dir = null,
        .dump_annotated_cfg_dir = null,
        .dump_path_trace_dir = null,
        .thread_count = 1,
    };

    const result = try mergeConfig(io_context, allocator, cli_args);
    defer freeMergedConfig(allocator, cli_args, result);

    switch (result.rule_filter) {
        .blocklist => |list| {
            try std.testing.expectEqual(@as(usize, 1), list.len);
            try std.testing.expectEqualStrings("todo", list[0]);
        },
        else => return error.UnexpectedFilterType,
    }
}

test "freeMergedConfig: releases every model a parsed config owns" {
    const allocator = std.testing.allocator;
    const io_context = compat.defaultContext();

    var tmp_dir = compat.TestDir.init();
    defer tmp_dir.cleanup();

    var tmp_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const tmp_path = try std.fmt.bufPrint(&tmp_path_buf, "{s}", .{tmp_dir.path()});

    var config_path_buf: [std.fs.max_path_bytes]u8 = undefined;
    const config_path = try std.fmt.bufPrint(&config_path_buf, "{s}/.zwanzig.json", .{tmp_path});

    // Every field the parsers fill today. A field added later and filled from
    // JSON is covered the same way: the models come from the parser rather than
    // from a literal here, and std.testing.allocator reports whatever the
    // release path misses as a leak.
    const config_content =
        \\{
        \\  "resource_models": [
        \\    {"kind": "open", "method_name": "open", "receiver_type": "MyPool", "return_type": "MyHandle", "fqn": "mypkg.MyPool.open"}
        \\  ],
        \\  "escape_models": [
        \\    {"fqn": "std.process.Child.init", "method_name": "init", "receiver_type": "std.process.Child", "param_indices": [0], "captures_into": "return"}
        \\  ]
        \\}
    ;
    try tmp_dir.writeFile(".zwanzig.json", config_content);

    const cli_allowlist = [_][]const u8{"dupe-import"};
    // `.none` keeps the parsed rule filter; an allowlist makes `mergeConfig`
    // release the loaded config's filter itself and hand over only the models,
    // which is the path that has to release what `Config.deinit` skipped.
    for ([_]RuleFilter{ .none, .{ .allowlist = &cli_allowlist } }) |rule_filter| {
        const cli_args = CliArgs{
            .paths = &.{},
            .rule_filter = rule_filter,
            .build_metadata = null,
            .config_path = config_path,
            .output_format = .text,
            .use_cache = false,
            .max_worklist_steps = null,
            .max_states_per_point = null,
            .use_widening = null,
            .dump_cfg_dir = null,
            .dump_exploded_graph_dir = null,
            .dump_annotated_cfg_dir = null,
            .dump_path_trace_dir = null,
            .thread_count = 1,
        };

        const merged = try mergeConfig(io_context, allocator, cli_args);
        try std.testing.expectEqual(@as(usize, 1), merged.resource_models.len);
        try std.testing.expectEqual(@as(usize, 1), merged.escape_models.len);
        freeMergedConfig(allocator, cli_args, merged);
    }
}

test "freeMergedConfig: releases models through the shared config helpers" {
    // A field-by-field release here would skip any field added to a model type
    // later, and the leak would surface only on the paths that come through
    // this function. Two releases of the same lists stay correct only while
    // both go through src/config.zig.
    const source = @embedFile("config_merge.zig");
    const start = std.mem.indexOf(u8, source, "pub fn freeMergedConfig") orelse
        return error.TestUnexpectedResult;
    const end = std.mem.indexOfPos(u8, source, start, "\n}\n") orelse
        return error.TestUnexpectedResult;
    const body = source[start..end];

    for ([_][]const u8{ "config.freeResourceModels(", "config.freeEscapeModels(" }) |call| {
        try std.testing.expect(std.mem.indexOf(u8, body, call) != null);
    }
    for ([_][]const u8{ ".fqn", ".method_name", ".receiver_type", ".return_type", ".param_indices" }) |field| {
        try std.testing.expect(std.mem.indexOf(u8, body, field) == null);
    }
}
