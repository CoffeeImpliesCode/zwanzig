const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const checker_mod = @import("../../checker.zig");
const CheckerError = checker_mod.CheckerError;
const Diagnostic = checker_mod.Diagnostic;
const Source = @import("../../source.zig").Source;
const ids = @import("../../ids.zig");
const cfg_mod = @import("../../cfg.zig");
const Cfg = cfg_mod.Cfg;
const engine_mod = @import("../../engine.zig");
const AnalysisEngine = engine_mod.AnalysisEngine;
const evaluator = @import("evaluator.zig");

const SiteKind = enum {
    division,
    modulo,
};

const Site = struct {
    ast_node: u32,
    denominator_node: u32,
    kind: SiteKind,
};

const SiteOutcome = enum {
    none,
    definite,
    possible,
};

pub fn scanForZeroDivisors(
    src: *Source,
    allocator: std.mem.Allocator,
    diagnostics: *std.ArrayList(Diagnostic),
    tree: *const std.zig.Ast,
    engine: *AnalysisEngine,
    cfg: *const Cfg,
    fn_node: ids.AstNodeId,
    reported: *std.AutoHashMap(u32, void),
) CheckerError!void {
    _ = engine.getGraph();

    const tags = tree.nodes.items(.tag);
    const datas = tree.nodes.items(.data);

    const fn_index = ids.astIndex(fn_node);
    if (fn_index >= tags.len) return;

    const parent_map = try allocator.alloc(u32, tags.len);
    defer allocator.free(parent_map);
    @memset(parent_map, 0);
    ast_walk.fillParentMap(tree, fn_index, parent_map);

    var sites: std.ArrayList(Site) = .empty;
    defer sites.deinit(allocator);

    for (0..tags.len) |i| {
        const node = @as(u32, @intCast(i));
        if (!isInFunctionSubtree(node, fn_index, parent_map)) continue;

        switch (tags[i]) {
            .div, .mod => {
                const pair = datas[i].node_and_node;
                try sites.append(allocator, .{
                    .ast_node = node,
                    .denominator_node = @intFromEnum(pair[1]),
                    .kind = if (tags[i] == .mod) .modulo else .division,
                });
            },
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            => {
                const builtin_kind = builtinKind(tree, node) orelse continue;
                var params_buf: [2]std.zig.Ast.Node.Index = undefined;
                const params = tree.builtinCallParams(&params_buf, @enumFromInt(node)) orelse continue;
                if (params.len < 2) continue;
                try sites.append(allocator, .{
                    .ast_node = node,
                    .denominator_node = @intFromEnum(params[1]),
                    .kind = builtin_kind,
                });
            },
            else => {},
        }
    }

    for (sites.items) |site| {
        if (reported.contains(site.ast_node)) continue;

        const outcome = blk: {
            if (findCfgNodeForAst(cfg, site.ast_node, tree)) |cfg_node| {
                break :blk assessWithCfg(tree, engine, cfg, cfg_node, site.denominator_node);
            }
            break :blk assessWithoutCfg(tree, site.denominator_node);
        };

        if (outcome == .none) continue;
        try emitDiagnostic(src, allocator, diagnostics, tree, site, outcome);
        try reported.put(site.ast_node, {});
    }
}

fn isInFunctionSubtree(node: u32, fn_index: u32, parent_map: []const u32) bool {
    if (node == fn_index) return true;
    if (node >= parent_map.len) return false;

    var current = node;
    var depth: u32 = 0;
    while (depth < 256 and current < parent_map.len) : (depth += 1) {
        const parent = parent_map[current];
        if (parent == 0) return false;
        if (parent == fn_index) return true;
        current = parent;
    }

    return false;
}

fn builtinKind(tree: *const std.zig.Ast, node: u32) ?SiteKind {
    const token = tree.nodes.items(.main_token)[node];
    const token_tags = tree.tokens.items(.tag);
    if (token >= token_tags.len or token_tags[token] != .builtin) return null;

    const name = tree.tokenSlice(token);
    if (std.mem.eql(u8, name, "@divTrunc") or
        std.mem.eql(u8, name, "@divFloor") or
        std.mem.eql(u8, name, "@divExact"))
    {
        return .division;
    }

    if (std.mem.eql(u8, name, "@mod") or std.mem.eql(u8, name, "@rem")) {
        return .modulo;
    }

    return null;
}

fn assessWithCfg(
    tree: *const std.zig.Ast,
    engine: *AnalysisEngine,
    cfg: *const Cfg,
    cfg_node_idx: ids.CfgNodeId,
    denominator_node: u32,
) SiteOutcome {
    const graph = engine.getGraph();

    var reached_paths: usize = 0;
    var saw_definite_zero = false;
    var saw_maybe_zero = false;
    var saw_definite_non_zero = false;
    var informative_paths: usize = 0;

    for (graph.nodes.items) |exploded_node| {
        if (exploded_node.point.cfg != cfg) continue;
        if (exploded_node.point.kind != .pre) continue;
        if (exploded_node.point.node_index != cfg_node_idx) continue;

        reached_paths += 1;
        const risk = evaluator.riskWithState(tree, denominator_node, &exploded_node.state, engine, cfg);
        switch (risk) {
            .definitely_zero => {
                saw_definite_zero = true;
                informative_paths += 1;
            },
            .maybe_zero => {
                saw_maybe_zero = true;
                informative_paths += 1;
            },
            .definitely_non_zero => {
                saw_definite_non_zero = true;
                informative_paths += 1;
            },
            .unknown => {},
        }
    }

    if (reached_paths == 0) {
        return .none;
    }
    if (informative_paths == 0) {
        return assessWithoutCfg(tree, denominator_node);
    }
    if (saw_definite_zero and !saw_maybe_zero and !saw_definite_non_zero) {
        return .definite;
    }
    if (saw_definite_zero or saw_maybe_zero) {
        return .possible;
    }
    return .none;
}

fn assessWithoutCfg(tree: *const std.zig.Ast, denominator_node: u32) SiteOutcome {
    return switch (evaluator.riskWithoutState(tree, denominator_node)) {
        .definitely_zero => .definite,
        .maybe_zero => .possible,
        else => .none,
    };
}

fn findCfgNodeForAst(cfg: *const Cfg, ast_node: u32, tree: *const std.zig.Ast) ?ids.CfgNodeId {
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    if (ast_node >= main_tokens.len) return null;

    for (cfg.nodes.items, 0..) |node, idx| {
        if (node.ir_node.ast_node) |node_ast| {
            if (node_ast == ast_node) {
                return ids.cfgId(@intCast(idx));
            }
        }
    }

    const target_pos = token_starts[main_tokens[ast_node]];

    var best_match: ?ids.CfgNodeId = null;
    var best_start: u32 = 0;

    for (cfg.nodes.items, 0..) |node, idx| {
        if (node.ir_node.ast_node) |node_ast| {
            if (node_ast >= main_tokens.len) continue;
            const cfg_pos = token_starts[main_tokens[node_ast]];
            if (cfg_pos <= target_pos and cfg_pos >= best_start) {
                best_start = cfg_pos;
                best_match = ids.cfgId(@intCast(idx));
            }
        }
    }

    return best_match;
}

fn emitDiagnostic(
    src: *Source,
    allocator: std.mem.Allocator,
    diagnostics: *std.ArrayList(Diagnostic),
    tree: *const std.zig.Ast,
    site: Site,
    outcome: SiteOutcome,
) CheckerError!void {
    const main_tokens = tree.nodes.items(.main_token);
    const token_starts = tree.tokens.items(.start);

    if (site.ast_node >= main_tokens.len) return;
    const token = main_tokens[site.ast_node];
    if (token >= token_starts.len) return;

    const offset = token_starts[token];
    const loc = try src.byteToLocation(offset);

    const severity: checker_mod.Severity = switch (outcome) {
        .definite => .err,
        .possible => .warning,
        .none => return,
    };
    const message: []const u8 = switch (site.kind) {
        .division => switch (outcome) {
            .definite => "division by zero can panic at runtime",
            .possible => "possible division by zero can panic at runtime",
            .none => return,
        },
        .modulo => switch (outcome) {
            .definite => "modulo by zero can panic at runtime",
            .possible => "possible modulo by zero can panic at runtime",
            .none => return,
        },
    };

    var diagnostic = try Diagnostic.initAtLocation(
        allocator,
        src.getFilePath(),
        "divide-by-zero-engine",
        severity,
        message,
        loc.line,
        loc.column,
    );
    errdefer diagnostic.deinit(allocator);
    try diagnostics.append(allocator, diagnostic);
}

test "divide-by-zero emission propagates allocation failures without leaks" {
    const Harness = struct {
        fn run(allocator: std.mem.Allocator, tree: *const std.zig.Ast, site: Site) !void {
            var source = Source.initParsed(allocator, "divide-emission-oom.zig", tree);
            defer source.deinit();
            var result = checker_mod.AnalysisResult.init();
            defer result.deinit(allocator);

            try emitDiagnostic(&source, allocator, &result.diagnostics, tree, site, .definite);
            try std.testing.expectEqual(@as(usize, 1), result.diagnostics.items.len);
            const diagnostic = result.diagnostics.items[0];
            try std.testing.expectEqualStrings("divide-by-zero-engine", diagnostic.rule_id);
            try std.testing.expectEqual(checker_mod.Severity.err, diagnostic.severity);
            try std.testing.expectEqual(
                checker_mod.SourceRange.fromSingleLocation(.{ .line = 2, .column = 11 }),
                diagnostic.range,
            );
        }
    };
    const code: [:0]const u8 =
        \\fn foo() void {
        \\    _ = 1 / 0;
        \\}
    ;
    var tree = try std.zig.Ast.parse(std.testing.allocator, code, .zig);
    defer tree.deinit(std.testing.allocator);
    const site: Site = for (tree.nodes.items(.tag), 0..) |tag, index| {
        if (tag != .div) continue;
        break .{
            .ast_node = @intCast(index),
            .denominator_node = @intFromEnum(tree.nodes.items(.data)[index].node_and_node[1]),
            .kind = .division,
        };
    } else return error.TestUnexpectedResult;

    // The borrowed AST isolates location, message, and append allocations.
    try std.testing.checkAllAllocationFailures(std.testing.allocator, Harness.run, .{ &tree, site });
}

test "a break that leaves the loop keeps the division behind it quiet" {
    // An unlabeled `break` is routed to the loop's own exit, so a guard that
    // fires one leaves the loop instead of falling into the statement it was
    // protecting. The break edge therefore never reaches the site, and every
    // path that does carry the negated guard, which is what proves the
    // denominator non-zero here. The labeled break in this same shape is
    // pinned quiet by `labeled_break_guard_no_violation`, and both builds
    // reach the site the same way, so both have to read the same way.
    const TypeContext = @import("../../type_context.zig").TypeContext;

    const Harness = struct {
        fn scanInto(code: [:0]const u8, allocator: std.mem.Allocator, diagnostics: *std.ArrayList(Diagnostic)) !void {
            var source = Source.init(allocator, "loop-break-guard.zig", code);
            defer source.deinit();
            var type_ctx = TypeContext.init(allocator, &source);
            defer type_ctx.deinit();
            const tree = try source.ast();

            var reported: std.AutoHashMap(u32, void) = std.AutoHashMap(u32, void).init(allocator);
            defer reported.deinit();

            const context: checker_mod.CheckerContext = .{
                .build_metadata = null,
                .type_context = &type_ctx,
            };

            const tags = tree.nodes.items(.tag);
            for (0..tags.len) |i| {
                if (tags[i] != .fn_decl) continue;
                const fn_node = ids.astId(@intCast(i));

                var cfg_handle = (context.getOrBuildCfg(allocator, &source, fn_node) catch |err| switch (err) {
                    error.OutOfMemory => return error.OutOfMemory,
                    error.InvalidAst => continue,
                }) orelse continue;
                defer cfg_handle.deinit();

                var analysis = try context.getOrAnalyze(allocator, &source, &cfg_handle, "divide-by-zero-engine", .configured);
                defer analysis.deinit();
                if (analysis.complete) {
                    try scanForZeroDivisors(&source, allocator, diagnostics, tree, analysis.engine, cfg_handle.cfg, fn_node, &reported);
                }
            }
        }
    };

    const guarded: [:0]const u8 =
        \\pub fn unlabeled_break_does_not_prune(lhs: i64, rhs: i64) i64 {
        \\    while (rhs != 7) {
        \\        if (rhs == 0) break;
        \\        return @divTrunc(lhs, rhs);
        \\    }
        \\    return 0;
        \\}
    ;

    // The control carries no guard at all, so a scan that reported nothing for
    // any reason would pass the case above on its own.
    const unguarded: [:0]const u8 =
        \\pub fn reachable_zero(lhs: i64, flag: bool) i64 {
        \\    var divisor: i64 = 2;
        \\    if (flag) {
        \\        divisor = 0;
        \\    }
        \\    return @divTrunc(lhs, divisor);
        \\}
    ;

    const allocator = std.testing.allocator;

    var guarded_diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (guarded_diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        guarded_diagnostics.deinit(allocator);
    }
    try Harness.scanInto(guarded, allocator, &guarded_diagnostics);
    try std.testing.expectEqual(@as(usize, 0), guarded_diagnostics.items.len);

    var unguarded_diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (unguarded_diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        unguarded_diagnostics.deinit(allocator);
    }
    try Harness.scanInto(unguarded, allocator, &unguarded_diagnostics);
    try std.testing.expectEqual(@as(usize, 1), unguarded_diagnostics.items.len);
    try std.testing.expectEqual(checker_mod.Severity.warning, unguarded_diagnostics.items[0].severity);
    try std.testing.expectEqualStrings("possible division by zero can panic at runtime", unguarded_diagnostics.items[0].message);
}
