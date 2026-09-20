const std = @import("std");
const ast_walk = @import("../../ast_walk.zig");
const call_resolver = @import("../../analysis/call_resolver.zig");
const ZirBridge = @import("../../zir_bridge.zig").ZirBridge;
const FunctionSummary = @import("../summary.zig").FunctionSummary;
const ids = @import("../../ids.zig");
const Source = @import("../../source.zig").Source;
const cfg_mod = @import("../../cfg.zig");
const Cfg = cfg_mod.Cfg;
const CfgBuilder = cfg_mod.CfgBuilder;
const AnalysisEngine = @import("engine.zig").AnalysisEngine;
const state_mod = @import("../state.zig");
const ProgramState = state_mod.ProgramState;
const ErrorState = state_mod.ErrorState;

pub fn Mixin(comptime _Engine: type) type {
    return struct {
        /// Get or compute a summary for a function.
        /// Returns the summary if it can be computed, or null if the function
        /// cannot be analyzed (e.g., missing source, external function).
        pub fn getOrComputeSummary(self: *_Engine, fn_ast_node: ids.AstNodeId) std.mem.Allocator.Error!?*FunctionSummary {
            // Check cache first
            if (self.summary_cache.get(fn_ast_node)) |summary| {
                return summary;
            }

            var summary = (try computeSummary(self, fn_ast_node)) orelse return null;
            errdefer summary.deinit();
            try self.summary_cache.put(summary);
            return self.summary_cache.get(fn_ast_node);
        }

        /// Compute a summary for a function by analyzing its CFG.
        pub fn computeSummary(self: *_Engine, fn_ast_node: ids.AstNodeId) std.mem.Allocator.Error!?FunctionSummary {
            // Get or build the function's CFG
            const callee_cfg = (try self.getOrBuildFunctionCfg(fn_ast_node)) orelse return null;

            const source = self.source orelse return null;
            const tree = try source.ast();
            var summary = FunctionSummary.init(self.allocator, fn_ast_node);
            var may_return_error = signatureMayReturnError(tree, ids.astIndex(fn_ast_node));
            var only_computation = true;

            for (callee_cfg.nodes.items) |cfg_node| {
                if (cfg_node.ir_node.tag == .try_expr) may_return_error = true;
                switch (cfg_node.ir_node.tag) {
                    .fn_entry, .fn_exit, .ret, .var_decl, .block, .expr, .nop, .branch => {},
                    else => only_computation = false,
                }
            }

            // An implicit exit or an unproven return keeps the success outcome.
            var has_exit = false;
            var all_exits_error = true;
            for (callee_cfg.edges.items) |edge| {
                if (edge.kind == .try_error) may_return_error = true;
                if (edge.to != callee_cfg.exit) continue;
                has_exit = true;
                if (edge.kind == .try_error) continue;
                const exit_node = callee_cfg.getNode(edge.from) orelse {
                    all_exits_error = false;
                    continue;
                };
                const returns_error = exit_node.ir_node.tag == .ret and
                    returnAlwaysErrors(tree, exit_node.ir_node.ast_node);
                may_return_error = may_return_error or returns_error;
                all_exits_error = all_exits_error and returns_error;
            }
            summary.setErrorBehavior(may_return_error, has_exit and all_exits_error);

            if (only_computation) {
                // Calls inside return values and initializers do not have call IR nodes.
                var effects = EffectScan{};
                EffectScan.scan(tree, ids.astIndex(fn_ast_node), &effects) catch unreachable;
                if (!effects.stop) summary.markPure();
            }
            return summary;
        }
    };
}

fn signatureMayReturnError(tree: *const std.zig.Ast, fn_node: u32) bool {
    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = tree.fullFnProto(&buffer, @enumFromInt(fn_node)) orelse return true;
    const return_type = proto.ast.return_type.unwrap() orelse return true;
    const first_token = tree.firstToken(return_type);
    if (first_token > 0 and tree.tokenTag(first_token - 1) == .bang) return true;

    // Qualified names can be shadowed aliases, not verified library types.
    switch (tree.nodeTag(return_type)) {
        .error_union, .field_access => return true,
        else => {},
    }
    // An unresolved alias is not proof of a successful return type.
    const info = ZirBridge.extractTypeFromAstNode(tree, @intFromEnum(return_type)) orelse
        return true;
    return info.kind == .error_union or info.kind == .unknown;
}

fn returnAlwaysErrors(tree: *const std.zig.Ast, return_node: ?u32) bool {
    const node = return_node orelse return false;
    if (node >= tree.nodes.len or tree.nodeTag(@enumFromInt(node)) != .@"return") {
        return false;
    }
    const expression = tree.nodeData(@enumFromInt(node)).opt_node.unwrap() orelse return false;
    return expressionAlwaysErrors(tree, @intFromEnum(expression), 0);
}

fn expressionAlwaysErrors(tree: *const std.zig.Ast, node: u32, depth: u8) bool {
    if (depth >= 64 or node >= tree.nodes.len) return false;
    const index: std.zig.Ast.Node.Index = @enumFromInt(node);
    switch (tree.nodeTag(index)) {
        .error_value => return true,
        .grouped_expression => {
            const child = tree.nodeData(index).node_and_token[0];
            return expressionAlwaysErrors(tree, @intFromEnum(child), depth + 1);
        },
        .@"if", .if_simple => {
            const full_if = tree.fullIf(index) orelse return false;
            const else_node = full_if.ast.else_expr.unwrap() orelse return false;
            return expressionAlwaysErrors(tree, @intFromEnum(full_if.ast.then_expr), depth + 1) and
                expressionAlwaysErrors(tree, @intFromEnum(else_node), depth + 1);
        },
        .@"switch", .switch_comma => {
            const full_switch = tree.switchFull(index);
            if (full_switch.ast.cases.len == 0) return false;
            for (full_switch.ast.cases) |case_node| {
                const full_case = tree.fullSwitchCase(case_node) orelse return false;
                if (!expressionAlwaysErrors(tree, @intFromEnum(full_case.ast.target_expr), depth + 1)) {
                    return false;
                }
            }
            return true;
        },
        else => return false,
    }
}

const EffectScan = struct {
    stop: bool = false,
    depth: u8 = 0,

    fn scan(tree: *const std.zig.Ast, node: u32, self: *EffectScan) error{}!void {
        if (self.stop) return;
        if (self.depth >= 64 or node >= tree.nodes.len) {
            self.stop = true;
            return;
        }
        const tag = tree.nodeTag(@enumFromInt(node));
        if (call_resolver.isCallNode(tag) or call_resolver.isAssignTag(tag)) {
            self.stop = true;
            return;
        }
        switch (tag) {
            .builtin_call,
            .builtin_call_comma,
            .builtin_call_two,
            .builtin_call_two_comma,
            .@"asm",
            .asm_simple,
            => {
                self.stop = true;
                return;
            },
            else => {},
        }
        self.depth += 1;
        defer self.depth -= 1;
        try ast_walk.walkChildren(EffectScan, tree, node, self, scan);
    }
};

fn expectSummaryBehavior(
    code: [:0]const u8,
    may_error: bool,
    always_error: bool,
    has_side_effects: bool,
) !void {
    const allocator = std.testing.allocator;

    var source = Source.init(allocator, "summary.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    try std.testing.expectEqual(@as(usize, 0), tree.errors.len);
    for (tree.rootDecls()) |decl| {
        if (tree.nodeTag(decl) != .fn_decl) continue;
        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = tree.fullFnProto(&buffer, decl) orelse continue;
        const name_token = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), "target")) continue;

        const fn_node = ids.astId(@intFromEnum(decl));
        var builder = CfgBuilder.init(allocator);
        var cfg = (try builder.buildFromFn(&source, fn_node)) orelse return error.MissingCfg;
        defer cfg.deinit();
        var engine = AnalysisEngine.initWithSource(allocator, &cfg, &source);
        defer engine.deinit();
        var summary = (try AnalysisEngine.Summaries.computeSummary(&engine, fn_node)) orelse
            return error.MissingSummary;
        defer summary.deinit();

        try std.testing.expectEqual(may_error, summary.may_return_error);
        try std.testing.expectEqual(always_error, summary.always_returns_error);
        try std.testing.expectEqual(has_side_effects, summary.has_side_effects);

        // Applying one outcome must not erase a pending caller error.
        for ([_]ErrorState{ .normal, .error_active, .error_handled }) |initial_error| {
            var state = ProgramState.init(allocator);
            defer state.deinit();
            state.setErrorState(initial_error);
            try std.testing.expect(summary.isApplicable(&state));
            try std.testing.expect(try summary.applyToState(&state));
            const expected_error: ErrorState = if (always_error) .error_active else initial_error;
            try std.testing.expectEqual(expected_error, state.error_state);
        }
        return;
    }
    return error.MissingFunction;
}

test "summary lookup propagates CFG and cache allocation failures" {
    const code: [:0]const u8 =
        "fn target(fail: bool) !u8 { if (fail) return error.Failed; return 1; }";
    var source = Source.init(std.testing.allocator, "summary-oom.zig", code);
    defer source.deinit();
    const tree = try source.ast();
    const fn_node = ids.astId(@intFromEnum(tree.rootDecls()[0]));
    try std.testing.checkAllAllocationFailures(
        std.testing.allocator,
        testSummaryAllocationFailure,
        .{ code, fn_node },
    );
}

fn testSummaryAllocationFailure(
    allocator: std.mem.Allocator,
    code: [:0]const u8,
    fn_node: ids.AstNodeId,
) !void {
    // No warmed CFG or AST: every mandatory allocation must return its failure.
    var source = Source.init(allocator, "summary-oom.zig", code);
    defer source.deinit();
    var root = Cfg.init(std.testing.allocator);
    defer root.deinit();
    var engine = AnalysisEngine.initWithSource(allocator, &root, &source);
    defer engine.deinit();
    const summary = (try AnalysisEngine.Summaries.getOrComputeSummary(&engine, fn_node)) orelse
        return error.TestUnexpectedResult;
    try std.testing.expect(summary.may_return_error);
    try std.testing.expect(!summary.always_returns_error);
    try std.testing.expect(!summary.has_side_effects);

    var state = ProgramState.init(allocator);
    defer state.deinit();
    state.setErrorState(.error_handled);
    try std.testing.expect(try summary.applyToState(&state));
    try std.testing.expectEqual(ErrorState.error_handled, state.error_state);
    const cached = (try AnalysisEngine.Summaries.getOrComputeSummary(&engine, fn_node)) orelse
        return error.TestUnexpectedResult;
    try std.testing.expectEqual(@as(u32, 1), cached.use_count);
}

test "summary lookup preserves semantic absence without allocation" {
    var source = Source.init(
        std.testing.allocator,
        "external-summary.zig",
        "extern fn external() void; const value = 1;",
    );
    defer source.deinit();
    const tree = try source.ast();
    var root = Cfg.init(std.testing.allocator);
    defer root.deinit();
    var failing = std.testing.FailingAllocator.init(std.testing.allocator, .{ .fail_index = 0 });
    var engine = AnalysisEngine.init(failing.allocator(), &root);
    defer engine.deinit();
    const external_fn = ids.astId(@intFromEnum(tree.rootDecls()[0]));
    try std.testing.expect((try AnalysisEngine.Summaries.getOrComputeSummary(&engine, external_fn)) == null);
    engine.source = &source;
    for (tree.rootDecls()) |decl| {
        try std.testing.expect((try AnalysisEngine.Summaries.getOrComputeSummary(
            &engine,
            ids.astId(@intFromEnum(decl)),
        )) == null);
    }
}

test "summary extraction recognizes explicit error returns" {
    try expectSummaryBehavior(
        "fn target() !void { return error.Failed; }",
        true,
        true,
        false,
    );
}

test "summary extraction keeps mixed returns separate from always error" {
    try expectSummaryBehavior(
        "fn target(fail: bool) !u8 { if (fail) return error.Failed; return 1; }",
        true,
        false,
        false,
    );
}

test "summary extraction counts implicit successful exits" {
    try expectSummaryBehavior(
        "fn target(fail: bool) !void { if (fail) return error.Failed; }",
        true,
        false,
        false,
    );
}

test "summary extraction respects error union signatures without try" {
    try expectSummaryBehavior(
        "fn target(value: anyerror!u8) anyerror!u8 { return value; }",
        true,
        false,
        false,
    );
}

test "summary extraction is conservative for return type aliases" {
    try expectSummaryBehavior(
        "const Result = error{Failed}!u8;" ++
            "fn target(value: Result) Result { return value; }",
        true,
        false,
        false,
    );
}

test "summary extraction does not trust qualified return type names" {
    try expectSummaryBehavior(
        "const std = struct { const fs = struct { const File = error{Failed}!u8; }; };" ++
            "fn target(value: std.fs.File) std.fs.File { return value; }",
        true,
        false,
        false,
    );
}

test "summary extraction does not prove error value aliases always fail" {
    try expectSummaryBehavior(
        "const failure = error.Failed; fn target() !void { return failure; }",
        true,
        false,
        false,
    );
}

test "summary extraction preserves successful function behavior" {
    try expectSummaryBehavior(
        "fn target(value: i32) i32 { return value + 1; }",
        false,
        false,
        false,
    );
}

test "summary extraction does not treat unknown callees as pure" {
    try expectSummaryBehavior(
        "const Result = error{Failed}!u8; extern fn external() Result;" ++
            "fn target() Result { return external(); }",
        true,
        false,
        true,
    );
}

test "summary extraction sees calls in initializers" {
    try expectSummaryBehavior(
        "extern fn external() u8;" ++
            "fn target() u8 { const value = external(); return value; }",
        false,
        false,
        true,
    );
}

test "summary extraction keeps error-returning writes impure" {
    try expectSummaryBehavior(
        "var global: u8 = 0; fn target() !void { global = 1; return error.Failed; }",
        true,
        true,
        true,
    );
}

test "summary extraction keeps try success paths possible" {
    try expectSummaryBehavior(
        "extern fn external() anyerror!void; fn target() !void { try external(); }",
        true,
        false,
        true,
    );
}

test "summary extraction checks every conditional return outcome" {
    try expectSummaryBehavior(
        "fn target(fail: bool) !u8 { return if (fail) (error.Failed) else error.Other; }",
        true,
        true,
        false,
    );
    try expectSummaryBehavior(
        "fn target(fail: bool) !u8 { return if (fail) error.Failed else 1; }",
        true,
        false,
        false,
    );
}
