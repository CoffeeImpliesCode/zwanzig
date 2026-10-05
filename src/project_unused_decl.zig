const std = @import("std");
const compat = @import("compat.zig");
const ast_walk = @import("ast_walk.zig");
const call_resolver = @import("analysis/call_resolver.zig");
const diagnostic_mod = @import("diagnostic.zig");
const Diagnostic = diagnostic_mod.Diagnostic;
const LocationMapper = diagnostic_mod.LocationMapper;
const import_resolver = @import("analysis/import_resolver.zig");
const ProjectSources = @import("project_sources.zig").ProjectSources;
const ProjectReferenceIndex = @import("analysis/project_reference_index.zig").ProjectReferenceIndex;
const Source = @import("source.zig").Source;
const suppression = @import("suppression.zig");

const rule_id = "unused-decl";
const fieldAccessName = import_resolver.fieldAccessName;
const identifierName = import_resolver.identifierName;
const importPathFromBuiltinCall = import_resolver.importPathFromBuiltinCall;
const isVarDeclTag = import_resolver.isVarDeclTag;
const normalizeIdentifier = import_resolver.normalizeIdentifier;

const DeclKind = enum {
    function,
    type_decl,
    constant,
    variable,
    declaration,

    fn description(self: DeclKind) []const u8 {
        return switch (self) {
            .function => "Function",
            .type_decl => "Type",
            .constant => "Constant",
            .variable => "Variable",
            .declaration => "Declaration",
        };
    }
};

const FileInfo = struct {
    path: []const u8,
    tree: *const std.zig.Ast,
    suppressions: suppression.SuppressionMap,

    fn deinit(self: *FileInfo) void {
        self.suppressions.deinit();
    }
};

const DeclInfo = struct {
    file_index: usize,
    node_index: u32,
    name: []const u8,
    normalized_name: []const u8,
    byte_offset: usize,
    kind: DeclKind,

    fn deinit(self: *DeclInfo, allocator: std.mem.Allocator) void {
        allocator.free(self.name);
        allocator.free(self.normalized_name);
    }
};

const BuildReceiver = struct {
    name: []const u8,
    declaration_node: u32,
};

/// A module declaration in one analyzed build script. Node indices repeat
/// across build scripts, so the script a declaration came from is part of its
/// identity: without it one script's binding answers for another's.
const ModuleBinding = struct {
    build_file: usize,
    declaration: u32,
};

const ProjectContext = struct {
    allocator: std.mem.Allocator,
    files: []const import_resolver.File,
    build_file_indices: []const usize,
    path_index: ?*import_resolver.PathIndex,
    api_roots: std.ArrayList(usize) = .empty,
    public_api_files: std.ArrayList(usize) = .empty,
    api_root_membership: std.AutoHashMapUnmanaged(usize, void) = .empty,
    public_api_membership: std.AutoHashMapUnmanaged(usize, void) = .empty,
    /// Root source files each build-script module declaration binds to. A
    /// declaration whose root is a version-conditional selection binds more
    /// than one, because the branch this analyzer's frontend did not take
    /// still names a root the script compiles on the other one.
    build_modules: std.AutoHashMapUnmanaged(ModuleBinding, std.ArrayListUnmanaged(usize)) = .empty,
    references: ProjectReferenceIndex,

    fn init(
        allocator: std.mem.Allocator,
        files: []const import_resolver.File,
        build_file_indices: []const usize,
        path_index: ?*import_resolver.PathIndex,
    ) !ProjectContext {
        return .{
            .allocator = allocator,
            .files = files,
            .build_file_indices = build_file_indices,
            .path_index = path_index,
            .references = try ProjectReferenceIndex.init(allocator, files),
        };
    }

    fn deinit(self: *ProjectContext) void {
        self.references.deinit();
        self.public_api_membership.deinit(self.allocator);
        var modules = self.build_modules.valueIterator();
        while (modules.next()) |roots| roots.deinit(self.allocator);
        self.build_modules.deinit(self.allocator);
        self.api_root_membership.deinit(self.allocator);
        self.public_api_files.deinit(self.allocator);
        self.api_roots.deinit(self.allocator);
    }

    fn collectApiRoots(self: *ProjectContext) !void {
        for (self.build_file_indices) |file_index| {
            if (file_index >= self.files.len) continue;
            try self.collectBuildRootSourceFiles(file_index);
        }
    }

    /// Bind an import name to a module root the build script declares. The
    /// table is the one every import resolver shares, so `@import(name)`
    /// answers the same file here and in the type resolver.
    fn registerModuleName(self: *ProjectContext, name: []const u8, file_index: usize) !void {
        const path_index = self.path_index orelse return;
        try import_resolver.addModuleName(self.allocator, &path_index.module_names, name, file_index);
    }

    fn collectPublicApiFiles(self: *ProjectContext) !void {
        for (self.api_roots.items) |root_index| {
            try self.appendPublicApiFile(root_index);
        }

        var cursor: usize = 0;
        while (cursor < self.public_api_files.items.len) : (cursor += 1) {
            const importer_index = self.public_api_files.items[cursor];
            for (try self.references.publicTargets(importer_index)) |file_index| {
                try self.appendPublicApiFile(file_index);
            }
        }
    }

    fn isPublicApiFile(self: *const ProjectContext, file_index: usize) bool {
        return self.public_api_membership.contains(file_index);
    }

    fn appendApiRoot(self: *ProjectContext, file_index: usize) !void {
        const result = try self.api_root_membership.getOrPut(self.allocator, file_index);
        if (result.found_existing) return;
        try self.api_roots.append(self.allocator, file_index);
    }

    fn appendPublicApiFile(self: *ProjectContext, file_index: usize) !void {
        const result = try self.public_api_membership.getOrPut(self.allocator, file_index);
        if (result.found_existing) return;
        try self.public_api_files.append(self.allocator, file_index);
    }
    fn collectBuildRootSourceFiles(self: *ProjectContext, build_file_index: usize) !void {
        const build_file = self.files[build_file_index];
        const resolver = call_resolver.ProjectTypeResolver{
            .files = self.files,
            .file_index = build_file_index,
        };
        try self.collectBuildRootSourceFilesFromTree(
            build_file.tree,
            build_file.path,
            resolver,
        );
    }

    fn collectBuildRootSourceFilesFromTree(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
    ) !void {
        if (tree.errors.len != 0) return;
        const build_receiver = buildFunctionReceiver(tree, resolver) orelse return;
        const tags = tree.nodes.items(.tag);

        // A module declaration binds a variable to a root source file, and an
        // import registration names that binding rather than the file, so every
        // binding is read before any registration is.
        for (tags, 0..) |tag, node_index| {
            if (!import_resolver.isVarDeclTag(tag)) continue;
            const full = tree.fullVarDecl(@enumFromInt(node_index)) orelse continue;
            const init_node = full.ast.init_node.unwrap() orelse continue;
            var roots = try self.buildModuleRoots(
                tree,
                @intFromEnum(init_node),
                build_path,
                resolver,
                build_receiver,
            ) orelse continue;
            errdefer roots.deinit(self.allocator);
            try self.build_modules.put(self.allocator, .{
                .build_file = resolver.file_index,
                .declaration = @intCast(node_index),
            }, roots);
        }

        for (tags, 0..) |tag, node_index| {
            if (!call_resolver.isCallNode(tag)) continue;
            const call_node: u32 = @intCast(node_index);
            const method = buildCallMethod(tree, call_node) orelse continue;
            // Method names are runtime text, so each group is compared by name
            // rather than dispatched on.
            if (std.mem.eql(u8, method, "addModule") or std.mem.eql(u8, method, "createModule")) {
                var roots = try self.buildModuleRoots(
                    tree,
                    call_node,
                    build_path,
                    resolver,
                    build_receiver,
                ) orelse continue;
                defer roots.deinit(self.allocator);
                // `addModule` publishes the module under its own name, and a
                // published module is a package root. A name bound to more
                // than one candidate of a selection is recorded as ambiguous
                // rather than answered from one of them.
                if (moduleDeclaredName(tree, call_node)) |name| {
                    for (roots.items) |root_index| {
                        try self.appendApiRoot(root_index);
                        try self.registerModuleName(name, root_index);
                    }
                }
                for (roots.items) |root_index| {
                    try self.collectModuleImportNames(
                        tree,
                        call_node,
                        build_path,
                        resolver,
                        build_receiver,
                        root_index,
                    );
                }
            } else if (std.mem.eql(u8, method, "addImport")) {
                try self.collectBuildImportName(
                    tree,
                    call_node,
                    build_path,
                    resolver,
                    build_receiver,
                );
            } else if (isArtifactStepMethod(method)) {
                var roots = try self.artifactCompilationRoots(
                    tree,
                    call_node,
                    build_path,
                    resolver,
                    build_receiver,
                ) orelse continue;
                defer roots.deinit(self.allocator);
                for (roots.items) |root_index| {
                    try self.references.addCompilationRoot(root_index);
                }
            }
        }
    }

    /// Root source files a build script binds to the module this call
    /// creates. A `root_source_file` is usually the `b.path` call itself, but a
    /// script may bind it to a local first or pick between candidates with a
    /// comptime version conditional, and every candidate such an expression
    /// can produce roots that module: the script the analyzer reads has
    /// already resolved its own comptime choice, and the remaining branch is
    /// the root the other frontend compiles.
    fn buildModuleRoots(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        node: u32,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
        build_receiver: BuildReceiver,
    ) !?std.ArrayListUnmanaged(usize) {
        if (!isBuildMethodCall(tree, resolver, node, build_receiver)) return null;
        const method = buildCallMethod(tree, node) orelse return null;
        if (!std.mem.eql(u8, method, "addModule") and !std.mem.eql(u8, method, "createModule")) return null;
        const root_field = buildCallOption(tree, node, "root_source_file") orelse return null;
        return try self.rootFilesForPathExpression(tree, root_field, build_path, resolver, build_receiver);
    }

    /// File indexes a `root_source_file` expression names, in the order the
    /// expression produces them. A build script that selects its root through
    /// a comptime version conditional names one candidate per frontend, so
    /// neither candidate may be dropped for lack of a branch that survived
    /// comptime evaluation here.
    fn rootFilesForPathExpression(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        node: u32,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
        build_receiver: BuildReceiver,
    ) !?std.ArrayListUnmanaged(usize) {
        var literals: std.ArrayListUnmanaged([]const u8) = .empty;
        defer literals.deinit(self.allocator);
        try collectRootPathLiterals(
            self.allocator,
            tree,
            resolver,
            node,
            build_receiver,
            0,
            &literals,
        );

        var roots: std.ArrayListUnmanaged(usize) = .empty;
        errdefer roots.deinit(self.allocator);
        for (literals.items) |root_path| {
            const root_index = import_resolver.resolveImportToFileIndex(self.files, build_path, root_path) orelse continue;
            if (std.mem.indexOfScalar(usize, roots.items, root_index) != null) continue;
            try roots.append(self.allocator, root_index);
        }
        if (roots.items.len == 0) return null;
        return roots;
    }

    /// Root modules an artifact step compiles. They are the files
    /// `@import("root")` names for every file of that compilation unit, so a
    /// separately named module reaches a checker the compilation root
    /// supplies.
    fn artifactCompilationRoots(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        node: u32,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
        build_receiver: BuildReceiver,
    ) !?std.ArrayListUnmanaged(usize) {
        if (!isBuildMethodCall(tree, resolver, node, build_receiver)) return null;
        const root_module = buildCallOption(tree, node, "root_module") orelse return null;
        return try self.moduleRootFiles(tree, root_module, build_path, resolver, build_receiver, 0);
    }

    /// Root source files a module expression binds: the variable a module
    /// declaration created, the expression that variable was initialized
    /// from, either arm of a conditional that selects between modules, an
    /// inline module call, or an options struct that names its own root source
    /// file. A binding the module walk never recorded still names the module it
    /// was initialized from, so a script that spells that module through any
    /// other expression answers the same roots here.
    fn moduleRootFiles(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        node: u32,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
        build_receiver: BuildReceiver,
        depth: u32,
    ) !?std.ArrayListUnmanaged(usize) {
        if (depth >= root_path_depth_limit) return null;
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return null;
        if (tags[node] == .identifier) {
            const declaration = resolver.resolveDeclarationNode(node) orelse return null;
            if (self.build_modules.get(.{
                .build_file = resolver.file_index,
                .declaration = declaration,
            })) |bound| {
                var roots: std.ArrayListUnmanaged(usize) = .empty;
                errdefer roots.deinit(self.allocator);
                try roots.appendSlice(self.allocator, bound.items);
                return roots;
            }
            const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return null;
            const init_node = full.ast.init_node.unwrap() orelse return null;
            return try self.moduleRootFiles(
                tree,
                @intFromEnum(init_node),
                build_path,
                resolver,
                build_receiver,
                depth + 1,
            );
        }
        // A conditional selects one module per frontend, and the branch this
        // analyzer's frontend did not take still names a root the other one
        // compiles, so both arms belong to the artifact.
        if (tree.fullIf(@enumFromInt(node))) |full| {
            var roots: std.ArrayListUnmanaged(usize) = .empty;
            errdefer roots.deinit(self.allocator);
            const then_roots = try self.moduleRootFiles(
                tree,
                @intFromEnum(full.ast.then_expr),
                build_path,
                resolver,
                build_receiver,
                depth + 1,
            );
            try mergeModuleRoots(self.allocator, &roots, then_roots);
            if (full.ast.else_expr.unwrap()) |alternative| {
                const else_roots = try self.moduleRootFiles(
                    tree,
                    @intFromEnum(alternative),
                    build_path,
                    resolver,
                    build_receiver,
                    depth + 1,
                );
                try mergeModuleRoots(self.allocator, &roots, else_roots);
            }
            if (roots.items.len == 0) return null;
            return roots;
        }
        if (try self.buildModuleRoots(tree, node, build_path, resolver, build_receiver)) |roots| return roots;
        const root_field = structInitOption(tree, node, "root_source_file") orelse return null;
        return try self.rootFilesForPathExpression(tree, root_field, build_path, resolver, build_receiver);
    }

    /// One root of a module expression, for the registrations that name a
    /// single module. A selection that names more than one has no single
    /// module to name, so those registrations stay unresolved.
    fn moduleRootFile(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        node: u32,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
        build_receiver: BuildReceiver,
    ) !?usize {
        var roots = try self.moduleRootFiles(tree, node, build_path, resolver, build_receiver, 0) orelse return null;
        defer roots.deinit(self.allocator);
        if (roots.items.len != 1) return null;
        return roots.items[0];
    }

    /// `module.addImport("name", module)` publishes the module bound to the
    /// second argument, so `@import("name")` in an analyzed source file names
    /// that root. A name no registration reaches stays unresolved.
    fn collectBuildImportName(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        node: u32,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
        build_receiver: BuildReceiver,
    ) !void {
        const tags = tree.nodes.items(.tag);
        if (node >= tags.len) return;

        var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return;
        if (call.ast.params.len != 2) return;
        const callee = @intFromEnum(call.ast.fn_expr);
        if (callee >= tags.len or tags[callee] != .field_access) return;

        const name = stringLiteralSlice(tree, @intFromEnum(call.ast.params[0])) orelse return;
        const root_index = try self.moduleRootFile(
            tree,
            @intFromEnum(call.ast.params[1]),
            build_path,
            resolver,
            build_receiver,
        ) orelse return;
        try self.registerModuleName(name, root_index);

        // The receiver names the module whose import table the name joins, and
        // that edge is what places the named module inside a compilation unit.
        const receiver = @intFromEnum(tree.nodes.items(.data)[callee].node_and_token[0]);
        const module_index = try self.moduleRootFile(
            tree,
            receiver,
            build_path,
            resolver,
            build_receiver,
        ) orelse return;
        try self.references.addModuleImport(module_index, root_index);
    }

    /// `.imports = &.{.{ .name = "seam", .module = seam }}` binds each name for
    /// every file of the module the call creates, so `@import("name")` reaches
    /// the named root and a compilation root walk reaches it too.
    fn collectModuleImportNames(
        self: *ProjectContext,
        tree: *const std.zig.Ast,
        node: u32,
        build_path: []const u8,
        resolver: call_resolver.ProjectTypeResolver,
        build_receiver: BuildReceiver,
        module_index: usize,
    ) !void {
        const imports_field = buildCallOption(tree, node, "imports") orelse return;
        var buffer: [2]std.zig.Ast.Node.Index = undefined;
        for (arrayInitElements(tree, &buffer, imports_field)) |entry_node| {
            const name_node = structInitOption(tree, @intFromEnum(entry_node), "name") orelse continue;
            const name = stringLiteralSlice(tree, name_node) orelse continue;
            const module_node = structInitOption(tree, @intFromEnum(entry_node), "module") orelse continue;
            const root_index = try self.moduleRootFile(
                tree,
                module_node,
                build_path,
                resolver,
                build_receiver,
            ) orelse continue;
            try self.references.addModuleImport(module_index, root_index);
            try self.registerModuleName(name, root_index);
        }
    }
};

/// Append roots one module expression produced to the roots collected so far,
/// keeping each root once. An expression that names no root contributes
/// nothing rather than ending the whole selection.
fn mergeModuleRoots(
    allocator: std.mem.Allocator,
    into: *std.ArrayListUnmanaged(usize),
    from: ?std.ArrayListUnmanaged(usize),
) error{OutOfMemory}!void {
    var roots = from orelse return;
    defer roots.deinit(allocator);
    for (roots.items) |root_index| {
        if (std.mem.indexOfScalar(usize, into.items, root_index) != null) continue;
        try into.append(allocator, root_index);
    }
}

/// Methods a build script uses to compile an artifact. Each one compiles its
/// root module, so every file that module graph reaches resolves
/// `@import("root")` to it.
const artifact_step_methods = [_][]const u8{
    "addExecutable",
    "addObject",
    "addLibrary",
    "addStaticLibrary",
    "addSharedLibrary",
    "addTest",
};

fn isArtifactStepMethod(method: []const u8) bool {
    for (artifact_step_methods) |name| {
        if (std.mem.eql(u8, method, name)) return true;
    }
    return false;
}

fn buildFunctionReceiver(
    tree: *const std.zig.Ast,
    resolver: call_resolver.ProjectTypeResolver,
) ?BuildReceiver {
    const tags = tree.nodes.items(.tag);
    var proto_buffer: [1]std.zig.Ast.Node.Index = undefined;

    for (tree.rootDecls()) |decl_idx| {
        const node = @intFromEnum(decl_idx);
        if (node >= tags.len or tags[node] != .fn_decl) continue;

        const proto = tree.fullFnProto(&proto_buffer, decl_idx) orelse continue;
        if (!isPubToken(tree, proto.visib_token)) continue;

        const name_token = proto.name_token orelse continue;
        if (!std.mem.eql(u8, tree.tokenSlice(name_token), "build")) continue;
        var params = proto.iterate(tree);
        const parameter = params.next() orelse return null;
        const type_node = parameter.type_expr orelse return null;
        if (!parameterIsStdBuild(tree, @intFromEnum(type_node), resolver)) return null;
        const parameter_token = parameter.name_token orelse return null;
        if (parameter_token >= tree.tokens.len or tree.tokenTag(parameter_token) != .identifier) return null;
        return .{
            .name = import_resolver.normalizeIdentifier(tree.tokenSlice(parameter_token)),
            .declaration_node = @intFromEnum(type_node),
        };
    }
    return null;
}

fn parameterIsStdBuild(
    tree: *const std.zig.Ast,
    type_node: u32,
    resolver: call_resolver.ProjectTypeResolver,
) bool {
    const tags = tree.nodes.items(.tag);
    var node = type_node;
    if (node >= tags.len) return false;

    switch (tags[node]) {
        .ptr_type,
        .ptr_type_aligned,
        .ptr_type_sentinel,
        .ptr_type_bit_range,
        => {
            const pointer = tree.fullPtrType(@enumFromInt(node)) orelse return false;
            node = @intFromEnum(pointer.ast.child_type);
            if (node >= tags.len) return false;
        },
        else => return false,
    }

    if (tags[node] != .field_access) return false;
    const access = tree.nodes.items(.data)[node].node_and_token;
    const namespace = @intFromEnum(access[0]);
    if (namespace >= tags.len or tags[namespace] != .identifier) return false;
    const namespace_token = tree.nodes.items(.main_token)[namespace];
    if (namespace_token >= tree.tokens.len or tree.tokenTag(namespace_token) != .identifier) return false;
    if (!resolver.isVerifiedImportBinding(namespace, "std")) return false;
    if (access[1] >= tree.tokens.len or tree.tokenTag(access[1]) != .identifier) return false;
    return std.mem.eql(u8, tree.tokenSlice(access[1]), "Build");
}

fn isBuildMethodCall(
    tree: *const std.zig.Ast,
    resolver: call_resolver.ProjectTypeResolver,
    node: u32,
    expected_receiver: BuildReceiver,
) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;

    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return false;
    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return false;

    const access = tree.nodes.items(.data)[callee].node_and_token;
    const receiver = @intFromEnum(access[0]);
    if (receiver >= tags.len or tags[receiver] != .identifier) return false;
    const main_token = tree.nodes.items(.main_token)[receiver];
    if (main_token >= tree.tokens.len or tree.tokenTag(main_token) != .identifier) return false;
    if (!std.mem.eql(u8, import_resolver.normalizeIdentifier(tree.tokenSlice(main_token)), expected_receiver.name)) return false;
    const declaration_node = resolver.resolveDeclarationNode(receiver) orelse return false;
    return declaration_node == expected_receiver.declaration_node;
}

/// Method a build-script call invokes, when it invokes one on a field.
fn buildCallMethod(tree: *const std.zig.Ast, node: u32) ?[]const u8 {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return null;

    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return null;
    const callee = @intFromEnum(call.ast.fn_expr);
    if (callee >= tags.len or tags[callee] != .field_access) return null;
    return tree.tokenSlice(tree.nodes.items(.data)[callee].node_and_token[1]);
}

/// Value a build-script call assigns to one field of its options struct.
fn buildCallOption(tree: *const std.zig.Ast, node: u32, field_name: []const u8) ?u32 {
    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return null;
    for (call.ast.params) |param_node| {
        if (structInitOption(tree, @intFromEnum(param_node), field_name)) |value| return value;
    }
    return null;
}

/// Value a struct literal assigns to one named field.
fn structInitOption(tree: *const std.zig.Ast, node: u32, field_name: []const u8) ?u32 {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return null;

    var struct_buffer: [2]std.zig.Ast.Node.Index = undefined;
    const struct_init = tree.fullStructInit(&struct_buffer, @enumFromInt(node)) orelse return null;
    for (struct_init.ast.fields) |field_node| {
        const field = structInitFieldName(tree, field_node) orelse continue;
        if (std.mem.eql(u8, field, field_name)) return @intFromEnum(field_node);
    }
    return null;
}

/// Elements an array literal holds. The buffer outlives the walk, because a
/// short array literal stores its elements there instead of in the AST. A
/// module import table is written as a pointer to that literal, so the
/// address-of wrapper is stepped through before the literal is read.
fn arrayInitElements(
    tree: *const std.zig.Ast,
    buffer: *[2]std.zig.Ast.Node.Index,
    node: u32,
) []const std.zig.Ast.Node.Index {
    const tags = tree.nodes.items(.tag);
    var literal = node;
    while (literal < tags.len and tags[literal] == .address_of) {
        literal = @intFromEnum(tree.nodes.items(.data)[literal].node);
    }
    if (literal >= tags.len) return &.{};
    const array_init = tree.fullArrayInit(buffer, @enumFromInt(literal)) orelse return &.{};
    return array_init.ast.elements;
}

fn structInitFieldName(tree: *const std.zig.Ast, value: std.zig.Ast.Node.Index) ?[]const u8 {
    const first = tree.firstToken(value);
    if (first < 3) return null;
    if (tree.tokenTag(first - 1) != .equal or tree.tokenTag(first - 2) != .identifier or tree.tokenTag(first - 3) != .period) return null;
    return import_resolver.normalizeIdentifier(tree.tokenSlice(first - 2));
}

/// Levels a `root_source_file` expression may reach before a `b.path` call. A
/// root selection is a local chain or a version conditional rather than an
/// unbounded expression, so the bound stops a self-referential binding chain
/// instead of recursing forever.
const root_path_depth_limit: u32 = 32;

/// Every `b.path("...")` literal a `root_source_file` expression can produce.
/// A build script may write the call inline, bind it to a local, or pick
/// between candidates with a comptime version conditional, so the walk follows
/// local bindings and both arms of a conditional rather than requiring the
/// call itself. Literals borrow the build script's source and are reported in
/// first-seen order, so the same path is never collected twice.
fn collectRootPathLiterals(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    resolver: call_resolver.ProjectTypeResolver,
    node: u32,
    receiver: BuildReceiver,
    depth: u32,
    literals: *std.ArrayListUnmanaged([]const u8),
) error{OutOfMemory}!void {
    if (depth >= root_path_depth_limit) return;
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return;

    if (tree.fullIf(@enumFromInt(node))) |full| {
        try collectRootPathLiterals(
            allocator,
            tree,
            resolver,
            @intFromEnum(full.ast.then_expr),
            receiver,
            depth + 1,
            literals,
        );
        if (full.ast.else_expr.unwrap()) |alternative| {
            try collectRootPathLiterals(
                allocator,
                tree,
                resolver,
                @intFromEnum(alternative),
                receiver,
                depth + 1,
                literals,
            );
        }
        return;
    }

    if (tags[node] == .identifier) {
        const declaration = resolver.resolveDeclarationNode(node) orelse return;
        const full = tree.fullVarDecl(@enumFromInt(declaration)) orelse return;
        const init_node = full.ast.init_node.unwrap() orelse return;
        try collectRootPathLiterals(
            allocator,
            tree,
            resolver,
            @intFromEnum(init_node),
            receiver,
            depth + 1,
            literals,
        );
        return;
    }

    if (isBuildMethodCall(tree, resolver, node, receiver) and
        std.mem.eql(u8, buildCallMethod(tree, node) orelse "", "path"))
    {
        var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
        const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return;
        if (call.ast.params.len != 1) return;
        const literal = stringLiteralSlice(tree, @intFromEnum(call.ast.params[0])) orelse return;
        for (literals.items) |existing| {
            if (std.mem.eql(u8, existing, literal)) return;
        }
        try literals.append(allocator, literal);
        return;
    }

    var children = RootPathChildren{ .allocator = allocator, .tree = tree, .resolver = resolver, .receiver = receiver, .depth = depth, .literals = literals };
    ast_walk.walkChildren(RootPathChildren, tree, node, &children, RootPathChildren.visit) catch return;
}

/// Walks the remaining shapes of a root expression: anything that is neither a
/// `b.path` call, a local binding, nor a conditional still names its candidate
/// somewhere below it, so every child is offered to the collector.
const RootPathChildren = struct {
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    resolver: call_resolver.ProjectTypeResolver,
    receiver: BuildReceiver,
    depth: u32,
    literals: *std.ArrayListUnmanaged([]const u8),

    fn visit(_: *const std.zig.Ast, node: u32, self: *RootPathChildren) !void {
        try collectRootPathLiterals(
            self.allocator,
            self.tree,
            self.resolver,
            node,
            self.receiver,
            self.depth + 1,
            self.literals,
        );
    }
};

/// Name `addModule` publishes the module under. `createModule` takes no such
/// parameter, so a module it creates stays unpublished.
fn moduleDeclaredName(tree: *const std.zig.Ast, node: u32) ?[]const u8 {
    if (!std.mem.eql(u8, buildCallMethod(tree, node) orelse return null, "addModule")) return null;

    var call_buffer: [1]std.zig.Ast.Node.Index = undefined;
    const call = tree.fullCall(&call_buffer, @enumFromInt(node)) orelse return null;
    if (call.ast.params.len == 0) return null;
    return stringLiteralSlice(tree, @intFromEnum(call.ast.params[0]));
}

/// Text of a string literal node, without its surrounding quotes.
fn stringLiteralSlice(tree: *const std.zig.Ast, node: u32) ?[]const u8 {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len or tags[node] != .string_literal) return null;
    const main_token = tree.nodes.items(.main_token)[node];
    const token_tags = tree.tokens.items(.tag);
    if (main_token >= token_tags.len or token_tags[main_token] != .string_literal) return null;
    const literal = tree.tokenSlice(main_token);
    if (literal.len < 2) return null;
    return literal[1 .. literal.len - 1];
}

fn isSelectedSource(diagnostic_indices: []const usize, index: usize) bool {
    for (diagnostic_indices) |selected| {
        if (selected == index) return true;
    }
    return false;
}

/// Report the syntax errors of a project file that the per-file analysis pass
/// never diagnoses. Build context is only read by this pass, so without a
/// diagnostic a build script that does not parse would silently remove
/// project-wide dead-code detection from an otherwise successful run.
fn appendContextParseErrors(
    allocator: std.mem.Allocator,
    diagnostics: *std.ArrayList(Diagnostic),
    file: import_resolver.File,
) !void {
    var mapper = try LocationMapper.init(allocator, file.tree.source);
    defer mapper.deinit();
    var message: std.Io.Writer.Allocating = .init(allocator);
    defer message.deinit();
    for (file.tree.errors) |parse_error| {
        message.writer.end = 0;
        file.tree.renderError(parse_error, &message.writer) catch return error.OutOfMemory;
        const offset = file.tree.tokens.items(.start)[parse_error.token] + file.tree.errorOffset(parse_error);
        const location = mapper.byteToLocation(offset);
        var diagnostic = try Diagnostic.initAtLocation(
            allocator,
            file.path,
            "parse-error",
            if (parse_error.is_note) .hint else .err,
            message.written(),
            location.line,
            location.column,
        );
        errdefer diagnostic.deinit(allocator);
        try diagnostics.append(allocator, diagnostic);
    }
}

pub fn analyze(
    project_sources: *const ProjectSources,
    allocator: std.mem.Allocator,
    diagnostics: *std.ArrayList(Diagnostic),
) !void {
    const resolver_files = project_sources.files();
    const diagnostic_indices = project_sources.diagnosticFileIndices();
    if (diagnostic_indices.len < 2) return;
    // Incomplete syntax cannot prove the absence of cross-file references.
    // Selected sources already reported their own parse errors, so only the
    // build context this pass depends on needs a diagnostic here.
    var incomplete = false;
    for (resolver_files, 0..) |file, index| {
        if (file.tree.errors.len == 0) continue;
        incomplete = true;
        if (isSelectedSource(diagnostic_indices, index)) continue;
        try appendContextParseErrors(allocator, diagnostics, file);
    }
    if (incomplete) return;

    const files = try allocator.alloc(FileInfo, resolver_files.len);
    var file_count: usize = 0;
    defer {
        for (files[0..file_count]) |*file| file.deinit();
        allocator.free(files);
    }

    for (resolver_files) |file| {
        const suppressions = try suppression.parseSuppressions(allocator, file.tree.source);
        files[file_count] = .{
            .path = file.path,
            .tree = file.tree,
            .suppressions = suppressions,
        };
        file_count += 1;
    }

    var project = try ProjectContext.init(
        allocator,
        resolver_files,
        project_sources.buildFileIndices(),
        project_sources.path_index,
    );
    defer project.deinit();
    try project.collectApiRoots();
    try project.collectPublicApiFiles();

    var decls: std.ArrayList(DeclInfo) = .empty;
    defer {
        for (decls.items) |*decl| decl.deinit(allocator);
        decls.deinit(allocator);
    }

    for (diagnostic_indices) |file_index| {
        if (file_index >= files.len) continue;
        const file = files[file_index];
        if (project.isPublicApiFile(file_index)) continue;
        try collectPublicRootDecls(allocator, file.tree, file.path, file_index, &decls);
    }

    const used = try collectProjectUsedDecls(
        allocator,
        files,
        resolver_files,
        decls.items,
        &project.references,
    );
    defer allocator.free(used);

    for (decls.items, 0..) |decl, decl_index| {
        if (used[decl_index]) continue;
        const file = files[decl.file_index];
        var source = Source.initParsed(allocator, file.path, file.tree);
        defer source.deinit();
        const range = try source.byteRangeToSourceRange(
            decl.byte_offset,
            decl.byte_offset + decl.name.len,
        );

        if (file.suppressions.isSuppressed(range.start.line, rule_id)) continue;

        const message = try std.fmt.allocPrint(
            allocator,
            "{s} '{s}' is never used by another analyzed file",
            .{ decl.kind.description(), decl.name },
        );
        defer allocator.free(message);

        var diag = try Diagnostic.init(
            allocator,
            file.path,
            rule_id,
            .warning,
            message,
            range,
        );
        errdefer diag.deinit(allocator);
        try diagnostics.append(allocator, diag);
    }
}

fn collectPublicRootDecls(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    path: []const u8,
    file_index: usize,
    decls: *std.ArrayList(DeclInfo),
) !void {
    if (tree.errors.len != 0) return;
    const tags = tree.nodes.items(.tag);
    const token_starts = tree.tokens.items(.start);

    for (tree.rootDecls()) |decl_idx| {
        const idx = @intFromEnum(decl_idx);
        const info = switch (tags[idx]) {
            .simple_var_decl,
            .aligned_var_decl,
            .global_var_decl,
            => try extractPublicVarDecl(allocator, tree, @intCast(idx), token_starts, file_index),
            .fn_decl,
            .fn_proto,
            .fn_proto_simple,
            .fn_proto_one,
            .fn_proto_multi,
            => try extractPublicFnDecl(allocator, tree, @intCast(idx), token_starts, file_index),
            else => null,
        };

        if (info) |decl| {
            if (isIgnoredPublicDecl(path, decl.name)) {
                var mutable_decl = decl;
                mutable_decl.deinit(allocator);
                continue;
            }
            var mutable_decl = decl;
            errdefer mutable_decl.deinit(allocator);
            try decls.append(allocator, mutable_decl);
        }
    }
}

fn extractPublicVarDecl(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    node_idx: u32,
    token_starts: []const u32,
    file_index: usize,
) !?DeclInfo {
    const full = tree.fullVarDecl(@enumFromInt(node_idx)) orelse return null;
    if (!isPubToken(tree, full.visib_token)) return null;
    if (full.extern_export_token != null) return null;
    if (isPublicAliasDecl(tree, full)) return null;

    const token_tags = tree.tokens.items(.tag);
    const name_token = full.ast.mut_token + 1;
    if (name_token >= token_tags.len) return null;
    if (token_tags[name_token] != .identifier) return null;

    const name = tree.tokenSlice(name_token);
    return try makeDeclInfo(
        allocator,
        file_index,
        node_idx,
        name,
        token_starts[name_token],
        classifyVarDecl(tree, full),
    );
}

fn extractPublicFnDecl(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    node_idx: u32,
    token_starts: []const u32,
    file_index: usize,
) !?DeclInfo {
    const tags = tree.nodes.items(.tag);
    const tag = tags[node_idx];
    var buffer: [1]std.zig.Ast.Node.Index = undefined;

    return switch (tag) {
        .fn_decl => blk: {
            const data = tree.nodes.items(.data)[node_idx];
            const proto_node = @intFromEnum(data.node_and_node[0]);
            break :blk extractPublicFnDecl(allocator, tree, proto_node, token_starts, file_index);
        },
        .fn_proto => extractPublicFnProto(
            allocator,
            tree,
            node_idx,
            tree.fnProto(@enumFromInt(node_idx)),
            token_starts,
            file_index,
        ),
        .fn_proto_simple => extractPublicFnProto(
            allocator,
            tree,
            node_idx,
            tree.fnProtoSimple(&buffer, @enumFromInt(node_idx)),
            token_starts,
            file_index,
        ),
        .fn_proto_one => extractPublicFnProto(
            allocator,
            tree,
            node_idx,
            tree.fnProtoOne(&buffer, @enumFromInt(node_idx)),
            token_starts,
            file_index,
        ),
        .fn_proto_multi => extractPublicFnProto(
            allocator,
            tree,
            node_idx,
            tree.fnProtoMulti(@enumFromInt(node_idx)),
            token_starts,
            file_index,
        ),
        else => null,
    };
}

fn extractPublicFnProto(
    allocator: std.mem.Allocator,
    tree: *const std.zig.Ast,
    node_idx: u32,
    proto: std.zig.Ast.full.FnProto,
    token_starts: []const u32,
    file_index: usize,
) !?DeclInfo {
    if (!isPubToken(tree, proto.visib_token)) return null;
    if (proto.extern_export_inline_token) |tok| {
        const tag = tree.tokenTag(tok);
        if (tag == .keyword_extern or tag == .keyword_export) return null;
    }

    const name_token = proto.name_token orelse return null;
    if (tree.tokenTag(name_token) != .identifier) return null;

    return try makeDeclInfo(
        allocator,
        file_index,
        node_idx,
        tree.tokenSlice(name_token),
        token_starts[name_token],
        .function,
    );
}

fn makeDeclInfo(
    allocator: std.mem.Allocator,
    file_index: usize,
    node_index: u32,
    name: []const u8,
    byte_offset: usize,
    kind: DeclKind,
) !DeclInfo {
    const name_copy = try allocator.dupe(u8, name);
    errdefer allocator.free(name_copy);
    const normalized_copy = try allocator.dupe(u8, normalizeIdentifier(name));
    return .{
        .file_index = file_index,
        .node_index = node_index,
        .name = name_copy,
        .normalized_name = normalized_copy,
        .byte_offset = byte_offset,
        .kind = kind,
    };
}

fn isPubToken(tree: *const std.zig.Ast, token: ?std.zig.Ast.TokenIndex) bool {
    const tok = token orelse return false;
    return tree.tokenTag(tok) == .keyword_pub;
}

fn isPublicAliasDecl(tree: *const std.zig.Ast, full: std.zig.Ast.full.VarDecl) bool {
    if (tree.tokenTag(full.ast.mut_token) != .keyword_const) return false;

    const init_node = full.ast.init_node.unwrap() orelse return false;
    const init_idx = @intFromEnum(init_node);
    const tags = tree.nodes.items(.tag);
    if (init_idx >= tags.len) return false;

    const name_token = full.ast.mut_token + 1;
    if (name_token >= tree.tokens.len or tree.tokenTag(name_token) != .identifier) return false;
    const public_name = tree.tokenSlice(name_token);

    return switch (tags[init_idx]) {
        .identifier => isReexportAlias(public_name, identifierName(tree, init_idx) orelse return false),
        .field_access => isReexportAlias(public_name, fieldAccessName(tree, init_idx) orelse return false),
        .builtin_call,
        .builtin_call_comma,
        .builtin_call_two,
        .builtin_call_two_comma,
        => isImportBuiltinCall(tree, init_idx),
        else => false,
    };
}

fn isImportBuiltinCall(tree: *const std.zig.Ast, node_idx: usize) bool {
    return importPathFromBuiltinCall(tree, node_idx) != null;
}

fn classifyVarDecl(tree: *const std.zig.Ast, full: std.zig.Ast.full.VarDecl) DeclKind {
    if (full.ast.init_node.unwrap()) |init_node| {
        const tag = tree.nodes.items(.tag)[@intFromEnum(init_node)];
        if (isContainerTag(tag) or tag == .error_set_decl) return .type_decl;
    }
    const mut_tag = tree.tokenTag(full.ast.mut_token);
    if (mut_tag == .keyword_const) return .constant;
    if (mut_tag == .keyword_var) return .variable;
    return .declaration;
}

fn collectProjectUsedDecls(
    allocator: std.mem.Allocator,
    files: []const FileInfo,
    resolver_files: []const import_resolver.File,
    decls: []const DeclInfo,
    references: *ProjectReferenceIndex,
) ![]bool {
    const used = try allocator.alloc(bool, decls.len);
    errdefer allocator.free(used);
    @memset(used, false);
    var usage = DeclUsage{ .allocator = allocator, .decls = decls, .used = used };
    defer usage.deinit();
    for (decls, 0..) |decl, decl_index| {
        const result = try usage.by_name.getOrPut(allocator, decl.normalized_name);
        if (!result.found_existing) result.value_ptr.* = .empty;
        try result.value_ptr.append(allocator, decl_index);
    }

    for (resolver_files, 0..) |file, file_index| {
        try usage.scanFile(resolver_files, file, file_index, references);
    }
    var cursor: usize = 0;
    while (cursor < usage.queue.items.len) : (cursor += 1) {
        const decl = decls[usage.queue.items[cursor]];
        var scanner = PublicSurfaceScanner{
            .tree = files[decl.file_index].tree,
            .usage = &usage,
            .file_index = decl.file_index,
        };
        try scanner.scanDecl(decl.node_index);
    }
    return used;
}

const DeclUsage = struct {
    allocator: std.mem.Allocator,
    decls: []const DeclInfo,
    used: []bool,
    by_name: std.StringHashMapUnmanaged(std.ArrayList(usize)) = .empty,
    queue: std.ArrayList(usize) = .empty,

    fn deinit(self: *DeclUsage) void {
        var values = self.by_name.valueIterator();
        while (values.next()) |value| value.deinit(self.allocator);
        self.by_name.deinit(self.allocator);
        self.queue.deinit(self.allocator);
    }

    fn mark(self: *DeclUsage, declaration: usize) !void {
        if (self.used[declaration]) return;
        try self.queue.append(self.allocator, declaration);
        self.used[declaration] = true;
    }

    fn hasUnused(self: *const DeclUsage, candidates: []const usize) bool {
        for (candidates) |candidate| {
            if (!self.used[candidate]) return true;
        }
        return false;
    }

    fn scanFile(
        self: *DeclUsage,
        files: []const import_resolver.File,
        file: import_resolver.File,
        file_index: usize,
        references: *ProjectReferenceIndex,
    ) !void {
        const tree = file.tree;
        if (tree.errors.len != 0) return;
        const resolver = call_resolver.ProjectTypeResolver{ .files = files, .file_index = file_index };
        // Every reference index answer is queried where it is read: the entry
        // table grows while this loop asks for namespace targets, so an answer
        // held across the loop would point at storage that has moved.
        for (tree.nodes.items(.tag), 0..) |tag, node| {
            switch (tag) {
                .identifier => {
                    const name = identifierName(tree, node) orelse continue;
                    const candidates = self.by_name.get(name) orelse continue;
                    for (candidates.items) |candidate| {
                        const decl = self.decls[candidate];
                        if (decl.file_index == file_index) {
                            if (node != decl.node_index) try self.mark(candidate);
                        } else if (!std.mem.eql(u8, file.path, files[decl.file_index].path) and
                            std.mem.indexOfScalar(usize, try references.usingTargets(file_index), decl.file_index) != null)
                        {
                            try self.mark(candidate);
                        }
                    }
                },
                .field_access => {
                    const name = fieldAccessName(tree, node) orelse continue;
                    const candidates = self.by_name.get(name) orelse continue;
                    if (!self.hasUnused(candidates.items)) continue;
                    const receiver = @intFromEnum(tree.nodes.items(.data)[node].node_and_token[0]);
                    const targets = try references.namespaceTargets(file_index, receiver);
                    const receiver_type = resolver.resolveExprType(receiver);
                    for (candidates.items) |candidate| {
                        const decl = self.decls[candidate];
                        // A declaration this file owns is not a cross-file
                        // reference, and equal paths already mean equal
                        // indices, so a candidate in another file is never
                        // skipped here.
                        if (receiver_type) |actual| {
                            if (actual.file_index == decl.file_index and actual.container_node == null) {
                                try self.mark(candidate);
                                continue;
                            }
                        }
                        if (decl.file_index != file_index and std.mem.indexOfScalar(usize, targets, decl.file_index) != null) {
                            try self.mark(candidate);
                        }
                    }
                },
                .enum_literal => {
                    const name = normalizeIdentifier(tree.tokenSlice(tree.nodes.items(.main_token)[node]));
                    const candidates = self.by_name.get(name) orelse continue;
                    if (!self.hasUnused(candidates.items)) continue;
                    const expected = resolver.resolveResultLocationTypeNode(@intCast(node)) orelse continue;
                    const owner_resolver = call_resolver.ProjectTypeResolver{
                        .files = files,
                        .file_index = expected.file_index,
                    };
                    const owner = owner_resolver.resolveTypeNode(expected.node_index) orelse continue;
                    if (owner.container_node != null) continue;
                    for (candidates.items) |candidate| {
                        const decl = self.decls[candidate];
                        if (decl.file_index != owner.file_index) continue;
                        if (decl.file_index != file_index and std.mem.eql(u8, file.path, files[decl.file_index].path)) continue;
                        try self.mark(candidate);
                    }
                },
                .simple_var_decl, .aligned_var_decl, .global_var_decl, .local_var_decl => {
                    const full = tree.fullVarDecl(@enumFromInt(node)) orelse continue;
                    const initializer = full.ast.init_node.unwrap() orelse continue;
                    const name = implicitResultMethodName(tree, @intFromEnum(initializer)) orelse continue;
                    const candidates = self.by_name.get(name) orelse continue;
                    if (!self.hasUnused(candidates.items)) continue;
                    for (candidates.items) |candidate| {
                        const decl = self.decls[candidate];
                        if (decl.file_index != file_index and std.mem.eql(u8, file.path, files[decl.file_index].path)) continue;
                        if (resolver.varDeclInitializerReferencesExpectedTypeMethod(full, decl.file_index, name)) {
                            try self.mark(candidate);
                        }
                    }
                },
                else => {},
            }
        }
    }
};

fn implicitResultMethodName(tree: *const std.zig.Ast, initial: u32) ?[]const u8 {
    var node = initial;
    while (node < tree.nodes.len) {
        const data = tree.nodes.items(.data)[node];
        switch (tree.nodes.items(.tag)[node]) {
            .call, .call_comma, .call_one, .call_one_comma => {
                var buffer: [1]std.zig.Ast.Node.Index = undefined;
                const call = tree.fullCall(&buffer, @enumFromInt(node)) orelse return null;
                const callee = @intFromEnum(call.ast.fn_expr);
                if (callee >= tree.nodes.len or tree.nodes.items(.tag)[callee] != .enum_literal) return null;
                return normalizeIdentifier(tree.tokenSlice(tree.nodes.items(.main_token)[callee]));
            },
            .@"try", .address_of, .deref, .optional_type => node = @intFromEnum(data.node),
            .grouped_expression, .unwrap_optional => node = @intFromEnum(data.node_and_token[0]),
            .@"catch" => node = @intFromEnum(data.node_and_node[0]),
            else => return null,
        }
    }
    return null;
}

const PublicSurfaceScanner = struct {
    tree: *const std.zig.Ast,
    usage: *DeclUsage,
    file_index: usize,
    stop: bool = false,

    fn scanDecl(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const tags = self.tree.nodes.items(.tag);
        if (node >= tags.len) return;

        switch (tags[node]) {
            .simple_var_decl,
            .aligned_var_decl,
            .global_var_decl,
            => try self.scanVarDeclSurface(node),
            .fn_decl => {
                const data = self.tree.nodes.items(.data)[node];
                try self.scanFnProto(@intFromEnum(data.node_and_node[0]));
            },
            .fn_proto,
            .fn_proto_simple,
            .fn_proto_one,
            .fn_proto_multi,
            => try self.scanFnProto(node),
            else => {},
        }
    }

    fn scanVarDeclSurface(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const full = self.tree.fullVarDecl(@enumFromInt(node)) orelse return;
        try self.scanOptionalNode(full.ast.type_node);

        const init_node = full.ast.init_node.unwrap() orelse return;
        const init_idx = @intFromEnum(init_node);
        const tags = self.tree.nodes.items(.tag);
        if (init_idx < tags.len and isContainerTag(tags[init_idx])) {
            try self.scanContainerSurface(init_idx);
        } else {
            try self.scanNode(init_idx);
        }
    }

    fn scanFnProto(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const tags = self.tree.nodes.items(.tag);
        if (node >= tags.len) return;

        var buffer: [1]std.zig.Ast.Node.Index = undefined;
        const proto = switch (tags[node]) {
            .fn_proto => self.tree.fnProto(@enumFromInt(node)),
            .fn_proto_simple => self.tree.fnProtoSimple(&buffer, @enumFromInt(node)),
            .fn_proto_one => self.tree.fnProtoOne(&buffer, @enumFromInt(node)),
            .fn_proto_multi => self.tree.fnProtoMulti(@enumFromInt(node)),
            else => return,
        };

        for (proto.ast.params) |param| try self.scanParam(@intFromEnum(param));
        try self.scanOptionalNode(proto.ast.return_type);
        try self.scanOptionalNode(proto.ast.align_expr);
        try self.scanOptionalNode(proto.ast.addrspace_expr);
        try self.scanOptionalNode(proto.ast.section_expr);
        try self.scanOptionalNode(proto.ast.callconv_expr);
    }

    fn scanParam(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const tags = self.tree.nodes.items(.tag);
        if (node >= tags.len) return;

        if (isVarDeclTag(tags[node])) {
            const full = self.tree.fullVarDecl(@enumFromInt(node)) orelse return;
            try self.scanOptionalNode(full.ast.type_node);
            return;
        }

        try self.scanNode(node);
    }

    fn scanContainerSurface(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const tags = self.tree.nodes.items(.tag);
        if (node >= tags.len) return;

        switch (tags[node]) {
            .container_decl,
            .container_decl_trailing,
            => try self.scanContainerDeclComponents(self.tree.containerDecl(@enumFromInt(node))),
            .container_decl_two,
            .container_decl_two_trailing,
            => {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                try self.scanContainerDeclComponents(self.tree.containerDeclTwo(&buffer, @enumFromInt(node)));
            },
            .container_decl_arg,
            .container_decl_arg_trailing,
            => try self.scanContainerDeclComponents(self.tree.containerDeclArg(@enumFromInt(node))),
            .tagged_union,
            .tagged_union_trailing,
            => try self.scanContainerDeclComponents(self.tree.taggedUnion(@enumFromInt(node))),
            .tagged_union_enum_tag,
            .tagged_union_enum_tag_trailing,
            => try self.scanContainerDeclComponents(self.tree.taggedUnionEnumTag(@enumFromInt(node))),
            .tagged_union_two,
            .tagged_union_two_trailing,
            => {
                var buffer: [2]std.zig.Ast.Node.Index = undefined;
                try self.scanContainerDeclComponents(self.tree.taggedUnionTwo(&buffer, @enumFromInt(node)));
            },
            else => {},
        }
    }

    fn scanContainerDeclComponents(
        self: *PublicSurfaceScanner,
        container: std.zig.Ast.full.ContainerDecl,
    ) anyerror!void {
        if (container.ast.arg.unwrap()) |arg_node| try self.scanNode(@intFromEnum(arg_node));

        const tags = self.tree.nodes.items(.tag);
        for (container.ast.members) |member_node| {
            const member = @intFromEnum(member_node);
            if (member >= tags.len) continue;

            switch (tags[member]) {
                .container_field,
                .container_field_init,
                .container_field_align,
                => try self.scanContainerField(member),
                .simple_var_decl,
                .aligned_var_decl,
                .global_var_decl,
                => {
                    const full = self.tree.fullVarDecl(@enumFromInt(member)) orelse continue;
                    if (isPubToken(self.tree, full.visib_token)) try self.scanVarDeclSurface(member);
                },
                .fn_decl,
                .fn_proto,
                .fn_proto_simple,
                .fn_proto_one,
                .fn_proto_multi,
                => if (isPublicFnDecl(self.tree, member)) try self.scanDecl(member),
                else => {},
            }
        }
    }

    fn scanContainerField(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        const field = self.tree.fullContainerField(@enumFromInt(node)) orelse return;
        try self.scanOptionalNode(field.ast.type_expr);
        try self.scanOptionalNode(field.ast.value_expr);
        try self.scanOptionalNode(field.ast.align_expr);
    }

    fn scanOptionalNode(self: *PublicSurfaceScanner, node_opt: std.zig.Ast.Node.OptionalIndex) anyerror!void {
        if (node_opt.unwrap()) |node| try self.scanNode(@intFromEnum(node));
    }

    fn scanNode(self: *PublicSurfaceScanner, node: u32) anyerror!void {
        try ast_walk.walk(PublicSurfaceScanner, self.tree, node, self);
    }

    pub fn visit(
        self: *PublicSurfaceScanner,
        tree: *const std.zig.Ast,
        node: u32,
        tag: std.zig.Ast.Node.Tag,
    ) anyerror!void {
        if (tag != .identifier) return;

        const main_tokens = tree.nodes.items(.main_token);
        if (node >= main_tokens.len) return;
        try self.markIdentifier(tree.tokenSlice(main_tokens[node]));
    }

    fn markIdentifier(self: *PublicSurfaceScanner, identifier: []const u8) !void {
        const candidates = self.usage.by_name.get(normalizeIdentifier(identifier)) orelse return;
        for (candidates.items) |candidate| {
            if (self.usage.decls[candidate].file_index != self.file_index) continue;
            try self.usage.mark(candidate);
        }
    }
};

fn isReexportAlias(public_name: []const u8, referenced_name: []const u8) bool {
    const normalized_public = normalizeIdentifier(public_name);
    const normalized_referenced = normalizeIdentifier(referenced_name);
    if (std.mem.eql(u8, normalized_public, normalized_referenced)) return true;
    return isTypeLikeName(normalized_public) and isTypeLikeName(normalized_referenced);
}

fn isTypeLikeName(name: []const u8) bool {
    if (name.len == 0) return false;
    return std.ascii.isUpper(name[0]);
}

fn isIgnoredPublicDecl(path: []const u8, name: []const u8) bool {
    if (isSpecialName(name)) return true;
    return std.mem.eql(u8, std.fs.path.basename(path), "build.zig") and std.mem.eql(u8, name, "build");
}

fn isSpecialName(name: []const u8) bool {
    if (name.len > 0 and name[0] == '_') return true;
    if (std.mem.eql(u8, name, "main")) return true;
    if (std.mem.eql(u8, name, "panic")) return true;
    if (std.mem.eql(u8, name, "std_options")) return true;
    return false;
}

fn isPublicFnDecl(tree: *const std.zig.Ast, node: u32) bool {
    const tags = tree.nodes.items(.tag);
    if (node >= tags.len) return false;

    var buffer: [1]std.zig.Ast.Node.Index = undefined;
    const proto = switch (tags[node]) {
        .fn_decl => blk: {
            const data = tree.nodes.items(.data)[node];
            const proto_node = @intFromEnum(data.node_and_node[0]);
            break :blk switch (tags[proto_node]) {
                .fn_proto => tree.fnProto(@enumFromInt(proto_node)),
                .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(proto_node)),
                .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(proto_node)),
                .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(proto_node)),
                else => return false,
            };
        },
        .fn_proto => tree.fnProto(@enumFromInt(node)),
        .fn_proto_simple => tree.fnProtoSimple(&buffer, @enumFromInt(node)),
        .fn_proto_one => tree.fnProtoOne(&buffer, @enumFromInt(node)),
        .fn_proto_multi => tree.fnProtoMulti(@enumFromInt(node)),
        else => return false,
    };

    return isPubToken(tree, proto.visib_token);
}

fn isContainerTag(tag: std.zig.Ast.Node.Tag) bool {
    return switch (tag) {
        .container_decl,
        .container_decl_trailing,
        .container_decl_two,
        .container_decl_two_trailing,
        .container_decl_arg,
        .container_decl_arg_trailing,
        .tagged_union,
        .tagged_union_trailing,
        .tagged_union_enum_tag,
        .tagged_union_enum_tag_trailing,
        .tagged_union_two,
        .tagged_union_two_trailing,
        => true,
        else => false,
    };
}

test "project unused source selection uses discovered API root scope" {
    const allocator = std.testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile(
        "build.zig",
        "const build_api = @import(\"std\");\n" ++
            "const Fake = struct {\n" ++
            "    fn addModule(_: anytype, _: anytype) void {}\n" ++
            "    fn path(_: []const u8) build_api.LazyPath {\n" ++
            "        return .{ .cwd_relative = \"not-api.zig\" };\n" ++
            "    }\n" ++
            "};\n" ++
            "const main = @import(\"main.zig\");\n" ++
            "pub fn contextOnly() void {}\n" ++
            "pub fn build(b: *build_api.Build) void {\n" ++
            "    {\n" ++
            "        const b = Fake;\n" ++
            "        _ = b.addModule(.{ .root_source_file = b.path(\"unrelated.zig\") });\n" ++
            "    }\n" ++
            "    _ = Fake.addModule(b, .{ .root_source_file = b.path(\"unrelated.zig\") });\n" ++
            "    _ = b.addModule(\"not_api\", .{ .root_source_file = Fake.path(\"unrelated.zig\") });\n" ++
            "    _ = b.addConfigHeader(.{}, .{ .root_source_file = b.path(\"unrelated.zig\") });\n" ++
            "    _ = b.addModule(\"fixture\", .{ .root_source_file = b.path(\"api.zig\") });\n" ++
            "    _ = main.publicUnused;\n" ++
            "}\n",
    );
    try temp_dir.writeFile(
        "api.zig",
        "pub fn exportedByPackage() void {}\n",
    );
    try temp_dir.writeFile(
        "main.zig",
        "pub fn publicUnused() void {}\n",
    );
    try temp_dir.writeFile(
        "unrelated.zig",
        "pub fn unrelatedUnused() void {}\n",
    );

    var api_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    var main_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    var unrelated_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const api_path = try std.fmt.bufPrint(
        &api_path_buffer,
        "{s}/api.zig",
        .{temp_dir.path()},
    );
    const main_path = try std.fmt.bufPrint(
        &main_path_buffer,
        "{s}/main.zig",
        .{temp_dir.path()},
    );
    const unrelated_path = try std.fmt.bufPrint(
        &unrelated_path_buffer,
        "{s}/unrelated.zig",
        .{temp_dir.path()},
    );
    const selected_files = [_][]const u8{ api_path, main_path, unrelated_path };

    var project = try ProjectSources.init(&io_context, allocator, &selected_files);
    defer project.deinit();
    for (project.files()) |file| try std.testing.expectEqual(0, file.tree.errors.len);

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*item| item.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    var found_unrelated = false;
    for (diagnostics.items) |diagnostic| {
        if (std.mem.eql(u8, diagnostic.file_path, unrelated_path)) {
            found_unrelated = std.mem.indexOf(u8, diagnostic.message, "unrelatedUnused") != null;
        }
    }
    try std.testing.expect(found_unrelated);
}

test "project unused rejects a shadowed std build type" {
    const allocator = std.testing.allocator;

    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile(
        "build.zig",
        "const std = struct { pub const Build = struct {}; };\n" ++
            "pub fn build(b: *std.Build) void {\n" ++
            "    _ = b.addModule(\"fixture\", .{ .root_source_file = b.path(\"api.zig\") });\n" ++
            "}\n",
    );
    try temp_dir.writeFile("api.zig", "pub fn exportedByPackage() void {}\n");
    try temp_dir.writeFile("main.zig", "pub fn publicUnused() void {}\n");

    var api_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    var main_path_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const api_path = try std.fmt.bufPrint(
        &api_path_buffer,
        "{s}/api.zig",
        .{temp_dir.path()},
    );
    const main_path = try std.fmt.bufPrint(
        &main_path_buffer,
        "{s}/main.zig",
        .{temp_dir.path()},
    );
    const selected_files = [_][]const u8{ api_path, main_path };

    var project = try ProjectSources.init(&io_context, allocator, &selected_files);
    defer project.deinit();

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*item| item.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var found_api = false;
    var found_main = false;
    for (diagnostics.items) |diagnostic| {
        if (std.mem.eql(u8, diagnostic.file_path, api_path)) {
            found_api = std.mem.indexOf(u8, diagnostic.message, "exportedByPackage") != null;
        } else if (std.mem.eql(u8, diagnostic.file_path, main_path)) {
            found_main = std.mem.indexOf(u8, diagnostic.message, "publicUnused") != null;
        }
    }
    try std.testing.expect(found_api);
    try std.testing.expect(found_main);
}

test "project public API closure follows conditional aliases and cycles" {
    const allocator = std.testing.allocator;
    var root = try std.zig.Ast.parse(allocator,
        \\const selected = @import("left.zig");
        \\pub const api = if (@import("condition.zig").enabled) selected else @import("right.zig");
        \\pub const value = make(@import("hidden.zig"));
    , .zig);
    defer root.deinit(allocator);
    var left = try std.zig.Ast.parse(allocator,
        \\pub const cycle = @import("root.zig");
        \\pub const leaf = @import("leaf.zig");
    , .zig);
    defer left.deinit(allocator);
    var empty = try std.zig.Ast.parse(allocator, "", .zig);
    defer empty.deinit(allocator);
    const files = [_]import_resolver.File{
        .{ .path = "root.zig", .tree = &root },
        .{ .path = "left.zig", .tree = &left },
        .{ .path = "right.zig", .tree = &empty },
        .{ .path = "leaf.zig", .tree = &empty },
        .{ .path = "condition.zig", .tree = &empty },
        .{ .path = "hidden.zig", .tree = &empty },
    };
    var project = try ProjectContext.init(allocator, &files, &.{}, null);
    defer project.deinit();
    try project.appendApiRoot(0);
    try project.collectPublicApiFiles();
    for (0..4) |index| try std.testing.expect(project.isPublicApiFile(index));
    try std.testing.expect(!project.isPublicApiFile(4));
    try std.testing.expect(!project.isPublicApiFile(5));
}

test "project references retain typed reexports without promoting homonyms" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var directory = compat.TestDir.init();
    defer directory.cleanup();
    try directory.writeFile("api.zig",
        \\const Self = @This();
        \\pub const Leaf = struct {};
        \\pub const Wrapper = struct { child: Leaf, next: ?*Wrapper };
        \\pub fn run(_: *Self) Wrapper { return undefined; }
        \\pub fn unused() void {}
    );
    try directory.writeFile("facade.zig", "pub const api = @import(\"api.zig\");\n");
    try directory.writeFile("decoy.zig", "pub fn run() void {}\n");
    try directory.writeFile("consumer.zig",
        \\const facade = @import("facade.zig");
        \\pub fn main() void {
        \\    var api: facade.api = .{};
        \\    _ = api.run();
        \\}
        \\fn dynamic(receiver: anytype) void { receiver.unused(); }
    );
    const names = [_][]const u8{ "api.zig", "facade.zig", "decoy.zig", "consumer.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ directory.path(), name });
    }
    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*item| item.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var found_unused = false;
    var found_homonym = false;
    for (diagnostics.items) |diagnostic| {
        if (std.mem.eql(u8, diagnostic.file_path, paths[0])) {
            found_unused = std.mem.indexOf(u8, diagnostic.message, "unused") != null;
        } else if (std.mem.eql(u8, diagnostic.file_path, paths[2])) {
            found_homonym = std.mem.indexOf(u8, diagnostic.message, "run") != null;
        }
    }
    try std.testing.expect(found_unused);
    try std.testing.expect(found_homonym);
}

test "project contextual constants retain only their expected container" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var directory = compat.TestDir.init();
    defer directory.cleanup();
    const constant = "pub const empty: @This() = .{};\n";
    try directory.writeFile("assigned.zig", constant);
    try directory.writeFile("returned.zig", constant);
    try directory.writeFile("initialized.zig", constant);
    try directory.writeFile("decoy.zig", constant);
    try directory.writeFile("nested.zig", constant ++
        "pub const Item = struct { pub const empty: @This() = .{}; };\n");
    try directory.writeFile(
        "consumer.zig",
        "const Assigned = @import(\"assigned.zig\");\n" ++
            "const Returned = @import(\"returned.zig\");\n" ++
            "const Initialized = @import(\"initialized.zig\");\n" ++
            "const Nested = @import(\"nested.zig\").Item;\n" ++
            "fn reset(value: *Assigned) void { value.* = .empty; }\n" ++
            "fn make() error{OutOfMemory}!Returned { return .empty; }\n" ++
            "pub fn main() void {\n" ++
            "    var assigned: Assigned = .{};\n" ++
            "    reset(&assigned);\n" ++
            "    _ = make() catch return;\n" ++
            "    const initialized: Initialized = .empty;\n" ++
            "    const nested: Nested = .empty;\n" ++
            "    _ = initialized;\n" ++
            "    _ = nested;\n" ++
            "}\n",
    );
    const names = [_][]const u8{
        "assigned.zig", "returned.zig", "initialized.zig",
        "decoy.zig",    "nested.zig",   "consumer.zig",
    };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ directory.path(), name });
    }
    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var found_decoy = false;
    var found_nested = false;
    for (diagnostics.items) |diagnostic| {
        try std.testing.expectEqual(@as(usize, 1), diagnostic.range.start.line);
        if (std.mem.eql(u8, diagnostic.file_path, paths[3])) found_decoy = true;
        if (std.mem.eql(u8, diagnostic.file_path, paths[4])) found_nested = true;
    }
    try std.testing.expect(found_decoy);
    try std.testing.expect(found_nested);
}

test "project unused declarations ignore Zig build entrypoint" {
    try std.testing.expect(isIgnoredPublicDecl("build.zig", "build"));
    try std.testing.expect(isIgnoredPublicDecl("workspace/build.zig", "build"));
    try std.testing.expect(!isIgnoredPublicDecl("src/lib.zig", "build"));
    try std.testing.expect(!isIgnoredPublicDecl("build.zig", "helper"));
}

test "project unused analysis requires complete source and build syntax" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var directory = compat.TestDir.init();
    defer directory.cleanup();
    try directory.writeFile("a.zig",
        \\pub fn unusedA() void {}
        \\fn use() void {
        \\    _ = @import("b.zig").used;
        \\}
    );
    try directory.writeFile("b.zig", "pub fn unusedB() void {}\npub const used = 1;\n");
    const complete_source = "pub fn ignored() void {}\n";
    const complete_build =
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    _ = b.addModule("fixture", .{ .root_source_file = b.path("b.zig") });
        \\}
    ;
    const scenarios = [_]struct {
        source: []const u8,
        build: []const u8,
        findings: usize,
        /// Build context this pass must report itself: no per-file analysis
        /// pass covers it, so an unparsable one would otherwise remove
        /// project-wide dead-code detection without a trace.
        broken_context: ?[]const u8,
    }{
        .{ .source = "const broken = ;", .build = complete_build, .findings = 0, .broken_context = null },
        .{ .source = complete_source, .build = "const broken = ;", .findings = 0, .broken_context = "build.zig" },
        .{ .source = complete_source, .build = complete_build, .findings = 2, .broken_context = null },
    };
    const Scenarios = @TypeOf(scenarios);
    const names = [_][]const u8{ "a.zig", "malformed.zig", "b.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ directory.path(), name });
    }
    const Harness = struct {
        fn run(
            failing_allocator: std.mem.Allocator,
            io: *compat.Context,
            input_paths: []const []const u8,
            cases: *const Scenarios,
            case_index: usize,
        ) !void {
            const scenario = cases[case_index];
            var diagnostics: std.ArrayList(Diagnostic) = .empty;
            defer {
                for (diagnostics.items) |*item| item.deinit(failing_allocator);
                diagnostics.deinit(failing_allocator);
            }
            var sources = try ProjectSources.init(io, failing_allocator, input_paths);
            defer sources.deinit();
            try analyze(&sources, failing_allocator, &diagnostics);

            var context_reports: usize = 0;
            for (diagnostics.items) |diagnostic| {
                if (!std.mem.eql(u8, diagnostic.rule_id, "parse-error")) continue;
                context_reports += 1;
                // A selected source is diagnosed by the per-file pass, so
                // reporting it again here would only duplicate that report.
                try std.testing.expect(!std.mem.eql(u8, "malformed.zig", std.fs.path.basename(diagnostic.file_path)));
                if (scenario.broken_context) |name| {
                    try std.testing.expectEqualStrings(name, std.fs.path.basename(diagnostic.file_path));
                }
            }
            if (scenario.broken_context) |_| {
                try std.testing.expect(context_reports > 0);
            } else {
                try std.testing.expectEqual(@as(usize, 0), context_reports);
            }

            try std.testing.expectEqual(scenario.findings, diagnostics.items.len - context_reports);
            if (scenario.findings == 0) return;
            try std.testing.expectEqualStrings("a.zig", std.fs.path.basename(diagnostics.items[0].file_path));
            try std.testing.expectEqualStrings("malformed.zig", std.fs.path.basename(diagnostics.items[1].file_path));
        }
    };
    for (scenarios, 0..) |scenario, case_index| {
        try directory.writeFile("malformed.zig", scenario.source);
        try directory.writeFile("build.zig", scenario.build);
        try std.testing.checkAllAllocationFailures(
            allocator,
            Harness.run,
            .{ &io_context, &paths, &scenarios, case_index },
        );
    }
}

test "project unused follows only the module name a build script actually registers" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var directory = compat.TestDir.init();
    defer directory.cleanup();

    try directory.writeFile("root.zig", "pub const leaf = @import(\"leaf.zig\");\n");
    try directory.writeFile("leaf.zig", "pub fn calledFromConsumer() void {}\npub fn neverCalled() void {}\n");
    try directory.writeFile("other.zig", "pub fn otherModule() void {}\n");
    try directory.writeFile("consumer.zig",
        \\const lib = @import("lib_alias");
        \\pub fn main() void {
        \\    lib.leaf.calledFromConsumer();
        \\}
    );

    const build_prefix =
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const lib = b.createModule(.{ .root_source_file = b.path("root.zig") });
        \\    const other = b.createModule(.{ .root_source_file = b.path("other.zig") });
        \\    const consumer = b.createModule(.{ .root_source_file = b.path("consumer.zig") });
        \\
    ;
    const scenarios = [_]struct {
        registrations: []const u8,
        /// The consumer reaches `calledFromConsumer` only through a name the
        /// build registers for the module whose root re-exports the leaf.
        reaches_leaf: bool,
    }{
        .{ .registrations = "    consumer.addImport(\"lib_alias\", lib);\n", .reaches_leaf = true },
        .{ .registrations = "", .reaches_leaf = false },
        .{ .registrations = "    consumer.addImport(\"lib_alias\", other);\n", .reaches_leaf = false },
        .{
            .registrations = "    consumer.addImport(\"lib_alias\", lib);\n" ++
                "    consumer.addImport(\"lib_alias\", other);\n",
            .reaches_leaf = false,
        },
    };

    const names = [_][]const u8{ "root.zig", "leaf.zig", "other.zig", "consumer.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ directory.path(), name });
    }

    inline for (scenarios) |scenario| {
        try directory.writeFile("build.zig", build_prefix ++ scenario.registrations ++ "}\n");
        var project = try ProjectSources.init(&io_context, allocator, &paths);
        defer project.deinit();

        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*item| item.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try analyze(&project, allocator, &diagnostics);

        var reached: usize = 0;
        var unreached: usize = 0;
        for (diagnostics.items) |diagnostic| {
            if (std.mem.indexOf(u8, diagnostic.message, "calledFromConsumer") != null) reached += 1;
            if (std.mem.indexOf(u8, diagnostic.message, "neverCalled") != null) unreached += 1;
        }
        try std.testing.expectEqual(@as(usize, 1), unreached);
        const expected_reached: usize = if (scenario.reaches_leaf) 0 else 1;
        try std.testing.expectEqual(expected_reached, reached);
    }
}

test "project unused counts a guarded root-mediated call from a named module seam" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile("build.zig",
        \\const std = @import("std");
        \\
        \\pub fn build(b: *std.Build) void {
        \\    const marker = b.createModule(.{
        \\        .root_source_file = b.path("marker.zig"),
        \\    });
        \\    const seam = b.createModule(.{
        \\        .root_source_file = b.path("seam.zig"),
        \\    });
        \\    const abi_check = b.addObject(.{
        \\        .name = "abi-check",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("checker.zig"),
        \\            .imports = &.{
        \\                .{ .name = "ztex_header", .module = marker },
        \\                .{ .name = "seam", .module = seam },
        \\            },
        \\        }),
        \\    });
        \\    b.getInstallStep().dependOn(&abi_check.step);
        \\}
        \\
    );
    // The checker the compilation root supplies, reached through
    // `@import("root")` rather than through the module that declares it.
    try temp_dir.writeFile("checker.zig",
        \\pub const ztex_abi_check_marker = @import("ztex_header");
        \\const header = ztex_abi_check_marker;
        \\
        \\pub fn checkSeam(comptime entries: anytype) void {
        \\    if (entries.abi_version != @TypeOf(header.ztex_abi_version)) @compileError("width drift");
        \\}
        \\
        \\pub fn unusedRootHelper() void {}
        \\
    );
    try temp_dir.writeFile("seam.zig",
        \\pub const ztex_abi_version: u32 = 1;
        \\
        \\comptime {
        \\    const checker_root = @import("root");
        \\    if (@hasDecl(checker_root, "ztex_abi_check_marker")) checker_root.checkSeam(.{
        \\        .abi_version = @TypeOf(ztex_abi_version),
        \\    });
        \\}
        \\
    );
    try temp_dir.writeFile("marker.zig", "pub const ztex_abi_version: u32 = 1;\n");

    const names = [_][]const u8{ "checker.zig", "seam.zig", "marker.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ temp_dir.path(), name });
    }

    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("checker.zig", std.fs.path.basename(diagnostics.items[0].file_path));
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "unusedRootHelper") != null);
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "checkSeam") == null);
}

test "project unused resolves the compilation root per artifact" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile("build.zig",
        \\const std = @import("std");
        \\
        \\pub fn build(b: *std.Build) void {
        \\    const seam = b.createModule(.{ .root_source_file = b.path("seam.zig") });
        \\    const probe_seam = b.createModule(.{ .root_source_file = b.path("probe_seam.zig") });
        \\    const abi_check = b.addObject(.{
        \\        .name = "abi-check",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("checker.zig"),
        \\            .imports = &.{.{ .name = "seam", .module = seam }},
        \\        }),
        \\    });
        \\    const abi_probe = b.addObject(.{
        \\        .name = "abi-probe",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("probe.zig"),
        \\            .imports = &.{.{ .name = "probe_seam", .module = probe_seam }},
        \\        }),
        \\    });
        \\    b.getInstallStep().dependOn(&abi_check.step);
        \\    b.step("probe", "Compile the probe").dependOn(&abi_probe.step);
        \\}
        \\
    );
    try temp_dir.writeFile("checker.zig",
        \\pub fn checkSeam() void {}
        \\
        \\pub fn unusedRootHelper() void {}
        \\
    );
    try temp_dir.writeFile("probe.zig",
        \\pub fn checkProbe() void {}
        \\
        \\pub fn unusedProbeHelper() void {}
        \\
    );
    try temp_dir.writeFile("seam.zig",
        \\comptime {
        \\    const checker_root = @import("root");
        \\    if (@hasDecl(checker_root, "checkSeam")) checker_root.checkSeam();
        \\}
        \\
    );
    try temp_dir.writeFile("probe_seam.zig",
        \\comptime {
        \\    const probe_root = @import("root");
        \\    if (@hasDecl(probe_root, "checkProbe")) probe_root.checkProbe();
        \\}
        \\
    );

    const names = [_][]const u8{ "checker.zig", "probe.zig", "seam.zig", "probe_seam.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ temp_dir.path(), name });
    }

    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    // Each artifact answers `@import("root")` for the files it alone reaches,
    // and neither root file is treated as entirely used because of that.
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var unused_helper: usize = 0;
    var unused_probe_helper: usize = 0;
    for (diagnostics.items) |diagnostic| {
        if (std.mem.indexOf(u8, diagnostic.message, "unusedRootHelper") != null) unused_helper += 1;
        if (std.mem.indexOf(u8, diagnostic.message, "unusedProbeHelper") != null) unused_probe_helper += 1;
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "checkSeam") == null);
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "checkProbe") == null);
    }
    try std.testing.expectEqual(@as(usize, 1), unused_helper);
    try std.testing.expectEqual(@as(usize, 1), unused_probe_helper);
}

test "project unused leaves a root call unresolved when two artifacts share the seam" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    try temp_dir.writeFile("build.zig",
        \\const std = @import("std");
        \\
        \\pub fn build(b: *std.Build) void {
        \\    const seam = b.createModule(.{ .root_source_file = b.path("seam.zig") });
        \\    _ = b.addObject(.{
        \\        .name = "first",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("first.zig"),
        \\            .imports = &.{.{ .name = "seam", .module = seam }},
        \\        }),
        \\    });
        \\    _ = b.addObject(.{
        \\        .name = "second",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("second.zig"),
        \\            .imports = &.{.{ .name = "seam", .module = seam }},
        \\        }),
        \\    });
        \\}
        \\
    );
    try temp_dir.writeFile("first.zig", "pub fn checkRoot() void {}\n");
    try temp_dir.writeFile("second.zig", "pub fn checkRoot() void {}\n");
    try temp_dir.writeFile("seam.zig",
        \\comptime {
        \\    const shared_root = @import("root");
        \\    if (@hasDecl(shared_root, "checkRoot")) shared_root.checkRoot();
        \\}
        \\
    );

    const names = [_][]const u8{ "first.zig", "second.zig", "seam.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ temp_dir.path(), name });
    }

    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    // A seam two artifacts reach has no single compilation root, so neither
    // `checkRoot` may be silenced by guessing which root the call names.
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var first_reports: usize = 0;
    var second_reports: usize = 0;
    for (diagnostics.items) |diagnostic| {
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "checkRoot") != null);
        if (std.mem.eql(u8, "first.zig", std.fs.path.basename(diagnostic.file_path))) first_reports += 1;
        if (std.mem.eql(u8, "second.zig", std.fs.path.basename(diagnostic.file_path))) second_reports += 1;
    }
    try std.testing.expectEqual(@as(usize, 1), first_reports);
    try std.testing.expectEqual(@as(usize, 1), second_reports);
}

test "project unused never resolves the reserved root import to a file or module name" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    // A file named root.zig and a module the build binds to the name `root` are
    // both decoys: `@import("root")` is reserved for the compilation root, so
    // neither may answer it in any build graph state.
    try temp_dir.writeFile("root.zig", "pub fn rootMember() void {}\n");
    try temp_dir.writeFile("lib.zig", "pub fn libMember() void {}\n");
    try temp_dir.writeFile("first.zig", "pub fn checkRoot() void {}\n");
    try temp_dir.writeFile("second.zig", "pub fn checkRoot() void {}\n");
    try temp_dir.writeFile("consumer.zig", "pub const seam = @import(\"abi_seam\");\n");
    try temp_dir.writeFile("seam.zig",
        \\comptime {
        \\    const reserved = @import("root");
        \\    if (@hasDecl(reserved, "checkRoot")) reserved.checkRoot();
        \\    if (@hasDecl(reserved, "rootMember")) reserved.rootMember();
        \\    if (@hasDecl(reserved, "libMember")) reserved.libMember();
        \\}
        \\
    );

    const build_prefix =
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const lib = b.createModule(.{ .root_source_file = b.path("lib.zig") });
        \\    const seam = b.createModule(.{ .root_source_file = b.path("seam.zig") });
        \\    const consumer = b.createModule(.{
        \\        .root_source_file = b.path("consumer.zig"),
        \\        .imports = &.{
        \\            .{ .name = "root", .module = lib },
        \\            .{ .name = "abi_seam", .module = seam },
        \\        },
        \\    });
        \\    _ = consumer;
        \\
    ;
    const first_artifact =
        \\    _ = b.addObject(.{
        \\        .name = "first",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("first.zig"),
        \\            .imports = &.{.{ .name = "abi_seam", .module = seam }},
        \\        }),
        \\    });
        \\
    ;
    const second_artifact =
        \\    _ = b.addObject(.{
        \\        .name = "second",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("second.zig"),
        \\            .imports = &.{.{ .name = "abi_seam", .module = seam }},
        \\        }),
        \\    });
        \\
    ;
    const scenarios = [_]struct {
        registrations: []const u8,
        /// Roots the build graph leaves without one compilation root, which is
        /// how many `checkRoot` declarations stay reportable.
        unreachable_roots: usize,
        first_reported: bool,
        second_reported: bool,
    }{
        .{ .registrations = first_artifact, .unreachable_roots = 1, .first_reported = false, .second_reported = true },
        .{
            .registrations = first_artifact ++ second_artifact,
            .unreachable_roots = 2,
            .first_reported = true,
            .second_reported = true,
        },
        .{ .registrations = "", .unreachable_roots = 2, .first_reported = true, .second_reported = true },
    };

    const names = [_][]const u8{ "root.zig", "lib.zig", "first.zig", "second.zig", "consumer.zig", "seam.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ temp_dir.path(), name });
    }

    inline for (scenarios) |scenario| {
        try temp_dir.writeFile("build.zig", build_prefix ++ scenario.registrations ++ "}\n");
        var project = try ProjectSources.init(&io_context, allocator, &paths);
        defer project.deinit();

        var diagnostics: std.ArrayList(Diagnostic) = .empty;
        defer {
            for (diagnostics.items) |*item| item.deinit(allocator);
            diagnostics.deinit(allocator);
        }
        try analyze(&project, allocator, &diagnostics);

        // The decoys stay reportable in every state, and `checkRoot` is counted
        // only where exactly one artifact reaches the seam.
        var check_root: usize = 0;
        var root_member: usize = 0;
        var lib_member: usize = 0;
        var first_reports: usize = 0;
        var second_reports: usize = 0;
        for (diagnostics.items) |diagnostic| {
            if (std.mem.indexOf(u8, diagnostic.message, "checkRoot") != null) check_root += 1;
            if (std.mem.indexOf(u8, diagnostic.message, "rootMember") != null) root_member += 1;
            if (std.mem.indexOf(u8, diagnostic.message, "libMember") != null) lib_member += 1;
            if (std.mem.eql(u8, "first.zig", std.fs.path.basename(diagnostic.file_path))) first_reports += 1;
            if (std.mem.eql(u8, "second.zig", std.fs.path.basename(diagnostic.file_path))) second_reports += 1;
        }
        try std.testing.expectEqual(@as(usize, 1), root_member);
        try std.testing.expectEqual(@as(usize, 1), lib_member);
        try std.testing.expectEqual(scenario.unreachable_roots, check_root);
        try std.testing.expectEqual(if (scenario.first_reported) 1 else 0, first_reports);
        try std.testing.expectEqual(if (scenario.second_reported) 1 else 0, second_reports);
        try std.testing.expectEqual(scenario.unreachable_roots + 2, diagnostics.items.len);
    }
}

test "project unused keeps two build scripts from claiming each other's modules" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    var pkg_buffer: [std.fs.max_path_bytes]u8 = undefined;
    const pkg_path = try std.fmt.bufPrint(&pkg_buffer, "{s}/pkg", .{temp_dir.path()});
    try compat.makePath(&io_context, pkg_path);

    // Two build scripts of identical shape, each binding the same import name
    // to its own seam module and compiling its own root. A module binding read
    // from the other script's declaration would resolve that shared name to a
    // module the reading file never imports.
    try temp_dir.writeFile("build.zig",
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const seam = b.createModule(.{ .root_source_file = b.path("seam_a.zig") });
        \\    const abi = b.addObject(.{
        \\        .name = "abi-a",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("root_a.zig"),
        \\            .imports = &.{.{ .name = "seam_name", .module = seam }},
        \\        }),
        \\    });
        \\    b.getInstallStep().dependOn(&abi.step);
        \\}
        \\
    );
    try temp_dir.writeFile("pkg/build.zig",
        \\const std = @import("std");
        \\pub fn build(b: *std.Build) void {
        \\    const seam = b.createModule(.{ .root_source_file = b.path("seam_b.zig") });
        \\    const abi = b.addObject(.{
        \\        .name = "abi-b",
        \\        .root_module = b.createModule(.{
        \\            .root_source_file = b.path("root_b.zig"),
        \\            .imports = &.{.{ .name = "seam_name", .module = seam }},
        \\        }),
        \\    });
        \\    b.getInstallStep().dependOn(&abi.step);
        \\}
        \\
    );
    try temp_dir.writeFile("seam_a.zig",
        \\pub fn seamAMember() void {}
        \\
        \\comptime {
        \\    const abi_root = @import("root");
        \\    if (@hasDecl(abi_root, "checkRootA")) abi_root.checkRootA();
        \\}
        \\
    );
    try temp_dir.writeFile("pkg/seam_b.zig",
        \\pub fn seamBOnly() void {}
        \\
        \\comptime {
        \\    const abi_root = @import("root");
        \\    if (@hasDecl(abi_root, "checkRootB")) abi_root.checkRootB();
        \\}
        \\
    );
    try temp_dir.writeFile("root_a.zig",
        \\const seam = @import("seam_name");
        \\
        \\pub fn checkRootA() void {}
        \\
        \\fn useSeamA() void {
        \\    seam.seamAMember();
        \\}
        \\
    );
    try temp_dir.writeFile("pkg/root_b.zig",
        \\const seam = @import("seam_name");
        \\
        \\pub fn checkRootB() void {}
        \\
        \\fn useSeamB() void {
        \\    seam.seamBOnly();
        \\}
        \\
    );

    const names = [_][]const u8{ "seam_a.zig", "root_a.zig", "pkg/seam_b.zig", "pkg/root_b.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ temp_dir.path(), name });
    }

    var sources = try ProjectSources.init(&io_context, allocator, &paths);
    defer sources.deinit();
    for (sources.files()) |file| try std.testing.expectEqual(@as(usize, 0), file.tree.errors.len);

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&sources, allocator, &diagnostics);

    // Each seam is reached by exactly one artifact, so its guarded call through
    // `@import("root")` is live in both scripts. The import name they share
    // stays unresolved instead of picking one script's module, which is what
    // leaves both seam members reported rather than one silently used.
    try std.testing.expectEqual(@as(usize, 2), diagnostics.items.len);
    var seam_a_reports: usize = 0;
    var seam_b_reports: usize = 0;
    for (diagnostics.items) |diagnostic| {
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "checkRootA") == null);
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "checkRootB") == null);
        if (std.mem.indexOf(u8, diagnostic.message, "seamAMember") != null) {
            try std.testing.expectEqualStrings("seam_a.zig", std.fs.path.basename(diagnostic.file_path));
            seam_a_reports += 1;
        }
        if (std.mem.indexOf(u8, diagnostic.message, "seamBOnly") != null) {
            try std.testing.expectEqualStrings("seam_b.zig", std.fs.path.basename(diagnostic.file_path));
            seam_b_reports += 1;
        }
    }
    try std.testing.expectEqual(@as(usize, 1), seam_a_reports);
    try std.testing.expectEqual(@as(usize, 1), seam_b_reports);
}

test "project unused follows a root entry file a version conditional selects from" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    // The build script names both candidate roots but the comptime choice
    // compiles only one of them, so the branch this frontend did not take
    // still names a root of the same artifact. Only `main.zig` reaches the
    // seam, so its hook is live through that compilation unit whichever
    // candidate was chosen.
    try temp_dir.writeFile("build.zig",
        \\const std = @import("std");
        \\const builtin = @import("builtin");
        \\
        \\pub fn build(b: *std.Build) void {
        \\    const main_source = if (builtin.zig_version.minor == 16)
        \\        b.path("main_0_16.zig")
        \\    else
        \\        b.path("main.zig");
        \\    _ = b.addExecutable(.{
        \\        .name = "app",
        \\        .root_module = b.createModule(.{ .root_source_file = main_source }),
        \\    });
        \\}
        \\
    );
    try temp_dir.writeFile("main.zig",
        \\const lib = @import("lib.zig");
        \\const seam = @import("seam.zig");
        \\
        \\pub fn seamHook() void {}
        \\
        \\pub fn main() void {
        \\    lib.viaNonSelectedRoot();
        \\    _ = seam;
        \\}
        \\
    );
    try temp_dir.writeFile("main_0_16.zig",
        \\const lib = @import("lib.zig");
        \\
        \\pub fn main() void {
        \\    lib.viaSelectedRoot();
        \\}
        \\
    );
    try temp_dir.writeFile("seam.zig",
        \\comptime {
        \\    const root = @import("root");
        \\    if (@hasDecl(root, "seamHook")) root.seamHook();
        \\}
        \\
    );
    try temp_dir.writeFile("lib.zig",
        \\pub fn viaNonSelectedRoot() void {}
        \\pub fn viaSelectedRoot() void {}
        \\pub fn dead() void {}
        \\
    );

    const names = [_][]const u8{ "main.zig", "main_0_16.zig", "seam.zig", "lib.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ temp_dir.path(), name });
    }

    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    for (project.files()) |file| try std.testing.expectEqual(@as(usize, 0), file.tree.errors.len);

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    // The alias reference and the guarded root call are both live, and only
    // the unreferenced declaration is reported.
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "dead") != null);
    try std.testing.expectEqualStrings("lib.zig", std.fs.path.basename(diagnostics.items[0].file_path));
    for (diagnostics.items) |diagnostic| {
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "seamHook") == null);
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "viaNonSelectedRoot") == null);
        try std.testing.expect(std.mem.indexOf(u8, diagnostic.message, "viaSelectedRoot") == null);
    }
}

test "project unused follows a root module a version conditional binds to a name" {
    const allocator = std.testing.allocator;
    var io_context = try compat.Context.init(allocator, 1);
    defer io_context.deinit();
    var temp_dir = compat.TestDir.init();
    defer temp_dir.cleanup();

    // The artifact compiles a module the script bound to a name first, and the
    // name is filled by a comptime version conditional. Both arms of that
    // selection are roots of the same artifact, so `@import("root")` in a file
    // the artifact reaches answers whichever one the frontend compiled.
    try temp_dir.writeFile("build.zig",
        \\const std = @import("std");
        \\const builtin = @import("builtin");
        \\
        \\pub fn build(b: *std.Build) void {
        \\    const app_module = if (builtin.zig_version.minor == 16)
        \\        b.createModule(.{ .root_source_file = b.path("main_0_16.zig") })
        \\    else
        \\        b.createModule(.{ .root_source_file = b.path("main.zig") });
        \\    _ = b.addExecutable(.{
        \\        .name = "app",
        \\        .root_module = app_module,
        \\    });
        \\}
        \\
    );
    try temp_dir.writeFile("main.zig",
        \\const seam = @import("seam.zig");
        \\
        \\pub fn seamHook() void {}
        \\
        \\pub fn main() void {
        \\    _ = seam;
        \\}
        \\
    );
    // Only the unselected candidate leaves the seam out of its module graph,
    // so the guarded call has one compilation root to name.
    try temp_dir.writeFile("main_0_16.zig", "pub fn main() void {}\n");
    try temp_dir.writeFile("seam.zig",
        \\comptime {
        \\    const root = @import("root");
        \\    if (@hasDecl(root, "seamHook")) root.seamHook();
        \\}
        \\
        \\pub fn unreachedSeamMember() void {}
        \\
    );

    const names = [_][]const u8{ "main.zig", "main_0_16.zig", "seam.zig" };
    var buffers: [names.len][std.fs.max_path_bytes]u8 = undefined;
    var paths: [names.len][]const u8 = undefined;
    for (names, 0..) |name, index| {
        paths[index] = try std.fmt.bufPrint(&buffers[index], "{s}/{s}", .{ temp_dir.path(), name });
    }

    var project = try ProjectSources.init(&io_context, allocator, &paths);
    defer project.deinit();
    for (project.files()) |file| try std.testing.expectEqual(@as(usize, 0), file.tree.errors.len);

    var diagnostics: std.ArrayList(Diagnostic) = .empty;
    defer {
        for (diagnostics.items) |*diagnostic| diagnostic.deinit(allocator);
        diagnostics.deinit(allocator);
    }
    try analyze(&project, allocator, &diagnostics);

    // The guarded call through `@import("root")` is live, and the seam member
    // nothing names is the only report left.
    try std.testing.expectEqual(@as(usize, 1), diagnostics.items.len);
    try std.testing.expectEqualStrings("seam.zig", std.fs.path.basename(diagnostics.items[0].file_path));
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "unreachedSeamMember") != null);
    try std.testing.expect(std.mem.indexOf(u8, diagnostics.items[0].message, "seamHook") == null);
}
