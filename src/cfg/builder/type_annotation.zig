const graph = @import("../graph.zig");
const Source = @import("../../source.zig").Source;
const IrNode = graph.IrNode;

pub fn Mixin(comptime _Builder: type) type {
    return struct {
        /// Annotate an IR node with type information if available.
        /// Returns the node (possibly enriched with type info).
        pub fn annotateWithType(self: *_Builder, node: IrNode, source: *Source, ast_node: u32) IrNode {
            _ = source;
            // Type annotation is opt-in through the builder's context.
            if (self.type_context) |ctx| {
                if (ctx.getNodeType(ast_node)) |ti| {
                    return node.withType(ti);
                }
            }

            return node;
        }

        /// Restore source-backed declaration metadata omitted by serialization.
        /// Synthetic try/catch annotations describe control flow, not declarations.
        pub fn restoreDeclarationTypes(self: *_Builder, cfg: *graph.Cfg, source: *Source) void {
            for (cfg.nodes.items) |*cfg_node| {
                var node = cfg_node.ir_node;
                if (node.tag != .var_decl) continue;
                const ast_node = node.ast_node orelse continue;
                node.type_info = null;
                cfg_node.ir_node = annotateWithType(self, node, source, ast_node);
            }
        }
    };
}
