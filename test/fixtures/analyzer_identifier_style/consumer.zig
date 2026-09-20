const Artifact = @import("Artifact.zig");

pub fn makeArtifact() Artifact {
    return Artifact.init();
}
