import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Phases
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CleanupChunks

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000

/-- All cleanup instructions, including volatile reads and writes, are retained. -/
theorem cleanup_body_decomposition : cleanup =
    cleanupChunks0Block.body ++ cleanupChunks1Block.body ++
    cleanupChunks2Block.body ++ cleanupChunks3Block.body ++
    cleanupChunks4Block.body ++ cleanupChunks5Block.body := rfl

end Agave.Ed25519.ScalarReduce32.Execution
