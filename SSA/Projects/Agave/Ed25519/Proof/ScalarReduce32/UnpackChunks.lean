import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Phases
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackChunk0
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackChunk1
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackChunk2
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackTail
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.UnpackScratch

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000

/-- The unpack slices retain all private stores, fences, and lifetime markers. -/
theorem unpack_body_decomposition : unpack =
    (program.entry.body.drop 95).take 11 ++
    unpackBlock0.body ++ unpackBlock1.body ++ unpackScratch0Block.body ++
    unpackBlock2.body ++ unpackScratch1Block.body ++ unpackBlock3.body ++
    unpackScratch2Block.body ++ unpackScratch3Block.body ++ unpackTailBlock.body := rfl

end Agave.Ed25519.ScalarReduce32.Execution
