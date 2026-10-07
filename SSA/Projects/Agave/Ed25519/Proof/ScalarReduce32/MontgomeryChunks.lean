import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Phases
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CancellationChunk0
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CancellationChunk1
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CancellationChunk2
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CancellationChunk3
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CancellationChunk4
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk0
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk1
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk2
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk3
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk4
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk5
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk6
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.CarryGapChunk7

namespace Agave.Ed25519.ScalarReduce32.Execution
set_option maxRecDepth 10000

/-- Exact instruction order of all five cancellation windows and their carries. -/
theorem montgomery_body_decomposition : montgomery =
    cancellationBlock0.body ++
    carryGapBlock0.body ++
    cancellationBlock1.body ++
    carryGapBlock1.body ++
    cancellationBlock2.body ++
    carryGapBlock2.body ++
    cancellationBlock3.body ++
    carryGapBlock3.body ++
    cancellationBlock4.body ++
    carryGapBlock4.body ++
    carryGapBlock5.body ++
    carryGapBlock6.body ++
    carryGapBlock7.body := rfl

end Agave.Ed25519.ScalarReduce32.Execution
