import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.MontgomeryRegisters
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PipelineReadiness
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PackingRefinement

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution
open ScalarMontgomeryMul
set_option maxRecDepth 100000

/-- Explicit witnesses for the actual reducer, computed from the caller bytes. -/
def reductionData (s : GlobalState) (bits : BitVec 256) : PipelineData :=
  wordPipelineData s bits (reductionQuotient (inputWords bits))

/-- Public validity alone establishes every register and memory precondition. -/
theorem reductionData_ready (out input : Pointer) (s : GlobalState) (bits : BitVec 256)
    (hwf : s.WF) (hout : SmallRange s.mem out 32) (hin : Dalek.ReadBytes s input 32 bits) :
    PipelineReady out input s (reductionData s bits) := by
  apply wordPipelineData_ready out input s bits hwf hout hin
  intro E
  have hm := montgomeryPhaseEnv_quotient E (reductionProducts (inputWords bits))
  have hqw := reductionQuotient_widen (inputWords bits) (inputWords_bound bits)
  constructor
  · exact hm.1.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hqw 0).symm)
  · exact hm.2.1.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hqw 1).symm)
  · exact hm.2.2.1.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hqw 2).symm)
  · exact hm.2.2.2.1.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hqw 3).symm)
  · exact hm.2.2.2.2.trans (congrArg LeanMLIR.RIR.PoisonOr.value (hqw 4).symm)

/-- The canonical witness builder has no execution or arithmetic hypotheses. -/
theorem pipeline_witnesses (out input : Pointer) (s : GlobalState) (bits : BitVec 256)
    (hwf : s.WF) (hout : SmallRange s.mem out 32) (hin : Dalek.ReadBytes s input 32 bits) :
    ∃ d : PipelineData, PipelineReady out input s d ∧
      (∀ i, s.alloc.nextFreeBlock ≤ (d.scratch i).id.id) ∧
      d.bytes = fun i => (Dalek.reduceScalarBytes bits).extractLsb' (8 * i.val) 8 := by
  exact ⟨reductionData s bits, reductionData_ready out input s bits hwf hout hin,
    startupScratch_local s, reductionBytes_correct bits⟩

end Agave.Ed25519.ScalarReduce32.Execution
