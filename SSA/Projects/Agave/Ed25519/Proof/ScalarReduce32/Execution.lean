import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PipelineWitnesses
import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PipelineFrame

/-! Caller-level refinement of the actual imported 32-byte scalar reducer. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution.Dalek

/-- Exact execution and public post-state for every valid 32-byte caller input.
The high input bit is unrestricted. All 34 private allocations and all 622
imported instructions are accounted for by the composed pipeline proof. -/
theorem call (out input : Pointer) (state : GlobalState) (bits : BitVec 256)
    (hwf : state.WF) (hout : SmallRange state.mem out 32)
    (hinput : ReadBytes state input 32 bits) :
    program.call (args2 out input) state =
      .value (.nil, resultState state out (reduceScalarBytes bits) 34) := by
  obtain ⟨d, hr, hl, hb⟩ := pipeline_witnesses out input state bits hwf hout hinput
  have h := pipeline_call_public out input state d hr hwf hl
  simpa only [hb, resultState, args2, program.args] using h

/-- Canonical scalar-reduction contract, with no assumed execution equation,
word bounds, arithmetic identity, or invariant-construction premise. -/
theorem contract (layout : Layout Point Scalar Result)
    (hlayout : ∀ bits, layout.reduce bits = reduceScalarBytes bits) :
    ScalarReduceContract program.call layout := by
  apply contract_of_call_equation layout hlayout
  intro out input state bits hwf hout hinput _hdisjoint
  exact call out input state bits hwf hout hinput

end Agave.Ed25519.ScalarReduce32.Execution
