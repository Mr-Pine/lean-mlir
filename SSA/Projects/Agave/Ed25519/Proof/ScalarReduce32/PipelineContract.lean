import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.PipelineFrame

/-! Reduction of the caller contract to explicit finite invariant construction.
The witness builder below is not proved here. In particular, this file does not
claim an unconditional canonical-reduction contract for the imported callee. -/
namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
open Agave.Ed25519.Verifier.Execution.Dalek

/-- Unlike the earlier call-equation adapter, this endpoint requires no assumed
RIR execution. The remaining witness obligation is word/memory arithmetic over
the explicit pipeline and the canonical byte identity. -/
theorem contract_of_pipeline_witnesses (layout : Layout Point Scalar Result)
    (hlayout : ∀ bits, layout.reduce bits = reduceScalarBytes bits)
    (hbuild : ∀ (out input : Pointer) (state : GlobalState) (bits : BitVec 256),
      state.WF → SmallRange state.mem out 32 → ReadBytes state input 32 bits →
      (Range.of out 256).Disjoint (Range.of input 256) →
      ∃ d : PipelineData,
        PipelineReady out input state d ∧
        (∀ i, state.alloc.nextFreeBlock ≤ (d.scratch i).id.id) ∧
        d.bytes = fun i => (reduceScalarBytes bits).extractLsb' (8 * i.val) 8) :
    ScalarReduceContract program.call layout := by
  apply contract_of_call_equation layout hlayout
  intro out input state bits hwf hout hinput hdisjoint
  obtain ⟨d, hready, hlocal, hbytes⟩ :=
    hbuild out input state bits hwf hout hinput hdisjoint
  have h := pipeline_call_public out input state d hready hwf hlocal
  simpa only [hbytes, resultState, args2, program.args] using h

end Agave.Ed25519.ScalarReduce32.Execution
