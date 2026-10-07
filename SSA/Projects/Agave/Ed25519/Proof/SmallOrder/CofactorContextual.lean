import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorLinked

/-! Invocation-level cofactor facts for the actual primitive installed by the
small-order linker. The caller supplies only live point bytes and a wellformed
state; the exact schedule supplies both the output representative and its group
interpretation. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR Verifier.Execution
open Reduce64.Execution (SmallRange)

/-- The installed verifier primitive has the proved cofactor contract in every
caller context, independently of the remaining primitive slots. -/
theorem linked_cofactorContract (remaining : Dalek.Primitives) :
    Dalek.CofactorContract (linkVerifier remaining).pointMulByPow2
      (Verifier.Execution.ValidPoint.layout SmallOrder.ValidPoint.timesEight) :=
  cofactorContract

/-- A concrete invocation returns the exact valid representative of eight
times the input point and preserves every disjoint caller observation. No
separation between input and output, global readiness, or phase premise is
needed for this callee. -/
theorem linked_cofactor_call_valid (remaining : Dalek.Primitives)
    (out input : Pointer) (s : GlobalState) (P : Verifier.Execution.ValidPoint)
    (hwf : s.WF) (hout : SmallRange s.mem out 160)
    (hin : Dalek.ReadBytes s input 160 P.bytes) :
    ∃ after : GlobalState,
      (linkVerifier remaining).pointMulByPow2
        (.cons (.value out) (.cons (.value input) (.cons (.value 3) .nil))) s =
          .value (.nil, after) ∧
      Dalek.OutputFrame s after out 160 ∧
      Dalek.ReadBytes after out 160 (SmallOrder.ValidPoint.timesEight P).bytes ∧
      (SmallOrder.ValidPoint.timesEight P).curve = 8 • P.curve := by
  have hi120 := SerialPoint.Execution.smallRange_add hin.1 (k := 0) (count := 120) (by decide)
  simp only [Pointer.add_zero] at hi120
  exact ⟨cofactorState s out input, cofactor_call_three out input s hwf hout hi120,
    cofactorState_frame s out input hwf hout hi120,
    cofactorState_payload s out input P hwf hout hin, rfl⟩

end Agave.Ed25519.SmallOrder.Execution
