import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoubleAdapter
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleExecution

/-! Transfer the proved serial projective-double execution through exact
program equality to the actual helper linked into the small-order call. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR
open SerialPoint SerialPoint.Execution
open Reduce64.Execution (SmallRange)

/-- The linked helper executes its original four square calls, arithmetic,
twenty output stores and stack cleanup. Its five private allocations advance
the counter, while only the 160 output bytes remain in memory. -/
theorem projective_double_call (out input : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120) :
    cofactorPrimitives.projectiveDouble
      (.cons (.value out) (.cons (.value input) .nil)) s =
      .value (.nil, pointPost s out (doubleWordTrace (readPointWords s input)) 5) := by
  change (Verifier.Execution.SmallOrderProjectiveDouble.program
      ⟨Encoding.Decompress.Execution.Pow2k.program.call⟩).call
    (.cons (.value out) (.cons (.value input) .nil)) s = _
  rw [← square_adapter_call]
  exact double_call out input s hwf hout hin

/-- The linked helper's readback is the completed-coordinate doubling formula,
and every disjoint caller observation survives its actual execution. -/
theorem projective_double_readback (out input : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120)
    (hP : ProjectiveTight (unsignedPoint (pointFromWords (readPointWords s input)))) :
    ∃ final : GlobalState,
      cofactorPrimitives.projectiveDouble
        (.cons (.value out) (.cons (.value input) .nil)) s = .value (.nil, final) ∧
      unsignedPoint (pointFromWords (readPointWords final out)) =
        doubleCompleted (unsignedPoint (pointFromWords (readPointWords s input))) ∧
      (∀ q bits, (Range.of q bits).Disjoint (Range.of out 1280) →
        final.mem.readAt q bits = s.mem.readAt q bits) := by
  change ∃ final : GlobalState,
    (Verifier.Execution.SmallOrderProjectiveDouble.program
      ⟨Encoding.Decompress.Execution.Pow2k.program.call⟩).call
      (.cons (.value out) (.cons (.value input) .nil)) s = .value (.nil, final) ∧ _
  rw [← square_adapter_call]
  exact double_readback out input s hwf hout hin hP

end Agave.Ed25519.SmallOrder.Execution
