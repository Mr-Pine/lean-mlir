import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.DoubleCall
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorConcreteExecution
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorPayload

/-! The exact imported multiplication-by-eight call, including all lower RIR
calls, its caller-memory frame, and its group-valued verifier contract. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialPoint SerialPoint.Execution
open Reduce64.Execution (SmallRange)
open Verifier.Execution

/-- The pinned cofactor program executes all three doublings for k=3. -/
theorem cofactor_call_three (out input : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120) :
    cofactorProgram.call
      (.cons (.value out) (.cons (.value input) (.cons (.value 3) .nil))) s =
      .value (.nil, cofactorState s out input) := by
  exact cofactor_call_three_of_double cofactorPrimitives.projectiveDouble
    projective_double_call out input s hwf hout hin

/-- The exact final state contains the twenty output words and nineteen
consumed private allocations. No phase or lower-call premise remains. -/
theorem cofactor_call_three_normal (out input : Pointer) (s : GlobalState)
    (hwf : s.WF) (hout : SmallRange s.mem out 160) (hin : SmallRange s.mem input 120) :
    cofactorProgram.call
      (.cons (.value out) (.cons (.value input) (.cons (.value 3) .nil))) s =
      .value (.nil, pointPost s out
        (pointToWords (eightTimesWord (readWordPoint s input))) 19) := by
  rw [cofactor_call_three out input s hwf hout hin,
    cofactorState_eq_pointPost s out input hwf hout hin]

/-- The verifier's cofactor contract follows from actual imported execution.
Input validity is already carried by ValidPoint; no extra representation,
phase, or arithmetic premise is required. -/
theorem cofactorContract :
    Dalek.CofactorContract cofactorProgram.call
      (Verifier.Execution.ValidPoint.layout SmallOrder.ValidPoint.timesEight) := by
  intro out input s P hwf hout hin _hdisjoint
  have hi120 := smallRange_add hin.1 (k := 0) (count := 120) (by decide)
  simp only [Pointer.add_zero] at hi120
  exact ⟨cofactorState s out input, cofactor_call_three out input s hwf hout hi120,
    cofactorState_frame s out input hwf hout hi120,
    cofactorState_payload s out input P hwf hout hin⟩

end Agave.Ed25519.SmallOrder.Execution
