import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Refinement
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Contract
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ExecutionMemory

/-! Execution of the multiplication helper used by serial cached addition.
This links the real imported field kernel to the PP stage after the caller has
prepared its operands. It does not assert execution of the enclosing point
kernel: its allocation, preparation, remaining calls and stores still need
their own execution proof. -/
namespace Agave.Ed25519.SerialPoint.Execution

open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
open SerialFieldMul

/-- The actual multiplication call for PP = (Y+X) * cache.(Y+X).
The only preparation premises describe the input memory. Arithmetic safety and
the output invariant follow from the point and cache bounds. -/
theorem cached_add_pp_call (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40) (P C : LimbPoint)
    (hP : PointTight P) (hC : PointBounded C)
    (hleft : unsigned (readLimbs s a) = add P.Y P.X)
    (hright : unsigned (readLimbs s b) = C.Y) :
    ∃ output : Fin 5 → BitVec 64,
      kernel.call (kernel.args (.value r) (.value a) (.value b)) s =
        .value (.nil, { s with mem := storeLimbs s.mem r output }) ∧
      unsigned output = mul (add P.Y P.X) C.Y ∧
      Tight (unsigned output) ∧
      value (unsigned output) = (value P.Y + value P.X) * value C.Y := by
  have hsum := add_bounded P.Y P.X hP.2.1 hP.1
  have hA : Bounded (unsigned (readLimbs s a)) := hleft.symm ▸ hsum
  have hB : Bounded (unsigned (readLimbs s b)) := hright.symm ▸ hC.2.1
  have hout : unsigned (machine (readLimbs s a) (readLimbs s b)) =
      mul (add P.Y P.X) C.Y := by
    rw [machine_unsigned _ _ hA hB, hleft, hright]
    rfl
  refine ⟨machine (readLimbs s a) (readLimbs s b),
    kernel_call r a b s hwf hr ha hb, hout, ?_, ?_⟩
  · rw [hout]
    exact mul_tight _ _ hsum hC.2.1
  · rw [hout]
    simp only [mul, mul_value, add_value]

/-- The PP stage is observed in the returned memory, not just in an auxiliary
output vector. Aliasing input and output is allowed by the field kernel. -/
theorem cached_add_pp_readback (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40) (P C : LimbPoint)
    (hP : PointTight P) (hC : PointBounded C)
    (hleft : unsigned (readLimbs s a) = add P.Y P.X)
    (hright : unsigned (readLimbs s b) = C.Y) :
    ∃ final : GlobalState,
      kernel.call (kernel.args (.value r) (.value a) (.value b)) s =
        .value (.nil, final) ∧
      unsigned (readLimbs final r) = mul (add P.Y P.X) C.Y ∧
      Tight (unsigned (readLimbs final r)) ∧
      value (unsigned (readLimbs final r)) = (value P.Y + value P.X) * value C.Y := by
  obtain ⟨output, hcall, hout, htight, hvalue⟩ :=
    cached_add_pp_call r a b s hwf hr ha hb P C hP hC hleft hright
  refine ⟨{ s with mem := storeLimbs s.mem r output }, hcall, ?_⟩
  rw [readLimbs_storeLimbs s r output hr]
  exact ⟨hout, htight, hvalue⟩

end Agave.Ed25519.SerialPoint.Execution
