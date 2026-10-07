import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Contract
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ExecutionMemory

/-! Reuse the actual multiplication kernel's execution proof at each of the
four equality call sites. The enclosing point body must still establish these
input ranges and coordinate bounds at each site. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR SerialFieldMul
open Reduce64.Execution (SmallRange)

private theorem serialValue_decode (a : Field.Serial) :
    Field.serialValue a = decode (unsigned a) := by
  unfold Field.serialValue
  rw [← Encoding.value_eq_decode51]
  rfl

/-- A concrete field-multiplication call and its output readback in the field
used by the canonical point-equality arithmetic. All machine flags are handled
by the existing kernel theorem, not assumed here. -/
theorem field_product_call (r a b : Pointer) (s : GlobalState) (hwf : s.WF)
    (hr : SmallRange s.mem r 40) (ha : SmallRange s.mem a 40)
    (hb : SmallRange s.mem b 40)
    (hA : Bounded (unsigned (readLimbs s a)))
    (hB : Bounded (unsigned (readLimbs s b))) :
    ∃ output : Field.Serial,
      kernel.call (kernel.args (.value r) (.value a) (.value b)) s =
        .value (.nil, {s with mem := storeLimbs s.mem r output}) ∧
      readLimbs {s with mem := storeLimbs s.mem r output} r = output ∧
      (Field.serialValue output : K) =
        (Field.serialValue (readLimbs s a) : K) *
          (Field.serialValue (readLimbs s b) : K) ∧
      Bounded (unsigned output) := by
  obtain ⟨output, hcall, hmod, _, _, hbound⟩ :=
    kernel_correct r a b s hwf hr ha hb hA hB
  refine ⟨output, hcall,
    SerialPoint.Execution.readLimbs_storeLimbs s r output hr, ?_, hbound⟩
  rw [serialValue_decode, serialValue_decode, serialValue_decode, ← Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).2 hmod

end Agave.Ed25519.SmallOrder.Execution
