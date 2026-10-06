import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBox
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Field
import SSA.Projects.RIR.Run.Scalar

/-! The emitted sign-byte extraction and flagged mask construction. These
lemmas are instruction arithmetic contracts; they do not assert that the
earlier decoder blocks reach this computation. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution
open LeanMLIR.RIR

/-- The last-byte shift produces a valid subtle Choice for every byte. -/
theorem sign_byte : ∀ byte : BitVec 8,
    byte >>> 7 = if byte[7] then 1#8 else 0#8 := by
  intro byte
  apply BitVec.eq_of_toNat_eq
  have hb := byte.isLt
  have ht : byte[7] = decide (128 ≤ byte.toNat) := by
    exact (BitVec.getLsbD_eq_getElem (x := byte) (by decide : 7 < 8)).symm.trans
      (BitVec.getLsbD_last byte)
  rw [ht]
  split <;>
    simp_all [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega


/-- The signed subtraction promise on the mask construction holds for every
input byte, because the seven-bit shift leaves only 0 or 1. -/
theorem sign_mask_nooverflow (byte : BitVec 8) :
    (0#64).ssubOverflow ((byte >>> 7).setWidth 64) = false := by
  rw [sign_byte]
  cases byte[7] <;> decide


/-- The scalar `nsw` subtraction actually executes without poison. -/
theorem sign_mask_operation (byte : BitVec 8) :
    Operation.sub {nsw := true} (.value 0#64) (.value ((byte >>> 7).setWidth 64)) =
      .value (if byte[7] then (-1#64) else 0#64) := by
  simp only [Operation.sub, PoisonOr.value_bind, sign_mask_nooverflow,
    Bool.false_eq_true, and_false, false_and, ite_false, PoisonOr.pure_def]
  rw [sign_byte]
  cases byte[7] <;> rfl


end Agave.Ed25519.Encoding.Decompress.Execution
