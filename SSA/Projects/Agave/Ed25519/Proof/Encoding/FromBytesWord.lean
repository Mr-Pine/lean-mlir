import SSA.Projects.Agave.Ed25519.Proof.Encoding.FieldBytes
import Mathlib.Tactic

namespace Agave.Ed25519.Encoding
section

/-- Exact 64-bit loads, shifts and masks in FieldElement51::from_bytes.
The input word denotes the little-endian contents of the 32-byte array. -/
def fromBytesWord (bytes : BitVec 256) : Field.Serial := ![
  bytes.extractLsb' 0 64 &&& 2251799813685247,
  (bytes.extractLsb' 48 64 >>> 3) &&& 2251799813685247,
  (bytes.extractLsb' 96 64 >>> 6) &&& 2251799813685247,
  (bytes.extractLsb' 152 64 >>> 1) &&& 2251799813685247,
  (bytes.extractLsb' 192 64 >>> 12) &&& 2251799813685247]

theorem fromBytesWord_slice (bytes : BitVec 256) (i : Fin 5) :
    fromBytesWord bytes i = (bytes.extractLsb' (51*i.val) 51).setWidth 64 := by
  fin_cases i <;> simp only [fromBytesWord, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  all_goals
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    interval_cases j <;>
      simp [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
        BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat]

theorem fromBytesWord_toNat (bytes : BitVec 256) (i : Fin 5) :
    (fromBytesWord bytes i).toNat = fromBytes bytes.toNat i := by
  rw [fromBytesWord_slice, BitVec.toNat_setWidth_of_le (by decide : 51 ≤ 64)]
  fin_cases i <;> simp [BitVec.extractLsb', BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, fromBytes, radix]

/-- All 256 input bits are covered, with precisely the sign bit discarded. -/
theorem fromBytesWord_value (bytes : BitVec 256) :
    Field.serialValue (fromBytesWord bytes) =
      (bytes.extractLsb' 0 255).toNat := by
  simp only [Field.serialValue, fromBytesWord_toNat]
  rw [← value_eq_decode51, fromBytes_value]
  simp [BitVec.extractLsb', BitVec.toNat_ofNat, top]

end
end Agave.Ed25519.Encoding
