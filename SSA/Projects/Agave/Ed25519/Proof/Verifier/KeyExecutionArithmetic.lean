import SSA.Projects.Agave.Ed25519.Proof.Reduce64.ScalarSafety
import SSA.Projects.RIR.Run.Tactic

/-! Safety of every flagged carry in the constructor's two inline negations.
These bounds hold even for arbitrary machine words. -/
namespace Agave.Ed25519.Verifier.Execution.Key
open LeanMLIR.RIR

private theorem add_flags (x y : BitVec 64)
    (hx : x.toNat < 2^62) (hy : y.toNat < 2^62) :
    x.saddOverflow y = false ∧ x.uaddOverflow y = false := by
  have hxi := BitVec.toInt_eq_toNat_of_lt (x := x) (by norm_num at hx ⊢; omega)
  have hyi := BitVec.toInt_eq_toNat_of_lt (x := y) (by norm_num at hy ⊢; omega)
  simp only [BitVec.saddOverflow, BitVec.uaddOverflow, hxi, hyi]
  norm_num at hx hy ⊢
  omega

theorem mask51_toNat (x : BitVec 64) :
    (x &&& 2251799813685247#64).toNat = x.toNat % 2^51 := by
  change x.toNat &&& (2^51 - 1) = _
  exact Nat.and_two_pow_sub_one_eq_mod _ _

theorem carry_mask51_flags (x y : BitVec 64) :
    (x &&& 2251799813685247#64).saddOverflow (y >>> 51) = false ∧
    (x &&& 2251799813685247#64).uaddOverflow (y >>> 51) = false := by
  apply add_flags
  · rw [mask51_toNat]; omega
  · have hy := y.isLt
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num at *
    omega

theorem fold_mask51_flags (x y : BitVec 64) :
    ((x >>> 51) * 19#64).saddOverflow (y &&& 2251799813685247#64) = false ∧
    ((x >>> 51) * 19#64).uaddOverflow (y &&& 2251799813685247#64) = false := by
  apply add_flags
  · have hx := x.isLt
    have hm := Nat.mod_le ((x.toNat / 2^51) * 19) (2^64)
    simp only [BitVec.toNat_mul, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num at *
    omega
  · rw [mask51_toNat]; omega

end Agave.Ed25519.Verifier.Execution.Key
