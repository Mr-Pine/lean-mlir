import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.PackingSource
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.InputValue

namespace Firedancer.Common.ScalarArithmetic
open IntegerRegisters

private theorem extract21_value (a : Int) :
    (((BitVec.ofInt 64 a).extractLsb' 0 21).toNat : Int) = a % 2097152 := by
  change (((BitVec.ofInt 64 a).setWidth 21).toNat : Int) = _
  rw [BitVec.toNat_setWidth, Int.natCast_emod, Int.natCast_pow]
  have hc : ((BitVec.ofInt 64 a).toNat : Int) = a % 2 ^ 64 := by
    rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    norm_num
  rw [hc]
  norm_num

private theorem extract25_value (a : Int) (ha : 0 ≤ a) (ha' : a < 2 ^ 25) :
    (((BitVec.ofInt 64 a).extractLsb' 0 25).toNat : Int) = a := by
  change (((BitVec.ofInt 64 a).setWidth 25).toNat : Int) = _
  rw [BitVec.toNat_setWidth, Int.natCast_emod, Int.natCast_pow]
  have hc : ((BitVec.ofInt 64 a).toNat : Int) = a % 2 ^ 64 := by
    rw [BitVec.toNat_ofInt, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))]
    norm_num
  rw [hc]
  norm_num at ha' ⊢
  exact Int.emod_eq_of_lt ha ha'

private theorem top_output_nonnegative (d : Digits) (hd : Bounded d) : 0 ≤ z446 d := by
  have ho := (output_bounds d hd).1
  have h426 := z426_bounds d hd
  have h425 := Int.emod_lt_of_pos (z425 d) (by decide : (0 : Int) < 2097152)
  have h428 := Int.emod_lt_of_pos (z428 d) (by decide : (0 : Int) < 2097152)
  have h430 := Int.emod_lt_of_pos (z430 d) (by decide : (0 : Int) < 2097152)
  have h432 := Int.emod_lt_of_pos (z432 d) (by decide : (0 : Int) < 2097152)
  have h434 := Int.emod_lt_of_pos (z434 d) (by decide : (0 : Int) < 2097152)
  have h436 := Int.emod_lt_of_pos (z436 d) (by decide : (0 : Int) < 2097152)
  have h438 := Int.emod_lt_of_pos (z438 d) (by decide : (0 : Int) < 2097152)
  have h440 := Int.emod_lt_of_pos (z440 d) (by decide : (0 : Int) < 2097152)
  have h442 := Int.emod_lt_of_pos (z442 d) (by decide : (0 : Int) < 2097152)
  have h444 := Int.emod_lt_of_pos (z444 d) (by decide : (0 : Int) < 2097152)
  unfold outputValue at ho
  omega

set_option maxHeartbeats 2000000 in
theorem packed_output_value (d : Digits) (hd : Bounded d) :
    ((packWords (packingWords (packingInputs d))).toNat : Int) = outputValue d := by
  have hlo := top_output_nonnegative d hd
  have hhi : z446 d < 2 ^ 25 := by
    have h := z446_bounds d hd
    norm_num
    omega
  rw [packingWords_bits]
  simp only [packingBits, append_natValue]
  simp only [
    show packingInputs d 0 = BitVec.ofInt 64 (z413 d) from rfl,
    show packingInputs d 1 = BitVec.ofInt 64 (z425 d) from rfl,
    show packingInputs d 2 = BitVec.ofInt 64 (z428 d) from rfl,
    show packingInputs d 3 = BitVec.ofInt 64 (z430 d) from rfl,
    show packingInputs d 4 = BitVec.ofInt 64 (z432 d) from rfl,
    show packingInputs d 5 = BitVec.ofInt 64 (z434 d) from rfl,
    show packingInputs d 6 = BitVec.ofInt 64 (z436 d) from rfl,
    show packingInputs d 7 = BitVec.ofInt 64 (z438 d) from rfl,
    show packingInputs d 8 = BitVec.ofInt 64 (z440 d) from rfl,
    show packingInputs d 9 = BitVec.ofInt 64 (z442 d) from rfl,
    show packingInputs d 10 = BitVec.ofInt 64 (z444 d) from rfl,
    show packingInputs d 11 = BitVec.ofInt 64 (z446 d) from rfl]
  rw [extract25_value _ hlo hhi]
  simp only [extract21_value, outputValue, z426]
  norm_num
  ring

end Firedancer.Common.ScalarArithmetic
