import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.LongBase
import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.SignedRadix

/-! Generic 64-bit LLVM instruction facts needed by the radix-2^21 scalar
reducer. `val` and `FitsLong` denote ordinary scalar i64 values and
bounds; no SIMD arithmetic or backend equivalence is assumed. -/

namespace Firedancer.Common.ScalarArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)

set_option maxHeartbeats 2000000

theorem mul_flags_ofInt {a b : Int} {flags : LLVM.NoWrapFlags}
    (ha : FitsLong a) (hb : FitsLong b) (hab : FitsLong (a * b))
    (hnuw : flags.nuw = true → 0 ≤ a ∧ 0 ≤ b) :
    LLVM.mul (val a) (val b) flags = val (a * b) := by
  simp only [val, LLVM.mul, PoisonOr.value_bind]
  rw [if_neg, if_neg]
  · simp [LLVM.mul?, BitVec.ofInt_mul]
  · rintro ⟨h1, h2⟩
    obtain ⟨ha0, hb0⟩ := hnuw h1
    simp only [BitVec.umulOverflow, ge_iff_le, decide_eq_true_eq] at h2
    have haN := toNat_ofInt ha ha0
    have hbN := toNat_ofInt hb hb0
    have hp : ((BitVec.ofInt 64 a).toNat : Int) *
        ((BitVec.ofInt 64 b).toNat : Int) = a * b := by rw [haN, hbN]
    have h2' : (2 ^ 64 : Int) ≤ ((BitVec.ofInt 64 a).toNat : Int) *
        ((BitVec.ofInt 64 b).toNat : Int) := by exact_mod_cast h2
    rw [hp] at h2'
    norm_num [FitsLong] at hab
    omega
  · rintro ⟨_, h2⟩
    simp only [BitVec.smulOverflow, ge_iff_le, decide_eq_true_eq, Bool.or_eq_true] at h2
    rw [toInt_ofInt ha, toInt_ofInt hb] at h2
    norm_num [FitsLong] at hab
    omega

private theorem highMask_bits (x : BitVec 64) :
    x &&& BitVec.ofInt 64 (-2097152) = (x.sshiftRight 21) <<< (21 : Nat) := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_shiftLeft, BitVec.getElem_sshiftRight]
  have hm : (BitVec.ofInt 64 (-2097152))[i] = decide (21 ≤ i) := by
    change (BitVec.ofInt 64 (-2097152)).getLsbD i = decide (21 ≤ i)
    interval_cases i <;> decide +kernel
  rw [hm]
  by_cases hlo : i < 21
  · simp [hlo, show ¬21 ≤ i by omega]
  · simp [hlo, show 21 ≤ i by omega, show i - 21 + 21 = i by omega, hi]

/-- The high-bit carry mask works for both positive and negative limbs. -/
theorem and_high21_ofInt {a : Int} (ha : FitsLong a) :
    LLVM.and (val a) (val (-2097152)) = val (a - a % 2097152) := by
  simp only [val, LLVM.and, PoisonOr.value_bind, LLVM.and?]
  rw [highMask_bits, BitVec.sshiftRight_eq, toInt_ofInt ha, Int.shiftRight_eq_div_pow]
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  have hpow : BitVec.twoPow 64 21 = BitVec.ofInt 64 2097152 := by decide +kernel
  rw [hpow, ← BitVec.ofInt_mul]
  congr 2
  have h := Int.emod_add_ediv_mul a 2097152
  norm_num
  omega

/-- `%170` uses a finite high mask because its operand is nonnegative and
below 2^43. The bound is an explicit premise rather than a silent truncation. -/
theorem and_finite_high21_ofInt {a : Int} (ha : FitsLong a)
    (hlo : 0 ≤ a) (hhi : a < 8796093022208) :
    LLVM.and (val a) (val 8796090925056) = val (a - a % 2097152) := by
  have hm : (BitVec.ofInt 64 8796090925056) =
      BitVec.ofInt 64 (-2097152) &&& BitVec.ofInt 64 (2 ^ 43 - 1) := by decide +kernel
  have hh := and_high21_ofInt ha
  simp only [val, LLVM.and, PoisonOr.value_bind, LLVM.and?, PoisonOr.value_inj] at hh ⊢
  rw [hm, ← BitVec.and_assoc, hh, and_mask_bv _ (by decide : 43 < 64)]
  congr 1
  have h0 := Int.emod_nonneg a (by decide : (2097152 : Int) ≠ 0)
  have h1 : a % 2097152 ≤ a := by omega
  apply Int.emod_eq_of_lt <;> norm_num at * <;> omega

end Firedancer.Common.ScalarArithmetic
