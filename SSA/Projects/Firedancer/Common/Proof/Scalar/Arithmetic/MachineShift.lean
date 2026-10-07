import SSA.Projects.Firedancer.Common.Proof.Scalar.Arithmetic.MachineLong

namespace Firedancer.Common.ScalarArithmetic
open LeanMLIR SLLVM
open InstCombine (LLVM)
open R43x6 (FitsLong)

/-- Exact signed shift flag check, derived from the signed input and product
bounds. This is used for the four `nsw` shifts in final packing. -/
theorem shl_nsw_ofInt {a : Int} {n : Nat} (ha : FitsLong a)
    (hp : FitsLong (a * 2 ^ n)) (hn : n < 64) :
    LLVM.shl (val a) (.value (BitVec.ofNat 64 n)) { nsw := true } =
      .value (BitVec.ofInt 64 a <<< n) := by
  have hn64 : n < 2 ^ 64 := by omega
  have hnat : (BitVec.ofNat 64 n).toNat = n := by simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
  have hpow : BitVec.twoPow 64 n = BitVec.ofInt 64 (2 ^ n) := by
    have hc : (2 : Int) ^ n = ((2 ^ n : Nat) : Int) := by norm_cast
    rw [hc, BitVec.ofInt_natCast]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow]
  have hs : BitVec.ofInt 64 a <<< n = BitVec.ofInt 64 (a * 2 ^ n) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow, hpow, ← BitVec.ofInt_mul]
  have hback : (BitVec.ofInt 64 a <<< n).sshiftRight n = BitVec.ofInt 64 a := by
    rw [hs, BitVec.sshiftRight_eq, toInt_ofInt hp, Int.shiftRight_eq_div_pow]
    congr 1
    exact Int.mul_ediv_cancel _ (by positivity)
  have hbound : ¬ BitVec.ofNat 64 n ≥ (64#64) := by
    simp only [ge_iff_le, BitVec.le_def, hnat]
    exact Nat.not_le_of_gt hn
  simp [val, LLVM.shl, LLVM.shl?, BitVec.sshiftRight',
    BitVec.shiftLeft_eq', hnat, hback, hbound]

end Firedancer.Common.ScalarArithmetic
