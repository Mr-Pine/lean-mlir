import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorCacheArithmetic
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionInstructions

/-! Exact, flagged scalar operations in the constructor's optimized scale/reduce pass. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.CacheScale
open LeanMLIR.RIR Avx2PointAdd
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

def natWord (n : Nat) : Operation.IntW 64 := .value (BitVec.ofNat 64 n)

theorem add_nat (x y : Nat) (hx : x < 2^62) (hy : y < 2^62) :
    Operation.add {nsw := true, nuw := true} (natWord x) (natWord y) =
      natWord (x+y) := by
  have hx64 : x < 2^64 := by omega
  have hy64 : y < 2^64 := by omega
  have hxi : (BitVec.ofNat 64 x).toInt = (x : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64]
    · simp only [BitVec.toNat_ofNat]; norm_num at hx ⊢; omega
  have hyi : (BitVec.ofNat 64 y).toInt = (y : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy64]
    · simp only [BitVec.toNat_ofNat]; norm_num at hy ⊢; omega
  have hs : (BitVec.ofNat 64 x).saddOverflow (BitVec.ofNat 64 y) = false := by
    simp only [BitVec.saddOverflow, hxi, hyi]
    norm_num at hx hy ⊢
    omega
  have hu : (BitVec.ofNat 64 x).uaddOverflow (BitVec.ofNat 64 y) = false := by
    simp only [BitVec.uaddOverflow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hy64]
    norm_num at hx hy ⊢
    omega
  simp [natWord, Operation.add, hs, hu, BitVec.ofNat_add]

theorem mul_nat (x y : Nat) (hx : x < 2^63) (hy : y < 2^63)
    (hxy : x*y < 2^63) :
    Operation.mul {nsw := true, nuw := true} (natWord x) (natWord y) =
      natWord (x*y) := by
  have hx64 : x < 2^64 := by omega
  have hy64 : y < 2^64 := by omega
  have hxi : (BitVec.ofNat 64 x).toInt = (x : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx64]; norm_num at hx ⊢; omega
  have hyi : (BitVec.ofNat 64 y).toInt = (y : Int) := by
    rw [BitVec.toInt_eq_toNat_of_lt]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy64]
    · simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy64]; norm_num at hy ⊢; omega
  have hs : (BitVec.ofNat 64 x).smulOverflow (BitVec.ofNat 64 y) = false := by
    simp only [BitVec.smulOverflow, hxi, hyi]
    norm_num
    constructor
    · exact_mod_cast hxy
    · omega
  have hu : (BitVec.ofNat 64 x).umulOverflow (BitVec.ofNat 64 y) = false := by
    simp only [BitVec.umulOverflow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hx64, Nat.mod_eq_of_lt hy64]
    norm_num at hxy ⊢
    omega
  simp [natWord, Operation.mul, hs, hu, BitVec.ofNat_mul]

theorem shr_nat (x n : Nat) (hx : x < 2^64) (hn : n < 64) :
    Operation.lshr false (natWord x) (natWord n) = natWord (x / 2^n) := by
  have hn64 : n < 2^64 := by omega
  have hword : (BitVec.ofNat 64 x >>> n) = BitVec.ofNat 64 (x / 2^n) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hn64, Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) hx)).symm
  simp only [natWord, Operation.lshr, PoisonOr.value_bind, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hn64, Nat.not_le.mpr hn, ite_false, Bool.false_eq_true, PoisonOr.pure_def]
  exact congrArg PoisonOr.value hword

theorem and_nat (x m : Nat) (hx : x < 2^64) (hm : m < 2^64) :
    Operation.and (natWord x) (natWord m) = natWord (x &&& m) := by
  simp [natWord, Operation.and, BitVec.ofNat_and]

theorem and_mask26 (x : Nat) (hx : x < 2^64) :
    Operation.and (natWord x) (natWord 67108863) = natWord (x % 2^26) := by
  rw [and_nat x _ hx (by decide)]
  congr 1
  exact Nat.and_two_pow_sub_one_eq_mod x 26

theorem and_mask25 (x : Nat) (hx : x < 2^64) :
    Operation.and (natWord x) (natWord 33554431) = natWord (x % 2^25) := by
  rw [and_nat x _ hx (by decide)]
  congr 1
  exact Nat.and_two_pow_sub_one_eq_mod x 25

theorem even_mask_nat (x : Nat) (hx : x % 2 = 0) :
    x &&& 67108862 = x % 2^26 := by
  have hm : (67108863 : Nat) = 67108862 ||| 1 := by decide
  have he : x &&& 67108863 = x &&& 67108862 := by
    rw [hm, Nat.and_or_distrib_left, Nat.and_one_is_mod, hx, Nat.or_zero]
  rw [← he]
  exact Nat.and_two_pow_sub_one_eq_mod x 26

theorem and_even_mask26 (x : Nat) (hx : x < 2^64) (he : x % 2 = 0) :
    Operation.and (natWord x) (natWord 67108862) = natWord (x % 2^26) := by
  rw [and_nat x _ hx (by decide), even_mask_nat x he]

end Agave.Ed25519.Tables.Avx2Constructor.CacheScale
