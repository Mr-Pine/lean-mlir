import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Arithmetic
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Correctness
import SSA.Projects.Agave.Ed25519.Proof.SerialFieldMul.Word

namespace Agave.Ed25519.SerialPoint
open SerialFieldMul
section

/-- The 19-fold top carry fits both unsigned and signed LLVM arithmetic. -/
theorem weak_mul_nooverflow (x : BitVec 64) :
    (x >>> 51).umulOverflow 19#64 = false ∧
    (x >>> 51).smulOverflow 19#64 = false := by
  have hx : (x >>> 51).toNat < 2^13 := by
    have h := x.isLt
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num at h ⊢
    omega
  have hxi : (x >>> 51).toInt = ((x >>> 51).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at hx ⊢; omega)
  constructor
  · simp only [BitVec.umulOverflow, BitVec.toNat_ofNat,
      decide_eq_false_iff_not, not_le]
    norm_num at hx ⊢
    omega
  · simp only [BitVec.smulOverflow, hxi]
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at hx ⊢
    norm_num at hx ⊢
    omega

/-- The final limb-zero addition has both LLVM no-overflow properties for
arbitrary input words. The other four additions use `final_add_nooverflow`. -/
theorem weak_fold_nooverflow (x y : BitVec 64) :
    ((x >>> 51)*19#64).uaddOverflow (y &&& 2251799813685247#64) = false ∧
    ((x >>> 51)*19#64).saddOverflow (y &&& 2251799813685247#64) = false := by
  have hx : (x >>> 51).toNat < 2^13 := by
    have h := x.isLt
    simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    norm_num at h ⊢
    omega
  have hm : ((x >>> 51)*19#64).toNat < 2^18 := by
    have hp : (x >>> 51).toNat * 19 < 2^18 := by omega
    have hp64 : (x >>> 51).toNat * 19 < 2^64 := by omega
    rw [BitVec.toNat_mul]
    change ((x >>> 51).toNat * 19) % 2^64 < 2^18
    rw [Nat.mod_eq_of_lt hp64]
    exact hp
  have hy : (y &&& 2251799813685247#64).toNat < 2^51 := by
    simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
    change y.toNat &&& (2^51-1) < 2^51
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hmi : ((x >>> 51)*19#64).toInt = (((x >>> 51)*19#64).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at hm ⊢; omega)
  have hyi : (y &&& 2251799813685247#64).toInt =
      ((y &&& 2251799813685247#64).toNat : Int) :=
    BitVec.toInt_eq_toNat_of_lt (by norm_num at hy ⊢; omega)
  constructor
  · simp only [BitVec.uaddOverflow, decide_eq_false_iff_not, not_le]
    norm_num at hm hy ⊢
    omega
  · simp only [BitVec.saddOverflow, hmi, hyi, Bool.or_eq_false_iff,
      decide_eq_false_iff_not]
    constructor <;> omega

theorem weak_carry_add_nooverflow (x y : BitVec 64) :
    (x &&& 2251799813685247#64).uaddOverflow (y >>> 51) = false ∧
    (x &&& 2251799813685247#64).saddOverflow (y >>> 51) = false := by
  simpa only [BitVec.uaddOverflow, BitVec.saddOverflow, add_comm] using
    final_add_nooverflow y x

def weakWord (a : Fin 5 → BitVec 64) : Fin 5 → BitVec 64 := ![
  (a 4 >>> 51)*19 + (a 0 &&& 2251799813685247#64),
  (a 0 >>> 51) + (a 1 &&& 2251799813685247#64),
  (a 1 >>> 51) + (a 2 &&& 2251799813685247#64),
  (a 2 >>> 51) + (a 3 &&& 2251799813685247#64),
  (a 3 >>> 51) + (a 4 &&& 2251799813685247#64)]

/-- All mask, shift and word additions in weak reduction implement the natural
carry schedule. No input premise is needed because inputs are 64-bit words. -/
theorem weakWord_cast (a : Fin 5 → BitVec 64) :
    weakWord a = fun i => (weakReduce (unsigned a) i : BitVec 64) := by
  have hc (x : BitVec 64) : x = (x.toNat : BitVec 64) := by simp
  have hs (x : BitVec 64) : x >>> 51 = ((x.toNat / radix : Nat) : BitVec 64) := by
    conv_lhs => rw [hc x]
    exact word_shift64 x.toNat x.isLt
  have hl (x : BitVec 64) : x &&& 2251799813685247#64 =
      ((x.toNat % radix : Nat) : BitVec 64) := by
    conv_lhs => rw [hc x]
    exact word_low64 x.toNat
  funext i
  fin_cases i <;> simp [weakWord, weakReduce, hs, hl, unsigned, Nat.cast_add,
    Nat.cast_mul, add_comm, mul_comm]

theorem weakWord_unsigned (a : Fin 5 → BitVec 64) :
    unsigned (weakWord a) = weakReduce (unsigned a) := by
  funext i
  rw [weakWord_cast]
  simp only [unsigned, BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have ht := weakReduce_tight (unsigned a) (fun j => (a j).isLt) i
  norm_num at ht ⊢
  omega

end
end Agave.Ed25519.SerialPoint
