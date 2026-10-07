import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.AddbackArithmetic

/-! Algebraic observation of the exact five-word conditional addback. The top
word deliberately wraps; reducing modulo 2^52 absorbs its u64 wrap. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction

open Agave.Ed25519.Bridge
open Agave.Ed25519.ScalarReduce32.Arithmetic (limbs radix)
set_option exponentiation.threshold 512

/-- The logical high-bit byte and arithmetic sign broadcast encode the same
bit. This holds for every u64 word, independent of its arithmetic provenance. -/
theorem borrowByte_of_shift (word : BitVec 64) (borrow : Nat) (hb : borrow ≤ 1)
    (hs : word.sshiftRight 63 = if borrow = 1 then -1 else 0) :
    (word >>> 63).setWidth 8 = BitVec.ofNat 8 borrow := by
  have hw := word.isLt
  rw [sign_mask] at hs
  have hh : borrow = 0 ∨ borrow = 1 := by omega
  rcases hh with rfl | rfl <;>
    cases hm : word.msb <;>
    simp only [hm, Bool.false_eq_true, ↓reduceIte] at hs
  · apply BitVec.eq_of_toNat_eq
    have ht := BitVec.msb_eq_false_iff_two_mul_lt.mp hm
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num at ht hw ⊢
    omega
  · have hf : (-1 : BitVec 64) ≠ 0 := by decide +kernel
    exact False.elim (hf hs)
  · have hf : (0 : BitVec 64) ≠ -1 := by decide +kernel
    exact False.elim (hf hs)
  · apply BitVec.eq_of_toNat_eq
    have ht := BitVec.msb_eq_true_iff_two_mul_ge.mp hm
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftRight_eq_div_pow]
    norm_num at ht hw ⊢
    omega

/-- A low-52-bit mask commutes with arbitrary u64 wrapping additions. -/
theorem mask_add_three (a b c : BitVec 64) :
    ((a + b + c) &&& 4503599627370495#64).toNat =
      (a.toNat % 2 ^ 52 + b.toNat + c.toNat) % 2 ^ 52 := by
  rw [ScalarMontgomeryMul.mask52_toNat, BitVec.toNat_add, BitVec.toNat_add]
  have hd : 2 ^ 52 ∣ 2 ^ 64 := by decide +kernel
  simp only [Nat.add_mod, Nat.mod_mod_of_dvd _ hd, Nat.mod_mod]

/-- Word addback refines its complete natural carry chain. This theorem is an
observation theorem for the exact word expression; the instruction proof must
also apply the corresponding nonpoison flag lemmas. -/
theorem addback_refine (d : Limbs) (digits : Fin 5 → Nat) (borrow : Nat)
    (hd : ∀ i, (d i &&& 4503599627370495#64).toNat = digits i)
    (hb : borrow ≤ 1) (hbyte : borrowByte d = BitVec.ofNat 8 borrow) :
    ∀ i, (addback d i).toNat = addbackSums digits borrow i % 2 ^ 52 := by
  let mask := (0 : BitVec 64) - (borrowByte d).setWidth 64
  have hb01 : borrow = 0 ∨ borrow = 1 := by omega
  have hk0 : (mask &&& 671914833335277#64).toNat = borrow * 671914833335277 := by
    rcases hb01 with h | h <;> simp [mask, hbyte, h]
  have hk1 : (mask &&& 3916664325105025#64).toNat = borrow * 3916664325105025 := by
    rcases hb01 with h | h <;> simp [mask, hbyte, h]
  have hk2 : (mask &&& 1367801#64).toNat = borrow * 1367801 := by
    rcases hb01 with h | h <;> simp [mask, hbyte, h]
  have hk4 : (mask &&& 17592186044416#64).toNat = borrow * 17592186044416 := by
    rcases hb01 with h | h <;> simp [mask, hbyte, h]
  have hdBound (i : Fin 5) : digits i < 2 ^ 52 := by
    rw [← hd i, ScalarMontgomeryMul.mask52_toNat]
    exact Nat.mod_lt _ (by decide)
  have hbounds := addbackSums_bounds digits borrow hdBound hb
  let t0 := (d 0 &&& 4503599627370495#64) + (mask &&& 671914833335277#64)
  let t1 := (t0 >>> 52) + (mask &&& 3916664325105025#64) +
    (d 1 &&& 4503599627370495#64)
  let t2 := (d 2 &&& 4503599627370495#64) + (mask &&& 1367801#64) + (t1 >>> 52)
  let t3 := (t2 >>> 52) + (d 3 &&& 4503599627370495#64)
  let t4 := d 4 + (mask &&& 17592186044416#64) + (t3 >>> 52)
  have hv0 : t0.toNat = addbackSums digits borrow 0 := by
    have h := (hbounds 0).1
    simp only [t0, BitVec.toNat_add, hd, hk0]
    change (digits 0 + borrow * 671914833335277) % 2 ^ 64 = _
    apply Nat.mod_eq_of_lt
    exact h.trans (by decide)
  have hs0 : (t0 >>> 52).toNat = addbackSums digits borrow 0 / 2 ^ 52 := by
    change t0.toNat >>> 52 = _
    rw [hv0, Nat.shiftRight_eq_div_pow]
  have hv1 : t1.toNat = addbackSums digits borrow 1 := by
    have h := (hbounds 1).1
    simp only [t1, BitVec.toNat_add, hs0, hk1, hd]
    change ((_ + _) % 2 ^ 64 + _) % 2 ^ 64 = _
    simp only [addbackSums] at h ⊢
    norm_num at h ⊢
    omega
  have hs1 : (t1 >>> 52).toNat = addbackSums digits borrow 1 / 2 ^ 52 := by
    change t1.toNat >>> 52 = _
    rw [hv1, Nat.shiftRight_eq_div_pow]
  have hv2 : t2.toNat = addbackSums digits borrow 2 := by
    have h := (hbounds 2).1
    simp only [t2, BitVec.toNat_add, hs1, hk2, hd]
    simp only [addbackSums] at h ⊢
    norm_num at h ⊢
    omega
  have hs2 : (t2 >>> 52).toNat = addbackSums digits borrow 2 / 2 ^ 52 := by
    change t2.toNat >>> 52 = _
    rw [hv2, Nat.shiftRight_eq_div_pow]
  have hv3 : t3.toNat = addbackSums digits borrow 3 := by
    have h := (hbounds 3).1
    simp only [t3, BitVec.toNat_add, hs2, hd]
    simp only [addbackSums] at h ⊢
    norm_num at h ⊢
    omega
  have hs3 : (t3 >>> 52).toNat = addbackSums digits borrow 3 / 2 ^ 52 := by
    change t3.toNat >>> 52 = _
    rw [hv3, Nat.shiftRight_eq_div_pow]
  have hv4 : (t4 &&& 4503599627370495#64).toNat =
      addbackSums digits borrow 4 % 2 ^ 52 := by
    dsimp only [t4]
    rw [mask_add_three, ← ScalarMontgomeryMul.mask52_toNat (d 4), hd,
      hk4, hs3]
    rfl
  intro i
  fin_cases i
  · exact (ScalarMontgomeryMul.mask52_toNat t0).trans (congrArg (· % 2 ^ 52) hv0)
  · exact (ScalarMontgomeryMul.mask52_toNat t1).trans (congrArg (· % 2 ^ 52) hv1)
  · exact (ScalarMontgomeryMul.mask52_toNat t2).trans (congrArg (· % 2 ^ 52) hv2)
  · exact (ScalarMontgomeryMul.mask52_toNat t3).trans (congrArg (· % 2 ^ 52) hv3)
  · exact hv4

/-- The exact five machine addback words represent the conditional subtraction
of the subgroup order. This does not assume complete RIR execution. -/
theorem conditional_subtract_words (x : Fin 5 → BitVec 52) :
    let words := addback (differences (x 0) (x 1) (x 2) (x 3) (x 4))
    limbs (words 0).toNat (words 1).toNat (words 2).toNat (words 3).toNat (words 4).toNat =
      if rawValue x < subgroupOrder then rawValue x else rawValue x - subgroupOrder := by
  let d := differences (x 0) (x 1) (x 2) (x 3) (x 4)
  have hd := differences_refine x
  have hb := (borrowSteps_certificate x).1 4
  have hbyte : borrowByte d = BitVec.ofNat 8 (borrowSteps x 4).2 :=
    borrowByte_of_shift (d 4) _ hb.2 (hd 4).2
  have ha := addback_refine d (fun i => (borrowSteps x i).1) (borrowSteps x 4).2
    (fun i => (hd i).1) hb.2 hbyte
  change limbs ((addback d 0).toNat) ((addback d 1).toNat) ((addback d 2).toNat)
    ((addback d 3).toNat) ((addback d 4).toNat) = _
  simp only [ha]
  exact borrow_addback_exact x

/-- A 52-bit append is precisely one radix-52 positional step. -/
theorem append52_toNat (hi : BitVec n) (lo : BitVec 52) :
    (hi ++ lo).toNat = hi.toNat * 2 ^ 52 + lo.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt lo.isLt, Nat.shiftLeft_eq]

/-- The bitvector packing convention agrees with the natural limb polynomial. -/
theorem packed_toNat (x0 x1 x2 x3 x4 : BitVec 52) :
    (packed x0 x1 x2 x3 x4).toNat =
      limbs x0.toNat x1.toNat x2.toNat x3.toNat x4.toNat := by
  simp only [packed, append52_toNat]
  norm_num [limbs, radix]
  omega

/-- Exact packed260 conditional-subtraction identity, proved algebraically
from local borrow and addback equations. No bitblasting is involved. -/
theorem packed_conditional_subtract (x : Fin 5 → BitVec 52) :
    packedOutput (addback (differences (x 0) (x 1) (x 2) (x 3) (x 4))) =
      BitVec.ofNat 260 (if rawValue x < subgroupOrder then rawValue x
        else rawValue x - subgroupOrder) := by
  let words := addback (differences (x 0) (x 1) (x 2) (x 3) (x 4))
  have hword (i : Fin 5) : (words i).toNat < 2 ^ 52 := by
    fin_cases i <;> change (_ &&& 4503599627370495#64).toNat < 2 ^ 52 <;>
      rw [ScalarMontgomeryMul.mask52_toNat] <;> exact Nat.mod_lt _ (by decide)
  have hraw : rawValue x < 2 ^ 260 := by
    exact Agave.Ed25519.ScalarReduce32.Arithmetic.adjustment_bound _ _ _ _ _
      (x 0).isLt (x 1).isLt (x 2).isLt (x 3).isLt (x 4).isLt
  have hout : (if rawValue x < subgroupOrder then rawValue x
      else rawValue x - subgroupOrder) < 2 ^ 260 := by split_ifs <;> omega
  apply BitVec.eq_of_toNat_eq
  change (packedOutput words).toNat = _
  simp only [packedOutput, packed_toNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (hword _), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hout]
  exact conditional_subtract_words x

end Agave.Ed25519.Verifier.Execution.ScalarWide.Subtraction
