/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Proof.Long
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_biased_carry_propagate_limbs
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_mod_nearly_reduced_limbs

/-!
# The facts a walk over `reduce` needs

`fd_r43x6_is_nonzero` and `fd_r43x6_diagnose` both run the header's

    fd_r43x6_biased_carry_propagate_limbs( l, l, 1L<<20 );
    fd_r43x6_mod_nearly_reduced_limbs( l, l );

and both walk the emitted code instruction by instruction. Each step needs the
same two kinds of fact: the recurrence its instruction computes (`_y0 += 19L`
is `mnrA y 0 = y 0 + 19`) and the `R43x6.FitsLong` bound that keeps its `nsw`
from denoting poison. `ReduceFacts` is all of them, and `reduceFacts` derives
them from the one hypothesis the caller has, `BcpPre (2^20) l`.
-/

namespace Firedancer.Avx512
open R43x6 (FitsLong)

/-- The bias, the mask and the `19` as `long`s. -/
theorem fitsLong_bias : FitsLong (-((2 : ℤ) ^ 20)) := by simp [R43x6.FitsLong]
theorem fitsLong_bias' : FitsLong ((2 : ℤ) ^ 20) := by simp [R43x6.FitsLong]
theorem fitsLong_19 : FitsLong (19 : ℤ) := by simp [R43x6.FitsLong]

/-- `q = y >> 255` is zero exactly below `2^40`, on the non-negative chain the
`_y0 += 19` pass produces. -/
theorem mnrQ_eq_zero_iff {y : Fin R43x6.limbCount → ℤ} (h : 0 ≤ mnrA y 5) :
    mnrQ y = 0 ↔ mnrA y 5 < 2 ^ 40 := by
  simp only [mnrQ, R43x6.shiftRight_eq]; omega

/-- What a walk over `reduce l` needs about the model, for `l` and the limbs
`y` the carry propagate returns. The names are the walk's: `f*` bounds an
`nsw` operand, `h*` is a recurrence the code computes, `hb*` a limb's range. -/
structure ReduceFacts (l y : Fin R43x6.limbCount → ℤ) : Prop where
  fa : ∀ i, FitsLong (bcpA (2 ^ 20) l i)
  fmul : FitsLong ((19 : ℤ) * (bcpA (2 ^ 20) l 5 >>> 40))
  fmul' : FitsLong ((bcpA (2 ^ 20) l 5 >>> 40) * 19)
  f54 : FitsLong (bcpA (2 ^ 20) l 5 % 2 ^ 40 + 2 ^ 20)
  f55 : FitsLong (bcpA (2 ^ 20) l 5 % 2 ^ 40 + 2 ^ 20 + bcpA (2 ^ 20) l 4 >>> 43)
  ha5 : bcpA (2 ^ 20) l 5 = l 5 + (-((2 : ℤ) ^ 20))
  ha0 : bcpA (2 ^ 20) l 0 = (19 : ℤ) * (bcpA (2 ^ 20) l 5 >>> 40) + l 0
  ha1 : bcpA (2 ^ 20) l 1 = (bcpA (2 ^ 20) l 0 >>> 43) + l 1
  ha2 : bcpA (2 ^ 20) l 2 = (bcpA (2 ^ 20) l 1 >>> 43) + l 2
  ha3 : bcpA (2 ^ 20) l 3 = (bcpA (2 ^ 20) l 2 >>> 43) + l 3
  ha4 : bcpA (2 ^ 20) l 4 = (bcpA (2 ^ 20) l 3 >>> 43) + l 4
  hmul19 : (bcpA (2 ^ 20) l 5 >>> 40) * (19 : ℤ) = (19 : ℤ) * (bcpA (2 ^ 20) l 5 >>> 40)
  hy0 : y 0 = bcpA (2 ^ 20) l 0 % (2 : ℤ) ^ 43
  hy1 : y 1 = bcpA (2 ^ 20) l 1 % (2 : ℤ) ^ 43
  hy2 : y 2 = bcpA (2 ^ 20) l 2 % (2 : ℤ) ^ 43
  hy3 : y 3 = bcpA (2 ^ 20) l 3 % (2 : ℤ) ^ 43
  hy4 : y 4 = bcpA (2 ^ 20) l 4 % (2 : ℤ) ^ 43
  hy5 : y 5 = bcpA (2 ^ 20) l 5 % (2 : ℤ) ^ 40 + (2 : ℤ) ^ 20 + (bcpA (2 ^ 20) l 4 >>> 43)
  hb0 : 0 ≤ y 0 ∧ y 0 < 2 ^ 43
  hb1 : 0 ≤ y 1 ∧ y 1 < 2 ^ 43
  hb2 : 0 ≤ y 2 ∧ y 2 < 2 ^ 43
  hb3 : 0 ≤ y 3 ∧ y 3 < 2 ^ 43
  hb4 : 0 ≤ y 4 ∧ y 4 < 2 ^ 43
  fy0 : FitsLong (y 0)
  fy1 : FitsLong (y 1)
  fy2 : FitsLong (y 2)
  fy3 : FitsLong (y 3)
  fy4 : FitsLong (y 4)
  fy5 : FitsLong (y 5)
  hy5nn : 0 ≤ y 5
  fA : ∀ i, FitsLong (mnrA y i)
  fE : ∀ i, FitsLong (mnrE y i)
  fA0 : ∀ i, 0 ≤ mnrA y i
  hA0 : mnrA y 0 = y 0 + 19
  hA1 : mnrA y 1 = y 1 + (mnrA y 0 >>> 43)
  hA2 : mnrA y 2 = y 2 + (mnrA y 1 >>> 43)
  hA3 : mnrA y 3 = y 3 + (mnrA y 2 >>> 43)
  hA4 : mnrA y 4 = y 4 + (mnrA y 3 >>> 43)
  hA5 : mnrA y 5 = y 5 + (mnrA y 4 >>> 43)
  hqlt : mnrQ y = 0 ↔ mnrA y 5 < 2 ^ 40
  fif : FitsLong (if mnrQ y = 0 then (19 : ℤ) else 0)
  hE0 : mnrE y 0 = mnrA y 0 % (2 : ℤ) ^ 43 - (if mnrQ y = 0 then 19 else 0)
  hE1 : (mnrE y 0 >>> 43) + mnrA y 1 % (2 : ℤ) ^ 43 = mnrE y 1
  hE2 : (mnrE y 1 >>> 43) + mnrA y 2 % (2 : ℤ) ^ 43 = mnrE y 2
  hE3 : (mnrE y 2 >>> 43) + mnrA y 3 % (2 : ℤ) ^ 43 = mnrE y 3
  hE4 : (mnrE y 3 >>> 43) + mnrA y 4 % (2 : ℤ) ^ 43 = mnrE y 4
  h71 : (mnrE y 4 >>> 43) + mnrA y 5 % (2 : ℤ) ^ 40 = mnr y 5
  f72 : FitsLong ((mnrE y 4 >>> 43) + mnrA y 5 % (2 : ℤ) ^ 40)
  hm0 : mnr y 0 = mnrE y 0 % (2 : ℤ) ^ 43
  hm1 : mnr y 1 = mnrE y 1 % (2 : ℤ) ^ 43
  hm2 : mnr y 2 = mnrE y 2 % (2 : ℤ) ^ 43
  hm3 : mnr y 3 = mnrE y 3 % (2 : ℤ) ^ 43
  hm4 : mnr y 4 = mnrE y 4 % (2 : ℤ) ^ 43
  fm0 : FitsLong (mnr y 0)
  fm1 : FitsLong (mnr y 1)
  fm2 : FitsLong (mnr y 2)
  fm3 : FitsLong (mnr y 3)
  fm4 : FitsLong (mnr y 4)
  fm5 : FitsLong (mnr y 5)

/-- **The facts, from the header's domain.** Everything is either a macro
theorem of the two `Proof/` files, or the definition of a chain unfolded at
one limb. -/
theorem reduceFacts {l : Fin R43x6.limbCount → ℤ} (hpre : BcpPre (2 ^ 20) l) :
    ReduceFacts l (bcp (2 ^ 20) l) := by
  have fa := bcpA_fitsLong (b := 2 ^ 20) (x := l) (by norm_num) (by norm_num) hpre
  obtain ⟨fmul, f54, f55⟩ := bcp_aux_fitsLong (b := 2 ^ 20)
    (x := l) (by norm_num) (by norm_num) hpre
  obtain ⟨hbl, hb5⟩ := bcp_limbs (b := 2 ^ 20) (x := l) (by norm_num) (by norm_num) hpre
  have hb0 := hbl 0 (by decide)
  have hb1 := hbl 1 (by decide)
  have hb2 := hbl 2 (by decide)
  have hb3 := hbl 3 (by decide)
  have hb4 := hbl 4 (by decide)
  have hmnr := bcp_nearlyReduced hpre
  have f71 := mnr_limb5_fitsLong hmnr
  have h71 : (mnrE (bcp (2 ^ 20) l) 4 >>> 43) + mnrA (bcp (2 ^ 20) l) 5 % (2 : ℤ) ^ 40
      = mnr (bcp (2 ^ 20) l) 5 := by simp [mnr, R43x6.limbs6]; ring
  have hm0 : mnr (bcp (2 ^ 20) l) 0 = mnrE (bcp (2 ^ 20) l) 0 % (2 : ℤ) ^ 43 := by
    simp [mnr, R43x6.limbs6]
  have hm1 : mnr (bcp (2 ^ 20) l) 1 = mnrE (bcp (2 ^ 20) l) 1 % (2 : ℤ) ^ 43 := by
    simp [mnr, R43x6.limbs6]
  have hm2 : mnr (bcp (2 ^ 20) l) 2 = mnrE (bcp (2 ^ 20) l) 2 % (2 : ℤ) ^ 43 := by
    simp [mnr, R43x6.limbs6]
  have hm3 : mnr (bcp (2 ^ 20) l) 3 = mnrE (bcp (2 ^ 20) l) 3 % (2 : ℤ) ^ 43 := by
    simp [mnr, R43x6.limbs6]
  have hm4 : mnr (bcp (2 ^ 20) l) 4 = mnrE (bcp (2 ^ 20) l) 4 % (2 : ℤ) ^ 43 := by
    simp [mnr, R43x6.limbs6]
  exact
    { fa := fa
      fmul := fmul
      fmul' := by rw [mul_comm] at fmul; exact fmul
      f54 := f54
      f55 := f55
      ha5 := by simp [bcpA, R43x6.limbs6]; ring
      ha0 := by simp [bcpA, R43x6.limbs6]; ring
      ha1 := by simp [bcpA, R43x6.limbs6]; ring
      ha2 := by simp [bcpA, R43x6.limbs6]; ring
      ha3 := by simp [bcpA, R43x6.limbs6]; ring
      ha4 := by simp [bcpA, R43x6.limbs6]; ring
      hmul19 := mul_comm _ _
      hy0 := by simp [bcp, R43x6.limbs6]
      hy1 := by simp [bcp, R43x6.limbs6]
      hy2 := by simp [bcp, R43x6.limbs6]
      hy3 := by simp [bcp, R43x6.limbs6]
      hy4 := by simp [bcp, R43x6.limbs6]
      hy5 := by simp [bcp, R43x6.limbs6]; ring
      hb0 := hb0
      hb1 := hb1
      hb2 := hb2
      hb3 := hb3
      hb4 := hb4
      fy0 := by simp only [R43x6.FitsLong]; omega
      fy1 := by simp only [R43x6.FitsLong]; omega
      fy2 := by simp only [R43x6.FitsLong]; omega
      fy3 := by simp only [R43x6.FitsLong]; omega
      fy4 := by simp only [R43x6.FitsLong]; omega
      fy5 := by simp only [R43x6.FitsLong]; omega
      hy5nn := by omega
      fA := mnrA_fitsLong hmnr
      fE := mnrE_fitsLong hmnr
      fA0 := mnrA_nonneg hmnr
      hA0 := by simp [mnrA, R43x6.limbs6]
      hA1 := by simp [mnrA, R43x6.limbs6]
      hA2 := by simp [mnrA, R43x6.limbs6]
      hA3 := by simp [mnrA, R43x6.limbs6]
      hA4 := by simp [mnrA, R43x6.limbs6]
      hA5 := by simp [mnrA, R43x6.limbs6]
      hqlt := mnrQ_eq_zero_iff (mnrA_nonneg hmnr 5)
      fif := by split <;> simp [R43x6.FitsLong]
      hE0 := by simp [mnrE, R43x6.limbs6]
      hE1 := by simp [mnrE, R43x6.limbs6]; ring
      hE2 := by simp [mnrE, R43x6.limbs6]; ring
      hE3 := by simp [mnrE, R43x6.limbs6]; ring
      hE4 := by simp [mnrE, R43x6.limbs6]; ring
      h71 := h71
      f72 := by rw [h71]; exact f71
      hm0 := hm0
      hm1 := hm1
      hm2 := hm2
      hm3 := hm3
      hm4 := hm4
      fm0 := by rw [hm0]; exact fitsLong_emod _ (by norm_num)
      fm1 := by rw [hm1]; exact fitsLong_emod _ (by norm_num)
      fm2 := by rw [hm2]; exact fitsLong_emod _ (by norm_num)
      fm3 := by rw [hm3]; exact fitsLong_emod _ (by norm_num)
      fm4 := by rw [hm4]; exact fitsLong_emod _ (by norm_num)
      fm5 := by rw [← h71, add_comm]; simpa using f71 }

end Firedancer.Avx512
