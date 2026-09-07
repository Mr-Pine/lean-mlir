/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Proof.Long
import SSA.Projects.Firedancer.Avx512.Proof.Util.fd_long_if
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_biased_carry_propagate_limbs
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_mod_nearly_reduced_limbs
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.MLIR.DenoteStep
import Mathlib.Tactic.Linarith

/-!
# `fd_r43x6_is_nonzero` decides whether its input is zero in `GF(2^255-19)`

The obligations of `Spec/fd_r43x6_is_nonzero.lean`, discharged. The arithmetic
is in the two macro proofs,
`Proof/fd_r43x6_biased_carry_propagate_limbs.lean` and
`Proof/fd_r43x6_mod_nearly_reduced_limbs.lean`; this file composes them, along
the header's own two lines --

    fd_r43x6_biased_carry_propagate_limbs( l, l, 1L<<20 );  /* nearly reduced */
    fd_r43x6_mod_nearly_reduced_limbs( l, l );              /* reduced */

-- with `bcp_nearlyReduced` supplying the `MnrPre` the second macro needs.

`isNonzeroDecides` is the one step that is more than composition: a limb-wise
comparison against zero decides the element only because the representation
reaching it is the unique reduced one, so it uses `reduceIsCanonical` (through
`R43x6.decodeLimbs_eq_zero_iff`) as well as `reducePreservesValue`.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The reduction's input is nearly reduced by the time the second macro sees
it -- the one fact the composition turns on. -/
private theorem nearlyReduced_bcp {x : Fin R43x6.limbCount → ℤ} (h : BcpPre (2 ^ 20) x) :
    MnrPre (bcp (2 ^ 20) x) := bcp_nearlyReduced h

/-! ## `nsw` and `nuw` -/

/-- **No `nsw` operand overflows**, in either chain. -/
theorem chainFitsLong (x : Fin R43x6.limbCount → ℤ) : ChainFitsLong x := fun h =>
  ⟨bcp_chain_fitsLong (by norm_num) (by norm_num) h,
    mnr_chain_fitsLong (nearlyReduced_bcp h)⟩

/-- **No `nuw` operand wraps and no `lshr` sees a negative value.** -/
theorem mnrChainNonneg (x : Fin R43x6.limbCount → ℤ) : MnrChainNonneg x := fun h =>
  mnrA_nonneg (nearlyReduced_bcp h)

/-! ## The arithmetic -/

/-- **The reduction preserves the element.** -/
theorem reducePreservesValue (x : Fin R43x6.limbCount → ℤ) : ReducePreservesValue x := fun h => by
  rw [reduce, mnr_congr (nearlyReduced_bcp h), bcp_congr]

/-- **The reduction returns the canonical representative.** -/
theorem reduceIsCanonical (x : Fin R43x6.limbCount → ℤ) : ReduceIsCanonical x := fun h =>
  mnr_reduced (nearlyReduced_bcp h)

/-- The reduction as an equation rather than a class: it is `%` on the nose. -/
theorem decodeLimbs_reduce {x : Fin R43x6.limbCount → ℤ} (h : BcpPre (2 ^ 20) x) :
    R43x6.decodeLimbs (reduce x)
      = R43x6.decodeLimbs (bcp (2 ^ 20) x) % (p : ℤ) :=
  decodeLimbs_mnr_eq_emod (nearlyReduced_bcp h)

/-! ## The decision -/

/-- `!!(l0|l1|l2|l3|l4|l5)` as the model states it. -/
private theorem isNonzero_eq_zero_iff (x : Fin R43x6.limbCount → ℤ) :
    isNonzero x = 0 ↔ (reduce x 0 = 0 ∧ reduce x 1 = 0 ∧ reduce x 2 = 0
      ∧ reduce x 3 = 0 ∧ reduce x 4 = 0 ∧ reduce x 5 = 0) := by
  simp only [isNonzero]
  split <;> rename_i hc <;> simp only [hc, iff_false] <;> decide

/-- **The decision is the right one.** -/
theorem isNonzeroDecides (x : Fin R43x6.limbCount → ℤ) : IsNonzeroDecides x := fun h => by
  obtain ⟨h04, h5, hnn, hlt⟩ := reduceIsCanonical x h
  have hval := reducePreservesValue x h
  rw [isNonzero_eq_zero_iff, ← R43x6.decodeLimbs_eq_zero_iff h04, ← hval]
  refine ⟨fun hz => by rw [hz]; simp, fun hz => ?_⟩
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz
  have := p_pos
  have hk0 : k = 0 := by nlinarith
  rw [hk, hk0, mul_zero]

/-! ## The specification

The obligations together, as a caller wants them: on a signed input the answer
is `0` exactly when the element is zero, and the reduced limbs it was read off
are the canonical representative of the input's element. Both statements are
`Spec/fd_r43x6_is_nonzero.lean`'s; nothing is restated here. -/

/-- **Specification of `fd_r43x6_is_nonzero`**, over extracted limbs. -/
theorem spec_fd_r43x6_is_nonzero (x : Fin R43x6.limbCount → ℤ) :
    IsNonzeroDecides x ∧ ReduceIsCanonical x ∧ ReducePreservesValue x :=
  ⟨isNonzeroDecides x, reduceIsCanonical x, reducePreservesValue x⟩

/-- **Specification of `fd_r43x6_is_nonzero`**, over the vector the C takes.
`R43x6.decodeLimbs_extractLimbs` is what makes it the same statement. -/
theorem isNonzeroDecidesVec (x : Vector (BitVec 64) 8) : IsNonzeroDecidesVec x := by
  intro h
  have hpre := bcpPre_of_s62 (b := 2 ^ 20) (by norm_num) (by norm_num) h
  rw [← R43x6.decodeLimbs_extractLimbs]
  exact isNonzeroDecides _ hpre

/-! ## The lifted region

The model is what the region computes. The derivation runs at the level of
`val` (`Proof/Long.lean`): every one of the eighty instructions takes `val`s to
a `val`, so each step is one rewrite with the `Proof/Long.lean` lemma for its
opcode and the `R43x6.FitsLong` facts the two macro proofs supply.

Each step `let`s its value under the macro's own name for it -- `_y k` is
`y<k>`, `_c` is `c<k>`, primed once per pass over the limbs, and the limbs
between the two macros are `l<k>'` -- then names the stepped variable and
`subst`s the two together. The valuation spine therefore holds those names
rather than the expressions, which is what keeps the terms shared; each step
unfolds only what it touches.

`denote_step_all` runs a block at a time -- the constants, the extracts, and
then one per pass over the limbs -- and a block is finished before the next
opens: every `v<i>` in it is `subst`ed and every `hv<i>` `denote_clear`ed, so
no `subst` ever has to rewrite an instruction belonging to another block.

The middle -- the two carry chains, `%20`-`%57` -- is generated by
`gen_is_nonzero_proof.py`, as `fd_r43x6_mul_fast`'s derivation is by
`gen_mul_proof.py`.

`hpre` is not bookkeeping. Every add in both chains is `nsw`, so an out-of-range
operand denotes to poison; the region computes the model only on the domain the
macro documents. -/

local macro "long_op " h:term : tactic =>
  `(tactic| (simp only [$h:term, Expr.denoteOp1, Expr.denoteOpPure]
             simp_peephole
             simp +zetaDelta only [HVector.head, LLVM.const?, val_eq]))

set_option maxHeartbeats 4000000 in
/-- **Denotation of `fd_r43x6_is_nonzero`**: the lifted region computes the
model, instruction by instruction. The hypothesis is what makes it denote to a
value at all -- without it the first `nsw` add is poison. -/
theorem denote_fd_r43x6_is_nonzero (x : Vector (BitVec 64) 8)
    (hpre : BcpPre (2^20) (R43x6.extractLimbs x)) :
    fd_r43x6_is_nonzero.denote (Ctxt.Valuation.singleton (x.map PoisonOr.value))
      = ([PoisonOr.value (isNonzero (R43x6.extractLimbs x))]ₕ : HVector TyDenote.toType
          [SLLVM.Ty.arith (.bitvec (.concrete 32))]) := by
  -- `l` and `y` are opaque: the limbs `fd_r43x6_extract_limbs` returns, and
  -- what the carry propagate makes of them. Naming them keeps the derivation's
  -- terms small, and keeps `simp` from unfolding either back to its definition.
  obtain ⟨l, hl⟩ : ∃ l, l = R43x6.extractLimbs x := ⟨_, rfl⟩
  rw [← hl] at hpre ⊢
  have fl : ∀ i, R43x6.FitsLong (l i) := by
    rw [hl]; exact fun i => fitsLong_toInt _
  have fa := bcpA_fitsLong (b := 2^20) (x := l) (by norm_num) (by norm_num) hpre
  obtain ⟨fmul, f54, f55⟩ := bcp_aux_fitsLong (b := 2^20)
    (x := l) (by norm_num) (by norm_num) hpre
  obtain ⟨hbl, hb5⟩ := bcp_limbs (b := 2^20) (x := l)
    (by norm_num) (by norm_num) hpre
  have hmnr : MnrPre (bcp (2^20) l) := bcp_nearlyReduced hpre
  obtain ⟨y, hyy⟩ : ∃ y, y = bcp (2^20) l := ⟨_, rfl⟩
  rw [← hyy] at hmnr hbl hb5
  have fA := mnrA_fitsLong hmnr
  have fE := mnrE_fitsLong hmnr
  have fA0 := mnrA_nonneg hmnr
  have f71 := mnr_limb5_fitsLong hmnr
  have fc6 : R43x6.FitsLong (-((2:ℤ)^20)) := by simp [R43x6.FitsLong]
  have fc9 : R43x6.FitsLong (19 : ℤ) := by simp [R43x6.FitsLong]
  have fc12 : R43x6.FitsLong ((2:ℤ)^20) := by simp [R43x6.FitsLong]
  -- the limb equations of the model, as recurrences
  have ha5 : bcpA (2^20) l 5 = l 5 + (-((2:ℤ)^20)) := by simp [bcpA, R43x6.limbs6]; ring
  have fmul' : R43x6.FitsLong ((bcpA (2^20) l 5 >>> 40) * 19) := by
    rw [mul_comm] at fmul; exact fmul
  have ha0 : bcpA (2^20) l 0 = (19:ℤ) * (bcpA (2^20) l 5 >>> 40) + l 0 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha1 : bcpA (2^20) l 1 = (bcpA (2^20) l 0 >>> 43) + l 1 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha2 : bcpA (2^20) l 2 = (bcpA (2^20) l 1 >>> 43) + l 2 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha3 : bcpA (2^20) l 3 = (bcpA (2^20) l 2 >>> 43) + l 3 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha4 : bcpA (2^20) l 4 = (bcpA (2^20) l 3 >>> 43) + l 4 := by
    simp [bcpA, R43x6.limbs6]; ring
  have hy0 : y 0 = bcpA (2^20) l 0 % (2:ℤ)^43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy1 : y 1 = bcpA (2^20) l 1 % (2:ℤ)^43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy2 : y 2 = bcpA (2^20) l 2 % (2:ℤ)^43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy3 : y 3 = bcpA (2^20) l 3 % (2:ℤ)^43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy4 : y 4 = bcpA (2^20) l 4 % (2:ℤ)^43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy5 : y 5 = bcpA (2^20) l 5 % (2:ℤ)^40 + (2:ℤ)^20 + (bcpA (2^20) l 4 >>> 43) := by
    rw [hyy]; simp [bcp, R43x6.limbs6]; ring
  have hA0 : mnrA y 0 = y 0 + 19 := by simp [mnrA, R43x6.limbs6]
  have hA1 : mnrA y 1 = y 1 + (mnrA y 0 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA2 : mnrA y 2 = y 2 + (mnrA y 1 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA3 : mnrA y 3 = y 3 + (mnrA y 2 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA4 : mnrA y 4 = y 4 + (mnrA y 3 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA5 : mnrA y 5 = y 5 + (mnrA y 4 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hE0 : mnrE y 0 = mnrA y 0 % (2:ℤ)^43 - (if mnrQ y = 0 then 19 else 0) := by
    simp [mnrE, R43x6.limbs6]
  have hE1 : (mnrE y 0 >>> 43) + mnrA y 1 % (2:ℤ)^43 = mnrE y 1 := by
    simp [mnrE, R43x6.limbs6]; ring
  have hE2 : (mnrE y 1 >>> 43) + mnrA y 2 % (2:ℤ)^43 = mnrE y 2 := by
    simp [mnrE, R43x6.limbs6]; ring
  have hE3 : (mnrE y 2 >>> 43) + mnrA y 3 % (2:ℤ)^43 = mnrE y 3 := by
    simp [mnrE, R43x6.limbs6]; ring
  have hE4 : (mnrE y 3 >>> 43) + mnrA y 4 % (2:ℤ)^43 = mnrE y 4 := by
    simp [mnrE, R43x6.limbs6]; ring
  have h71 : (mnrE y 4 >>> 43) + mnrA y 5 % (2:ℤ)^40 = mnr y 5 := by
    simp [mnr, R43x6.limbs6]; ring
  have hb0 := hbl 0 (by decide)
  have hb1 := hbl 1 (by decide)
  have hb2 := hbl 2 (by decide)
  have hb3 := hbl 3 (by decide)
  have hb4 := hbl 4 (by decide)
  have fy0 : R43x6.FitsLong (y 0) := by simp only [R43x6.FitsLong]; omega
  have fy1 : R43x6.FitsLong (y 1) := by simp only [R43x6.FitsLong]; omega
  have fy2 : R43x6.FitsLong (y 2) := by simp only [R43x6.FitsLong]; omega
  have fy3 : R43x6.FitsLong (y 3) := by simp only [R43x6.FitsLong]; omega
  have fy4 : R43x6.FitsLong (y 4) := by simp only [R43x6.FitsLong]; omega
  have fy5 : R43x6.FitsLong (y 5) := by simp only [R43x6.FitsLong]; omega
  simp only [fd_r43x6_is_nonzero]
  denote_step_all v 13
  have v0Value : v0 = val 0 := by
    long_op hv0
  subst v0Value
  have v1Value : v1 = val 1 := by
    long_op hv1
  subst v1Value
  have v2Value : v2 = val 2 := by
    long_op hv2
  subst v2Value
  have v3Value : v3 = val 3 := by
    long_op hv3
  subst v3Value
  have v4Value : v4 = val 4 := by
    long_op hv4
  subst v4Value
  have v5Value : v5 = val 5 := by
    long_op hv5
  subst v5Value
  have v6Value : v6 = val (-(2^20)) := by
    long_op hv6
    norm_num
  subst v6Value
  have v7Value : v7 = val ((40:ℕ) : ℤ) := by
    long_op hv7
    norm_num
  subst v7Value
  have v8Value : v8 = val (2^40 - 1) := by
    long_op hv8
    norm_num
  subst v8Value
  have v9Value : v9 = val 19 := by
    long_op hv9
  subst v9Value
  have v10Value : v10 = val ((43:ℕ) : ℤ) := by
    long_op hv10
    norm_num
  subst v10Value
  have v11Value : v11 = val (2^43 - 1) := by
    long_op hv11
    norm_num
  subst v11Value
  have v12Value : v12 = val (2^20) := by
    long_op hv12
    norm_num
  subst v12Value
  have v13Value : v13 = val (2^40) := by
    long_op hv13
    norm_num
  subst v13Value
  denote_clear v 0 13
  denote_step_all v 19
  -- `fd_r43x6_extract_limbs( x, l )`
  let l0 := val (l 0)
  have v14Value : v14 = l0 := by
    long_op hv14
    simp [hl, val, LLVM.Ty.extractelement, Ctxt.Valuation.singleton,
      R43x6.extractLimbs, LimbRepresentations.toInts]
  subst v14Value
  let l1 := val (l 1)
  have v15Value : v15 = l1 := by
    long_op hv15
    simp [hl, val, LLVM.Ty.extractelement, Ctxt.Valuation.singleton,
      R43x6.extractLimbs, LimbRepresentations.toInts]
  subst v15Value
  let l2 := val (l 2)
  have v16Value : v16 = l2 := by
    long_op hv16
    simp [hl, val, LLVM.Ty.extractelement, Ctxt.Valuation.singleton,
      R43x6.extractLimbs, LimbRepresentations.toInts]
  subst v16Value
  let l3 := val (l 3)
  have v17Value : v17 = l3 := by
    long_op hv17
    simp [hl, val, LLVM.Ty.extractelement, Ctxt.Valuation.singleton,
      R43x6.extractLimbs, LimbRepresentations.toInts]
  subst v17Value
  let l4 := val (l 4)
  have v18Value : v18 = l4 := by
    long_op hv18
    simp [hl, val, LLVM.Ty.extractelement, Ctxt.Valuation.singleton,
      R43x6.extractLimbs, LimbRepresentations.toInts]
  subst v18Value
  let l5 := val (l 5)
  have v19Value : v19 = l5 := by
    long_op hv19
    simp [hl, val, LLVM.Ty.extractelement, Ctxt.Valuation.singleton,
      R43x6.extractLimbs, LimbRepresentations.toInts]
  subst v19Value
  denote_clear v 14 19
  denote_step_all v 38
  -- `_y5 -= _b`, and the carry chain from there
  let y5 := val (bcpA (2^20) l 5)
  have v20Value : v20 = y5 := by
    long_op hv20
    rw [add_ofInt (fl 5) fc6 (ha5 ▸ fa 5) (by simp), ha5]
  subst v20Value
  let c5 := val (bcpA (2^20) l 5 >>> 40)
  have v21Value : v21 = c5 := by
    long_op hv21; rw [ashr_ofInt (fa 5) (by norm_num)]
  subst v21Value
  let y5m := val (bcpA (2^20) l 5 % 2^40)
  have v22Value : v22 = y5m := by
    long_op hv22; rw [and_mask_ofInt (k := 40) (by norm_num)]
  subst v22Value
  let c5x19 := val ((19:ℤ) * (bcpA (2^20) l 5 >>> 40))
  have v23Value : v23 = c5x19 := by
    long_op hv23
    rw [mul_ofInt rfl (fitsLong_shiftRight (fa 5) 40) fc9 fmul', mul_comm]
  subst v23Value
  let y0 := val (bcpA (2^20) l 0)
  have v24Value : v24 = y0 := by
    long_op hv24
    rw [add_ofInt fmul (fl 0) (ha0 ▸ fa 0) (by simp), ha0]
  subst v24Value
  let c0 := val (bcpA (2^20) l 0 >>> 43)
  have v25Value : v25 = c0 := by
    long_op hv25; rw [ashr_ofInt (fa 0) (by norm_num)]
  subst v25Value
  let l0' := val (y 0)
  have v26Value : v26 = l0' := by
    long_op hv26
    rw [and_mask_ofInt (k := 43) (by norm_num), ← hy0]
  subst v26Value
  let y1 := val (bcpA (2^20) l 1)
  have v27Value : v27 = y1 := by
    long_op hv27
    rw [add_ofInt (fitsLong_shiftRight (fa 0) 43) (fl 1) (ha1 ▸ fa 1) (by simp), ha1]
  subst v27Value
  let c1 := val (bcpA (2^20) l 1 >>> 43)
  have v28Value : v28 = c1 := by
    long_op hv28; rw [ashr_ofInt (fa 1) (by norm_num)]
  subst v28Value
  let l1' := val (y 1)
  have v29Value : v29 = l1' := by
    long_op hv29
    rw [and_mask_ofInt (k := 43) (by norm_num), ← hy1]
  subst v29Value
  let y2 := val (bcpA (2^20) l 2)
  have v30Value : v30 = y2 := by
    long_op hv30
    rw [add_ofInt (fitsLong_shiftRight (fa 1) 43) (fl 2) (ha2 ▸ fa 2) (by simp), ha2]
  subst v30Value
  let c2 := val (bcpA (2^20) l 2 >>> 43)
  have v31Value : v31 = c2 := by
    long_op hv31; rw [ashr_ofInt (fa 2) (by norm_num)]
  subst v31Value
  let l2' := val (y 2)
  have v32Value : v32 = l2' := by
    long_op hv32
    rw [and_mask_ofInt (k := 43) (by norm_num), ← hy2]
  subst v32Value
  let y3 := val (bcpA (2^20) l 3)
  have v33Value : v33 = y3 := by
    long_op hv33
    rw [add_ofInt (fitsLong_shiftRight (fa 2) 43) (fl 3) (ha3 ▸ fa 3) (by simp), ha3]
  subst v33Value
  let c3 := val (bcpA (2^20) l 3 >>> 43)
  have v34Value : v34 = c3 := by
    long_op hv34; rw [ashr_ofInt (fa 3) (by norm_num)]
  subst v34Value
  let l3' := val (y 3)
  have v35Value : v35 = l3' := by
    long_op hv35
    rw [and_mask_ofInt (k := 43) (by norm_num), ← hy3]
  subst v35Value
  let y4 := val (bcpA (2^20) l 4)
  have v36Value : v36 = y4 := by
    long_op hv36
    rw [add_ofInt (fitsLong_shiftRight (fa 3) 43) (fl 4) (ha4 ▸ fa 4) (by simp), ha4]
  subst v36Value
  let c4 := val (bcpA (2^20) l 4 >>> 43)
  have v37Value : v37 = c4 := by
    long_op hv37; rw [ashr_ofInt (fa 4) (by norm_num)]
  subst v37Value
  let l4' := val (y 4)
  have v38Value : v38 = l4' := by
    long_op hv38
    rw [and_mask_ofInt (k := 43) (by norm_num), ← hy4]
  subst v38Value
  denote_clear v 20 38
  denote_step_all v 57
  -- `_y0 += 19L`, and the carry chain from there
  let y0' := val (mnrA y 0)
  have v39Value : v39 = y0' := by
    long_op hv39
    rw [add_ofInt fy0 fc9 (hA0 ▸ fA 0) (fun _ => ⟨hb0.1, by norm_num⟩), hA0]
  subst v39Value
  let c0' := val (mnrA y 0 >>> 43)
  have v40Value : v40 = c0' := by
    long_op hv40
    rw [lshr_ofInt (fA 0) (fA0 0) (by norm_num) (by norm_num)]
  subst v40Value
  let y0m' := val (mnrA y 0 % 2^43)
  have v41Value : v41 = y0m' := by
    long_op hv41; rw [and_mask_ofInt (k := 43) (by norm_num)]
  subst v41Value
  let y1' := val (mnrA y 1)
  have v42Value : v42 = y1' := by
    long_op hv42
    rw [add_ofInt fy1 (fitsLong_shiftRight (fA 0) 43) (hA1 ▸ fA 1) (fun _ => ⟨hb1.1, shiftRight_nonneg (fA0 0) 43⟩), hA1]
  subst v42Value
  let c1' := val (mnrA y 1 >>> 43)
  have v43Value : v43 = c1' := by
    long_op hv43
    rw [lshr_ofInt (fA 1) (fA0 1) (by norm_num) (by norm_num)]
  subst v43Value
  let y1m' := val (mnrA y 1 % 2^43)
  have v44Value : v44 = y1m' := by
    long_op hv44; rw [and_mask_ofInt (k := 43) (by norm_num)]
  subst v44Value
  let y2' := val (mnrA y 2)
  have v45Value : v45 = y2' := by
    long_op hv45
    rw [add_ofInt fy2 (fitsLong_shiftRight (fA 1) 43) (hA2 ▸ fA 2) (fun _ => ⟨hb2.1, shiftRight_nonneg (fA0 1) 43⟩), hA2]
  subst v45Value
  let c2' := val (mnrA y 2 >>> 43)
  have v46Value : v46 = c2' := by
    long_op hv46
    rw [lshr_ofInt (fA 2) (fA0 2) (by norm_num) (by norm_num)]
  subst v46Value
  let y2m' := val (mnrA y 2 % 2^43)
  have v47Value : v47 = y2m' := by
    long_op hv47; rw [and_mask_ofInt (k := 43) (by norm_num)]
  subst v47Value
  let y3' := val (mnrA y 3)
  have v48Value : v48 = y3' := by
    long_op hv48
    rw [add_ofInt fy3 (fitsLong_shiftRight (fA 2) 43) (hA3 ▸ fA 3) (fun _ => ⟨hb3.1, shiftRight_nonneg (fA0 2) 43⟩), hA3]
  subst v48Value
  let c3' := val (mnrA y 3 >>> 43)
  have v49Value : v49 = c3' := by
    long_op hv49
    rw [lshr_ofInt (fA 3) (fA0 3) (by norm_num) (by norm_num)]
  subst v49Value
  let y3m' := val (mnrA y 3 % 2^43)
  have v50Value : v50 = y3m' := by
    long_op hv50; rw [and_mask_ofInt (k := 43) (by norm_num)]
  subst v50Value
  let y4' := val (mnrA y 4)
  have v51Value : v51 = y4' := by
    long_op hv51
    rw [add_ofInt fy4 (fitsLong_shiftRight (fA 3) 43) (hA4 ▸ fA 4) (fun _ => ⟨hb4.1, shiftRight_nonneg (fA0 3) 43⟩), hA4]
  subst v51Value
  let c4' := val (mnrA y 4 >>> 43)
  have v52Value : v52 = c4' := by
    long_op hv52
    rw [lshr_ofInt (fA 4) (fA0 4) (by norm_num) (by norm_num)]
  subst v52Value
  let y4m' := val (mnrA y 4 % 2^43)
  have v53Value : v53 = y4m' := by
    long_op hv53; rw [and_mask_ofInt (k := 43) (by norm_num)]
  subst v53Value
  -- the carry propagate's `_y5 += _b` and `_y5 += _c`, scheduled here
  let y5b := val (bcpA (2^20) l 5 % 2^40 + 2^20)
  have v54Value : v54 = y5b := by
    long_op hv54
    rw [add_ofInt (fitsLong_emod _ (by norm_num)) fc12 f54
      (fun _ => ⟨Int.emod_nonneg _ (by norm_num), by norm_num⟩)]
  subst v54Value
  let l5' := val (y 5)
  have v55Value : v55 = l5' := by
    long_op hv55
    rw [add_ofInt f54 (fitsLong_shiftRight (fa 4) 43) (hy5 ▸ f55) (by simp), ← hy5]
  subst v55Value
  let y5' := val (mnrA y 5)
  have v56Value : v56 = y5' := by
    long_op hv56
    rw [add_ofInt fy5 (fitsLong_shiftRight (fA 4) 43) (hA5 ▸ fA 5)
      (fun _ => ⟨by omega, shiftRight_nonneg (fA0 4) 43⟩), hA5]
  subst v56Value
  let y5m' := val (mnrA y 5 % 2^40)
  have v57Value : v57 = y5m' := by
    long_op hv57; rw [and_mask_ofInt (k := 40) (by norm_num)]
  subst v57Value
  denote_clear v 39 57
  denote_step_all v 71
  -- `_c = _y5>>40` decided, and `fd_long_if( !_c, 19L, 0L )`
  have hA5nn : (0:ℤ) ≤ mnrA y 5 := fA0 5
  have hqlt : mnrQ y = 0 ↔ mnrA y 5 < 2^40 := by
    simp only [mnrQ, R43x6.shiftRight_eq]; omega
  let notc := PoisonOr.value (BitVec.ofBool (decide (mnrA y 5 < 2^40)))
  have v58Value : v58 = notc := by
    long_op hv58
    rw [icmp_ult_ofInt (fA 5) (by simp [R43x6.FitsLong]) hA5nn (by positivity)]
  subst v58Value
  let notc32 := PoisonOr.value ((BitVec.ofBool (decide (mnrA y 5 < 2^40))).setWidth 32)
  have v59Value : v59 = notc32 := by
    long_op hv59; rw [zext_ofBool]
  subst v59Value
  -- the callee is not stepped through again: `denote_fd_long_if` is what it
  -- computes, and `Spec/fd_long_if.lean` says which arm each condition takes
  let sub19 := val (if mnrQ y = 0 then 19 else 0)
  have v60Value : v60 = sub19 := by
    simp only [hv60, Expr.denoteOp1, Expr.denoteOpPure, SLLVM.denoteOp_call]
    show HVector.head (fd_long_if.denote (Ctxt.Valuation.singleton
      (PoisonOr.value ((BitVec.ofBool (decide (mnrA y 5 < 2^40))).setWidth 32)))) = _
    rw [denote_fd_long_if]
    simp only [HVector.head, fdLongIf, sub19, val]
    congr
    simp [hqlt, BitVec.ofBool, Bool.cond_decide, apply_ite]
  subst v60Value
  -- `_y0 -= fd_long_if(…)`, and the borrow chain from there
  have fif : R43x6.FitsLong (if mnrQ y = 0 then (19:ℤ) else 0) := by
    split <;> simp [R43x6.FitsLong]
  let y0'' := val (mnrE y 0)
  have v61Value : v61 = y0'' := by
    long_op hv61
    rw [sub_ofInt rfl (fitsLong_emod _ (by norm_num)) fif (hE0 ▸ fE 0), ← hE0]
  subst v61Value
  let c0'' := val (mnrE y 0 >>> 43)
  have v62Value : v62 = c0'' := by
    long_op hv62; rw [ashr_ofInt (fE 0) (by norm_num)]
  subst v62Value
  let y1'' := val (mnrE y 1)
  have v63Value : v63 = y1'' := by
    long_op hv63
    rw [add_ofInt (fitsLong_shiftRight (fE 0) 43) (fitsLong_emod _ (by norm_num))
      (hE1 ▸ fE 1) (by simp), hE1]
  subst v63Value
  let c1'' := val (mnrE y 1 >>> 43)
  have v64Value : v64 = c1'' := by
    long_op hv64; rw [ashr_ofInt (fE 1) (by norm_num)]
  subst v64Value
  let y2'' := val (mnrE y 2)
  have v65Value : v65 = y2'' := by
    long_op hv65
    rw [add_ofInt (fitsLong_shiftRight (fE 1) 43) (fitsLong_emod _ (by norm_num))
      (hE2 ▸ fE 2) (by simp), hE2]
  subst v65Value
  let c2'' := val (mnrE y 2 >>> 43)
  have v66Value : v66 = c2'' := by
    long_op hv66; rw [ashr_ofInt (fE 2) (by norm_num)]
  subst v66Value
  let y3'' := val (mnrE y 3)
  have v67Value : v67 = y3'' := by
    long_op hv67
    rw [add_ofInt (fitsLong_shiftRight (fE 2) 43) (fitsLong_emod _ (by norm_num))
      (hE3 ▸ fE 3) (by simp), hE3]
  subst v67Value
  let c3'' := val (mnrE y 3 >>> 43)
  have v68Value : v68 = c3'' := by
    long_op hv68; rw [ashr_ofInt (fE 3) (by norm_num)]
  subst v68Value
  let y4'' := val (mnrE y 4)
  have v69Value : v69 = y4'' := by
    long_op hv69
    rw [add_ofInt (fitsLong_shiftRight (fE 3) 43) (fitsLong_emod _ (by norm_num))
      (hE4 ▸ fE 4) (by simp), hE4]
  subst v69Value
  let c4'' := val (mnrE y 4 >>> 43)
  have v70Value : v70 = c4'' := by
    long_op hv70; rw [ashr_ofInt (fE 4) (by norm_num)]
  subst v70Value
  let l5'' := val (mnr y 5)
  have v71Value : v71 = l5'' := by
    long_op hv71
    rw [add_ofInt (fitsLong_shiftRight (fE 4) 43) (fitsLong_emod _ (by norm_num))
      (h71 ▸ f71) (by simp), h71]
  subst v71Value
  denote_clear v 58 71
  denote_step_all v 79
  -- `!!(l0|l1|l2|l3|l4|l5)`, with the mask taken across the disjunction
  have hm0 : mnr y 0 = mnrE y 0 % (2:ℤ)^43 := by simp [mnr, R43x6.limbs6]
  have hm1 : mnr y 1 = mnrE y 1 % (2:ℤ)^43 := by simp [mnr, R43x6.limbs6]
  have hm2 : mnr y 2 = mnrE y 2 % (2:ℤ)^43 := by simp [mnr, R43x6.limbs6]
  have hm3 : mnr y 3 = mnrE y 3 % (2:ℤ)^43 := by simp [mnr, R43x6.limbs6]
  have hm4 : mnr y 4 = mnrE y 4 % (2:ℤ)^43 := by simp [mnr, R43x6.limbs6]
  let or1 := PoisonOr.value (BitVec.ofInt 64 (mnrE y 1) ||| BitVec.ofInt 64 (mnrE y 0))
  have v72Value : v72 = or1 := by
    long_op hv72; rw [or_ofInt]
  subst v72Value
  let or2 := PoisonOr.value ((BitVec.ofInt 64 (mnrE y 1) ||| BitVec.ofInt 64 (mnrE y 0))
    ||| BitVec.ofInt 64 (mnrE y 2))
  have v73Value : v73 = or2 := by
    long_op hv73; rw [or_val]
  subst v73Value
  let or3 := PoisonOr.value (((BitVec.ofInt 64 (mnrE y 1) ||| BitVec.ofInt 64 (mnrE y 0))
    ||| BitVec.ofInt 64 (mnrE y 2)) ||| BitVec.ofInt 64 (mnrE y 3))
  have v74Value : v74 = or3 := by
    long_op hv74; rw [or_val]
  subst v74Value
  let or4 := PoisonOr.value ((((BitVec.ofInt 64 (mnrE y 1) ||| BitVec.ofInt 64 (mnrE y 0))
    ||| BitVec.ofInt 64 (mnrE y 2)) ||| BitVec.ofInt 64 (mnrE y 3))
    ||| BitVec.ofInt 64 (mnrE y 4))
  have v75Value : v75 = or4 := by
    long_op hv75; rw [or_val]
  subst v75Value
  let orm := PoisonOr.value ((((BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0))
    ||| BitVec.ofInt 64 (mnr y 2)) ||| BitVec.ofInt 64 (mnr y 3))
    ||| BitVec.ofInt 64 (mnr y 4))
  have v76Value : v76 = orm := by
    long_op hv76
    simp only [val, LLVM.and, PoisonOr.value_bind, LLVM.and?,
      BitVec.and_or_distrib_right, and_mask_bv _ (show 43 < 64 by norm_num),
      hm0, hm1, hm2, hm3, hm4]
  subst v76Value
  let orAll := PoisonOr.value (((((BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0))
    ||| BitVec.ofInt 64 (mnr y 2)) ||| BitVec.ofInt 64 (mnr y 3))
    ||| BitVec.ofInt 64 (mnr y 4)) ||| BitVec.ofInt 64 (mnr y 5))
  have v77Value : v77 = orAll := by
    long_op hv77; rw [or_val]
  subst v77Value
  let nz := PoisonOr.value (BitVec.ofBool
    ((((((BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0))
      ||| BitVec.ofInt 64 (mnr y 2)) ||| BitVec.ofInt 64 (mnr y 3))
      ||| BitVec.ofInt 64 (mnr y 4)) ||| BitVec.ofInt 64 (mnr y 5)) != BitVec.ofInt 64 0))
  have v78Value : v78 = nz := by
    long_op hv78; rw [icmp_ne_val]
  subst v78Value
  let ret := PoisonOr.value ((BitVec.ofBool
    ((((((BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0))
      ||| BitVec.ofInt 64 (mnr y 2)) ||| BitVec.ofInt 64 (mnr y 3))
      ||| BitVec.ofInt 64 (mnr y 4)) ||| BitVec.ofInt 64 (mnr y 5))
      != BitVec.ofInt 64 0)).setWidth 32)
  have v79Value : v79 = ret := by
    long_op hv79; rw [zext_ofBool]
  subst v79Value
  denote_clear v 72 79
  -- the decision
  have fm0 : R43x6.FitsLong (mnr y 0) := by rw [hm0]; exact fitsLong_emod _ (by norm_num)
  have fm1 : R43x6.FitsLong (mnr y 1) := by rw [hm1]; exact fitsLong_emod _ (by norm_num)
  have fm2 : R43x6.FitsLong (mnr y 2) := by rw [hm2]; exact fitsLong_emod _ (by norm_num)
  have fm3 : R43x6.FitsLong (mnr y 3) := by rw [hm3]; exact fitsLong_emod _ (by norm_num)
  have fm4 : R43x6.FitsLong (mnr y 4) := by rw [hm4]; exact fitsLong_emod _ (by norm_num)
  have fm5 : R43x6.FitsLong (mnr y 5) := by
    rw [← h71, add_comm]; simpa using f71
  have hred : ∀ k, reduce l k = mnr y k := by intro k; rw [hyy]; rfl
  simp only [Com.denote_rets, ret]
  simp only [isNonzero, hred]
  by_cases hz : mnr y 0 = 0 ∧ mnr y 1 = 0 ∧ mnr y 2 = 0 ∧ mnr y 3 = 0 ∧ mnr y 4 = 0
      ∧ mnr y 5 = 0
  · rw [if_pos hz]
    obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hz
    rw [h0, h1, h2, h3, h4, h5]
    rfl
  · rw [if_neg hz]
    have hne : ¬ ((((((BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0))
        ||| BitVec.ofInt 64 (mnr y 2)) ||| BitVec.ofInt 64 (mnr y 3))
        ||| BitVec.ofInt 64 (mnr y 4)) ||| BitVec.ofInt 64 (mnr y 5)) = BitVec.ofInt 64 0) := by
      intro hc
      apply hz
      simp only [show BitVec.ofInt 64 (0:ℤ) = 0#64 from rfl, BitVec.or_eq_zero_iff,
        ofInt_eq_zero_iff fm0, ofInt_eq_zero_iff fm1, ofInt_eq_zero_iff fm2,
        ofInt_eq_zero_iff fm3, ofInt_eq_zero_iff fm4, ofInt_eq_zero_iff fm5] at hc
      tauto
    have hb : ((((((BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0))
        ||| BitVec.ofInt 64 (mnr y 2)) ||| BitVec.ofInt 64 (mnr y 3))
        ||| BitVec.ofInt 64 (mnr y 4)) ||| BitVec.ofInt 64 (mnr y 5))
        != BitVec.ofInt 64 0) = true := by
      simp only [bne_iff_ne, ne_eq]; exact hne
    rw [hb]
    rfl

/-- **Specification of `fd_r43x6_is_nonzero`, on the lifted region**: on an
`s62` vector the region returns `0` when the vector's element is zero in
`GF(2^255-19)` and `1` when it is not. The model does not appear: this is the
composition of `denote_fd_r43x6_is_nonzero` with `IsNonzeroDecidesVec`, which
is what a caller of the C function is entitled to. -/
theorem spec_denote_fd_r43x6_is_nonzero (x : Vector (BitVec 64) 8)
    (h : R43x6.S62 (x.take R43x6.limbCount)) :
    fd_r43x6_is_nonzero.denote (Ctxt.Valuation.singleton (x.map PoisonOr.value))
      = ([PoisonOr.value (if ((R43x6.decode' x : ℤ) : ZMod p) = 0 then 0 else 1)]ₕ :
          HVector TyDenote.toType [SLLVM.Ty.arith (.bitvec (.concrete 32))]) := by
  rw [denote_fd_r43x6_is_nonzero x (bcpPre_of_s62 (by norm_num) (by norm_num) h)]
  have hd := isNonzeroDecidesVec x h
  by_cases hz : ((R43x6.decode' x : ℤ) : ZMod p) = 0
  · rw [if_pos hz, hd.mpr hz]
  · rw [if_neg hz]
    have hne : isNonzero (R43x6.extractLimbs x) ≠ 0 := fun hc => hz (hd.mp hc)
    have : isNonzero (R43x6.extractLimbs x) = 1 := by
      simp only [isNonzero] at hne ⊢
      split at hne
      · exact absurd rfl hne
      · rename_i hc; rw [if_neg hc]
    rw [this]

end Firedancer.Avx512
