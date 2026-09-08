/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Field.fd_r43x6_is_nonzero
import SSA.Projects.Firedancer.Avx512.Proof.Long
import SSA.Projects.Firedancer.Avx512.Proof.Util.fd_long_if
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_biased_carry_propagate_limbs
import SSA.Projects.Firedancer.Avx512.Proof.Field.ReduceWalk
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

One `denote_step_reduce` line per instruction: its operands' hypotheses, the
`Proof/Long.lean` lemma for its opcode with the `R43x6.FitsLong` side
conditions `ReduceFacts` supplies, and the model equation it folds into. So
`hv<i>` reads `v<i> = val (bcpA (2^20) l 0)`, one per `_y k` and `_c` of the
macros. `fd_long_if` is not stepped through again; `denote_fd_long_if` is what
it computes.

`hpre` is not bookkeeping: every add in both chains is `nsw`, so an
out-of-range operand denotes to poison. -/

-- `denote_assert_folded` is a check, so it never changes the goal
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
/-- **Denotation of `fd_r43x6_is_nonzero`**: the lifted region computes the
model, instruction by instruction. The hypothesis is what makes it denote to a
value at all -- without it the first `nsw` add is poison. -/
theorem denote_fd_r43x6_is_nonzero (x : Vector (BitVec 64) 8)
    (hpre : BcpPre (2^20) (R43x6.extractLimbs x)) :
    fd_r43x6_is_nonzero.denote (Ctxt.Valuation.singleton (x.map PoisonOr.value))
      = ([PoisonOr.value (isNonzero (R43x6.extractLimbs x))]ₕ : HVector TyDenote.toType
          [SLLVM.Ty.arith (.bitvec (.concrete 32))]) := by
  -- `l` and `y` stay opaque, so every term below is limb-sized
  obtain ⟨l, hl⟩ : ∃ l, l = R43x6.extractLimbs x := ⟨_, rfl⟩
  rw [← hl] at hpre ⊢

  have fl : ∀ i, R43x6.FitsLong (l i) := by
    rw [hl]; exact fun i => fitsLong_toInt _
  obtain ⟨y, hyy⟩ : ∃ y, y = bcp (2 ^ 20) l := ⟨_, rfl⟩
  have F : ReduceFacts l y := by rw [hyy]; exact reduceFacts hpre
  have hred : ∀ k, reduce l k = mnr y k := by intro k; rw [hyy]; rfl
  have cv0 : (PoisonOr.value 0#64 : LLVM.IntW 64) = val 0 := by decide

  have cv6 : (PoisonOr.value 18446744073708503040#64 : LLVM.IntW 64)
      = val (-((2 : ℤ) ^ 20)) := by decide
  have cv7 : (PoisonOr.value 40#64 : LLVM.IntW 64) = val ((40 : ℕ) : ℤ) := by decide
  have cv8 : (PoisonOr.value 1099511627775#64 : LLVM.IntW 64)
      = val ((2 : ℤ) ^ 40 - 1) := by decide
  have cv9 : (PoisonOr.value 19#64 : LLVM.IntW 64) = val 19 := by decide
  have cv10 : (PoisonOr.value 43#64 : LLVM.IntW 64) = val ((43 : ℕ) : ℤ) := by decide
  have cv11 : (PoisonOr.value 8796093022207#64 : LLVM.IntW 64)
      = val ((2 : ℤ) ^ 43 - 1) := by decide
  have cv12 : (PoisonOr.value 1048576#64 : LLVM.IntW 64) = val ((2 : ℤ) ^ 20) := by decide
  have cv13 : (PoisonOr.value 1099511627776#64 : LLVM.IntW 64)
      = val ((2 : ℤ) ^ 40) := by decide
  have ev0 : (PoisonOr.value x[0] : LLVM.IntW 64) = val (l 0) := by
    rw [hl]; simp [val, R43x6.extractLimbs, LimbRepresentations.toInts]
  have ev1 : (PoisonOr.value x[1] : LLVM.IntW 64) = val (l 1) := by
    rw [hl]; simp [val, R43x6.extractLimbs, LimbRepresentations.toInts]
  have ev2 : (PoisonOr.value x[2] : LLVM.IntW 64) = val (l 2) := by
    rw [hl]; simp [val, R43x6.extractLimbs, LimbRepresentations.toInts]
  have ev3 : (PoisonOr.value x[3] : LLVM.IntW 64) = val (l 3) := by
    rw [hl]; simp [val, R43x6.extractLimbs, LimbRepresentations.toInts]
  have ev4 : (PoisonOr.value x[4] : LLVM.IntW 64) = val (l 4) := by
    rw [hl]; simp [val, R43x6.extractLimbs, LimbRepresentations.toInts]
  have ev5 : (PoisonOr.value x[5] : LLVM.IntW 64) = val (l 5) := by
    rw [hl]; simp [val, R43x6.extractLimbs, LimbRepresentations.toInts]

  -- long _y0 = (x##0); … long _y5 = (x##5);
  denote_step_reduce v 19 [LLVM.const?, LLVM.Ty.extractelement, Ctxt.Valuation.singleton] fold
  simp only [cv6, cv7, cv8, cv9, cv10, cv11, cv12, cv13, ev0, ev1, ev2, ev3, ev4, ev5]
    at hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv14 hv15 hv16 hv17 hv18 hv19
  denote_assert_folded v 0 19 [val]

  -- _y5 -= _b; _c = _y5>>40; _y5 &= _m40; _y0 += 19L*_c;
  denote_step_reduce v 20 only
    [hv19, hv6, add_ofInt (flags := {nsw := true}) (fl 5) fitsLong_bias (F.ha5 ▸ F.fa 5)
      (by simp), F.ha5.symm]
  denote_step_reduce v 21 only [hv20, hv7, ashr_ofInt (n := 40) (F.fa 5) (by norm_num)]
  denote_step_reduce v 22 only [hv20, hv8, and_mask_ofInt (k := 40) (by norm_num)]
  denote_step_reduce v 23 only
    [hv21, hv9, mul_ofInt (flags := {nsw := true}) rfl (fitsLong_shiftRight (F.fa 5) 40)
      fitsLong_19 F.fmul', F.hmul19]
  denote_step_reduce v 24 only
    [hv23, hv14, add_ofInt (flags := {nsw := true}) F.fmul (fl 0) (F.ha0 ▸ F.fa 0)
      (by simp), F.ha0.symm]

  -- _c = _y0>>43; _y0 &= _m43; _y1 += _c;
  denote_step_reduce v 25 only [hv24, hv10, ashr_ofInt (n := 43) (F.fa 0) (by norm_num)]
  denote_step_reduce v 26 only [hv24, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy0.symm]
  denote_step_reduce v 27 only
    [hv25, hv15, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fa 0) 43) (fl 1)
      (F.ha1 ▸ F.fa 1) (by simp), F.ha1.symm]

  -- _c = _y1>>43; _y1 &= _m43; _y2 += _c;
  denote_step_reduce v 28 only [hv27, hv10, ashr_ofInt (n := 43) (F.fa 1) (by norm_num)]
  denote_step_reduce v 29 only [hv27, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy1.symm]
  denote_step_reduce v 30 only
    [hv28, hv16, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fa 1) 43) (fl 2)
      (F.ha2 ▸ F.fa 2) (by simp), F.ha2.symm]

  -- _c = _y2>>43; _y2 &= _m43; _y3 += _c;
  denote_step_reduce v 31 only [hv30, hv10, ashr_ofInt (n := 43) (F.fa 2) (by norm_num)]
  denote_step_reduce v 32 only [hv30, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy2.symm]
  denote_step_reduce v 33 only
    [hv31, hv17, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fa 2) 43) (fl 3)
      (F.ha3 ▸ F.fa 3) (by simp), F.ha3.symm]

  -- _c = _y3>>43; _y3 &= _m43; _y4 += _c;
  denote_step_reduce v 34 only [hv33, hv10, ashr_ofInt (n := 43) (F.fa 3) (by norm_num)]
  denote_step_reduce v 35 only [hv33, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy3.symm]
  denote_step_reduce v 36 only
    [hv34, hv18, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fa 3) 43) (fl 4)
      (F.ha4 ▸ F.fa 4) (by simp), F.ha4.symm]

  -- _c = _y4>>43; _y4 &= _m43;   (`_y5 += _c` and `_y5 += _b` are scheduled later)
  denote_step_reduce v 37 only [hv36, hv10, ashr_ofInt (n := 43) (F.fa 4) (by norm_num)]
  denote_step_reduce v 38 only [hv36, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy4.symm]
  denote_assert_folded v 20 38 [val]
  denote_clear v 1 7
  denote_clear v 14 21
  denote_clear v 23 25
  denote_clear v 27 28
  denote_clear v 30 31
  denote_clear v 33 34
  denote_clear v 36 36

  -- _y0 += 19L; _c = _y0>>43; _y0 &= _m43; _y1 += _c;   (`lshr`: the chain is non-negative)
  denote_step_reduce v 39 only
    [hv26, hv9, add_ofInt (flags := {nsw := true, nuw := true}) F.fy0 fitsLong_19 (F.hA0 ▸ F.fA 0)
      (fun _ => ⟨F.hb0.1, by norm_num⟩), F.hA0.symm]
  denote_step_reduce v 40 only
    [hv39, hv10, lshr_ofInt (n := 43) (F.fA 0) (F.fA0 0) (by norm_num) (by norm_num)]
  denote_step_reduce v 41 only [hv39, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 42 only
    [hv29, hv40, add_ofInt (flags := {nsw := true, nuw := true}) F.fy1
      (fitsLong_shiftRight (F.fA 0) 43) (F.hA1 ▸ F.fA 1)
      (fun _ => ⟨F.hb1.1, shiftRight_nonneg (F.fA0 0) 43⟩), F.hA1.symm]
  denote_step_reduce v 43 only
    [hv42, hv10, lshr_ofInt (n := 43) (F.fA 1) (F.fA0 1) (by norm_num) (by norm_num)]
  denote_step_reduce v 44 only [hv42, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 45 only
    [hv32, hv43, add_ofInt (flags := {nsw := true, nuw := true}) F.fy2
      (fitsLong_shiftRight (F.fA 1) 43) (F.hA2 ▸ F.fA 2)
      (fun _ => ⟨F.hb2.1, shiftRight_nonneg (F.fA0 1) 43⟩), F.hA2.symm]
  denote_step_reduce v 46 only
    [hv45, hv10, lshr_ofInt (n := 43) (F.fA 2) (F.fA0 2) (by norm_num) (by norm_num)]
  denote_step_reduce v 47 only [hv45, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 48 only
    [hv35, hv46, add_ofInt (flags := {nsw := true, nuw := true}) F.fy3
      (fitsLong_shiftRight (F.fA 2) 43) (F.hA3 ▸ F.fA 3)
      (fun _ => ⟨F.hb3.1, shiftRight_nonneg (F.fA0 2) 43⟩), F.hA3.symm]
  denote_step_reduce v 49 only
    [hv48, hv10, lshr_ofInt (n := 43) (F.fA 3) (F.fA0 3) (by norm_num) (by norm_num)]
  denote_step_reduce v 50 only [hv48, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 51 only
    [hv38, hv49, add_ofInt (flags := {nsw := true, nuw := true}) F.fy4
      (fitsLong_shiftRight (F.fA 3) 43) (F.hA4 ▸ F.fA 4)
      (fun _ => ⟨F.hb4.1, shiftRight_nonneg (F.fA0 3) 43⟩), F.hA4.symm]
  denote_step_reduce v 52 only
    [hv51, hv10, lshr_ofInt (n := 43) (F.fA 4) (F.fA0 4) (by norm_num) (by norm_num)]
  denote_step_reduce v 53 only [hv51, hv11, and_mask_ofInt (k := 43) (by norm_num)]

  -- the carry propagate's `_y5 += _b` and `_y5 += _c`, scheduled here
  denote_step_reduce v 54 only
    [hv22, hv12, add_ofInt (flags := {nsw := true, nuw := true})
      (fitsLong_emod _ (by norm_num)) fitsLong_bias' F.f54
      (fun _ => ⟨Int.emod_nonneg _ (by norm_num), by norm_num⟩)]
  denote_step_reduce v 55 only
    [hv54, hv37, add_ofInt (flags := {nsw := true}) F.f54 (fitsLong_shiftRight (F.fa 4) 43)
      (F.hy5 ▸ F.f55) (by simp), F.hy5.symm]
  denote_step_reduce v 56 only
    [hv55, hv52, add_ofInt (flags := {nsw := true, nuw := true}) F.fy5
      (fitsLong_shiftRight (F.fA 4) 43) (F.hA5 ▸ F.fA 5)
      (fun _ => ⟨F.hy5nn, shiftRight_nonneg (F.fA0 4) 43⟩), F.hA5.symm]
  denote_step_reduce v 57 only [hv56, hv8, and_mask_ofInt (k := 40) (by norm_num)]
  denote_assert_folded v 39 57 [val]
  denote_clear v 8 9
  denote_clear v 12 12
  denote_clear v 22 40
  denote_clear v 42 43
  denote_clear v 45 46
  denote_clear v 48 49
  denote_clear v 51 52
  denote_clear v 54 55

  -- _c = _y5>>40 decided, then `fd_long_if( !_c, 19L, 0L )`
  denote_step_reduce v 58 only
    [hv56, hv13, icmp_ult_ofInt (b := (2 : ℤ) ^ 40) (F.fA 5) (by simp [R43x6.FitsLong]) (F.fA0 5)
      (by positivity)]
  denote_step_reduce v 59 only [hv58, zext_ofBool]
  denote_step_all v 60
  have hv60' : v60 = val (if mnrQ y = 0 then (19 : ℤ) else 0) := by
    simp only [hv60, hv59, Expr.denoteOp1, Expr.denoteOpPure, SLLVM.denoteOp_call]
    show HVector.head (fd_long_if.denote (Ctxt.Valuation.singleton
      (PoisonOr.value ((BitVec.ofBool (decide (mnrA y 5 < 2 ^ 40))).setWidth 32)))) = _
    rw [denote_fd_long_if]
    simp only [HVector.head, fdLongIf, val]
    congr
    simp [F.hqlt, BitVec.ofBool, Bool.cond_decide, apply_ite]

  -- _y0 -= fd_long_if(…), and the borrow chain from there
  denote_step_reduce v 61 only
    [hv41, hv60', sub_ofInt (flags := {nsw := true}) rfl (fitsLong_emod _ (by norm_num)) F.fif
      (F.hE0 ▸ F.fE 0), F.hE0.symm]
  denote_step_reduce v 62 only [hv61, hv10, ashr_ofInt (n := 43) (F.fE 0) (by norm_num)]
  denote_step_reduce v 63 only
    [hv62, hv44, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 0) 43)
      (fitsLong_emod _ (by norm_num)) (F.hE1 ▸ F.fE 1) (by simp), F.hE1]
  denote_step_reduce v 64 only [hv63, hv10, ashr_ofInt (n := 43) (F.fE 1) (by norm_num)]
  denote_step_reduce v 65 only
    [hv64, hv47, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 1) 43)
      (fitsLong_emod _ (by norm_num)) (F.hE2 ▸ F.fE 2) (by simp), F.hE2]
  denote_step_reduce v 66 only [hv65, hv10, ashr_ofInt (n := 43) (F.fE 2) (by norm_num)]
  denote_step_reduce v 67 only
    [hv66, hv50, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 2) 43)
      (fitsLong_emod _ (by norm_num)) (F.hE3 ▸ F.fE 3) (by simp), F.hE3]
  denote_step_reduce v 68 only [hv67, hv10, ashr_ofInt (n := 43) (F.fE 3) (by norm_num)]
  denote_step_reduce v 69 only
    [hv68, hv53, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 3) 43)
      (fitsLong_emod _ (by norm_num)) (F.hE4 ▸ F.fE 4) (by simp), F.hE4]
  denote_step_reduce v 70 only [hv69, hv10, ashr_ofInt (n := 43) (F.fE 4) (by norm_num)]
  denote_step_reduce v 71 only
    [hv70, hv57, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 4) 43)
      (fitsLong_emod (mnrA y 5) (k := 40) (by norm_num)) F.f72 (by simp), F.h71]
  denote_assert_folded v 58 59 [val]
  denote_assert_folded v 61 71 [val]
  clear hv60'
  denote_clear v 10 10
  denote_clear v 13 13
  denote_clear v 41 60

  -- l0|l1|l2|l3|l4|l5, with the mask taken across the disjunction
  denote_step_reduce v 72 only [hv63, hv61, or_ofInt]
  denote_step_reduce v 73 only [hv72, hv65, or_val]
  denote_step_reduce v 74 only [hv73, hv67, or_val]
  denote_step_reduce v 75 only [hv74, hv69, or_val]
  denote_step_reduce v 76 only
    [hv75, hv11, val, LLVM.and, PoisonOr.value_bind, LLVM.and?, BitVec.and_or_distrib_right,
      and_mask_bv _ (show (43 : ℕ) < 64 by norm_num),
      F.hm0.symm, F.hm1.symm, F.hm2.symm, F.hm3.symm, F.hm4.symm]
  denote_step_reduce v 77 only [hv76, hv71, or_val]
  denote_assert_folded v 72 77 [val]

  -- zero exactly when every reduced limb is; named, to keep the last two steps short
  have hzero : (BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0)
      ||| BitVec.ofInt 64 (mnr y 2) ||| BitVec.ofInt 64 (mnr y 3)
      ||| BitVec.ofInt 64 (mnr y 4) ||| BitVec.ofInt 64 (mnr y 5)) = BitVec.ofInt 64 0
      ↔ (mnr y 0 = 0 ∧ mnr y 1 = 0 ∧ mnr y 2 = 0 ∧ mnr y 3 = 0 ∧ mnr y 4 = 0 ∧ mnr y 5 = 0) := by
    simp only [show BitVec.ofInt 64 (0 : ℤ) = 0#64 from rfl, BitVec.or_eq_zero_iff,
      ofInt_eq_zero_iff F.fm0, ofInt_eq_zero_iff F.fm1, ofInt_eq_zero_iff F.fm2,
      ofInt_eq_zero_iff F.fm3, ofInt_eq_zero_iff F.fm4, ofInt_eq_zero_iff F.fm5]
    tauto
  obtain ⟨o, ho⟩ : ∃ o : BitVec 64, o = (BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0)
      ||| BitVec.ofInt 64 (mnr y 2) ||| BitVec.ofInt 64 (mnr y 3) ||| BitVec.ofInt 64 (mnr y 4)
      ||| BitVec.ofInt 64 (mnr y 5)) := ⟨_, rfl⟩
  rw [← ho] at hv77 hzero
  denote_clear v 11 11
  denote_clear v 62 76

  -- !!(…): on the canonical representative, the disjunction decides the element
  simp only [cv0] at hv0
  denote_step_reduce v 78 only [hv77, hv0, icmp_ne_val]
  denote_step_reduce v 79 only [hv78, zext_ofBool]
  denote_assert_folded v 78 79 [val]
  denote_clear v 0 0
  denote_clear v 77 78

  simp only [Com.denote_rets, hv79, isNonzero, hred]
  by_cases hz : mnr y 0 = 0 ∧ mnr y 1 = 0 ∧ mnr y 2 = 0 ∧ mnr y 3 = 0 ∧ mnr y 4 = 0
      ∧ mnr y 5 = 0
  · rw [if_pos hz, hzero.mpr hz]
    rfl
  · rw [if_neg hz]
    have hne : ¬ (o = BitVec.ofInt 64 0) := fun hc => hz (hzero.mp hc)
    have hb : (o != BitVec.ofInt 64 0) = true := by
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
