/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanMLIR.Tactic
public import SSA.Projects.Firedancer.Avx512.Proof.Long
public import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_biased_carry_propagate_limbs
public import SSA.Projects.Firedancer.Avx512.Proof.Field.ReduceWalk
public import SSA.Projects.Firedancer.Avx512.Proof.Util.fd_long_if
public import SSA.Projects.Firedancer.Avx512.Proof.Util.fd_int_if
public import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_diagnose
public import SSA.Projects.Firedancer.MLIR.DenoteStep

@[expose] public section

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The element six `long` lanes hold: `R43x6.decodeLimbs` of their signed
values, poison in any lane giving poison. -/
def decodeVals (a0 a1 a2 a3 a4 a5 : LLVM.IntW 64) : PoisonOr ℤ := do
  let b0 ← a0; let b1 ← a1; let b2 ← a2; let b3 ← a3; let b4 ← a4; let b5 ← a5
  return R43x6.decodeLimbs
    (R43x6.limbs6 b0.toInt b1.toInt b2.toInt b3.toInt b4.toInt b5.toInt)

/-- On the six low lanes of a vector, `decodeVals` is `R43x6.decode'`. -/
theorem decodeVals_lanes (x : Vector (BitVec 64) 8) :
    decodeVals (.value x[0]) (.value x[1]) (.value x[2]) (.value x[3]) (.value x[4])
        (.value x[5]) = .value (R43x6.decode' x) := by
  simp [decodeVals, R43x6.decode'_eq, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five]

/-- Changing the last lane by `d` moves the decoded value by that lane's
weight, `2^(43*5)`. -/
theorem decodeVals_last {a0 a1 a2 a3 a4 : LLVM.IntW 64} {b c : BitVec 64} {d : ℤ}
    (h : c.toInt = b.toInt - d) :
    decodeVals a0 a1 a2 a3 a4 (.value c)
      = (· - 2 ^ (43 * 5) * d) <$> decodeVals a0 a1 a2 a3 a4 (.value b) := by
  cases a0 using PoisonOr.casesOn' <;> cases a1 using PoisonOr.casesOn' <;>
    cases a2 using PoisonOr.casesOn' <;> cases a3 using PoisonOr.casesOn' <;>
    cases a4 using PoisonOr.casesOn' <;>
    simp [decodeVals, R43x6.limbs6_zero, R43x6.limbs6_one, R43x6.limbs6_two, R43x6.limbs6_three, R43x6.limbs6_four, R43x6.limbs6_five, h]; ring

/-- `llvm.icmp eq` against a `val`, on an accumulated left operand. -/
theorem icmp_eq_val (bv : BitVec 64) (b : ℤ) :
    LLVM.icmp .eq (.value bv) (val b)
      = .value (BitVec.ofBool (bv == BitVec.ofInt 64 b)) := rfl

/-- `llvm.trunc` of a `long` to an `int`. -/
theorem trunc_val (a : ℤ) :
    LLVM.trunc 32 (val a) = .value ((BitVec.ofInt 64 a).setWidth 32) := rfl

/-- `llvm.and` on two `int`s. -/
theorem and32_value (u w : BitVec 32) :
    LLVM.and (.value u) (.value w) = .value (u &&& w) := rfl

/-- The low bit of a `long`, as `(int)x & 1` computes it. -/
theorem lowbit_setWidth (a : ℤ) :
    (BitVec.ofInt 64 a).setWidth 32 &&& 1#32 = BitVec.ofInt 32 (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofInt, Nat.and_one_is_mod]
  omega

-- `denote_assert_folded` is a check, so it never changes the goal
set_option linter.unusedTactic false in
set_option maxHeartbeats 4000000 in
theorem fd_r43x6_diagnose_conforms (x : Vector (BitVec 64) 8) :
    fd_r43x6_diagnose_spec x := by
  simp only [fd_r43x6_diagnose_spec]
  intro inputBounds

  suffices h : fd_r43x6_diagnose.denote (Ctxt.Valuation.singleton (x.map PoisonOr.value))
      = ([PoisonOr.value (diagnose (R43x6.extractLimbs x))]ₕ : HVector TyDenote.toType
          [SLLVM.Ty.arith (.bitvec (.concrete 32))]) by
    rw [h]; rfl

  -- `l` and `y` stay opaque, so every term below is limb-sized
  obtain ⟨l, hl⟩ : ∃ l, l = R43x6.extractLimbs x := ⟨_, rfl⟩
  rw [← hl]
  have hpre : BcpPre (2 ^ 20) l := by
    rw [hl]; exact bcpPre_of_s62 (by norm_num) (by norm_num) inputBounds

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
  denote_step_reduce v 20 [LLVM.const?, LLVM.Ty.extractelement, Ctxt.Valuation.singleton] fold
  simp only [cv6, cv7, cv8, cv9, cv10, cv11, cv12, cv13, ev0, ev1, ev2, ev3, ev4, ev5]
    at hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv15 hv16 hv17 hv18 hv19 hv20
  denote_assert_folded v 0 20 [val]

  -- _y5 -= _b; _c = _y5>>40; _y5 &= _m40; _y0 += 19L*_c;
  denote_step_reduce v 21 only
    [hv20, hv6, add_ofInt (flags := {nsw := true}) (fl 5) fitsLong_bias (F.ha5 ▸ F.fa 5)
      (by simp), F.ha5.symm]
  denote_step_reduce v 22 only [hv21, hv7, ashr_ofInt (n := 40) (F.fa 5) (by norm_num)]
  denote_step_reduce v 23 only [hv21, hv8, and_mask_ofInt (k := 40) (by norm_num)]
  denote_step_reduce v 24 only
    [hv22, hv9, mul_ofInt (flags := {nsw := true}) rfl (fitsLong_shiftRight (F.fa 5) 40)
      fitsLong_19 F.fmul', F.hmul19]
  denote_step_reduce v 25 only
    [hv24, hv15, add_ofInt (flags := {nsw := true}) F.fmul (fl 0) (F.ha0 ▸ F.fa 0)
      (by simp), F.ha0.symm]

  -- _c = _y0>>43; _y0 &= _m43; _y1 += _c;
  denote_step_reduce v 26 only [hv25, hv10, ashr_ofInt (n := 43) (F.fa 0) (by norm_num)]
  denote_step_reduce v 27 only [hv25, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy0.symm]
  denote_step_reduce v 28 only
    [hv26, hv16, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fa 0) 43) (fl 1)
      (F.ha1 ▸ F.fa 1) (by simp), F.ha1.symm]

  -- _c = _y1>>43; _y1 &= _m43; _y2 += _c;
  denote_step_reduce v 29 only [hv28, hv10, ashr_ofInt (n := 43) (F.fa 1) (by norm_num)]
  denote_step_reduce v 30 only [hv28, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy1.symm]
  denote_step_reduce v 31 only
    [hv29, hv17, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fa 1) 43) (fl 2)
      (F.ha2 ▸ F.fa 2) (by simp), F.ha2.symm]

  -- _c = _y2>>43; _y2 &= _m43; _y3 += _c;
  denote_step_reduce v 32 only [hv31, hv10, ashr_ofInt (n := 43) (F.fa 2) (by norm_num)]
  denote_step_reduce v 33 only [hv31, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy2.symm]
  denote_step_reduce v 34 only
    [hv32, hv18, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fa 2) 43) (fl 3)
      (F.ha3 ▸ F.fa 3) (by simp), F.ha3.symm]

  -- _c = _y3>>43; _y3 &= _m43; _y4 += _c;
  denote_step_reduce v 35 only [hv34, hv10, ashr_ofInt (n := 43) (F.fa 3) (by norm_num)]
  denote_step_reduce v 36 only [hv34, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy3.symm]
  denote_step_reduce v 37 only
    [hv35, hv19, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fa 3) 43) (fl 4)
      (F.ha4 ▸ F.fa 4) (by simp), F.ha4.symm]

  -- _c = _y4>>43; _y4 &= _m43;   (`_y5 += _c` and `_y5 += _b` are scheduled later)
  denote_step_reduce v 38 only [hv37, hv10, ashr_ofInt (n := 43) (F.fa 4) (by norm_num)]
  denote_step_reduce v 39 only [hv37, hv11, and_mask_ofInt (k := 43) (by norm_num), F.hy4.symm]
  denote_assert_folded v 21 39 [val]
  denote_clear v 1 7
  denote_clear v 15 22
  denote_clear v 24 26
  denote_clear v 28 29
  denote_clear v 31 32
  denote_clear v 34 35
  denote_clear v 37 37

  -- _y0 += 19L; _c = _y0>>43; _y0 &= _m43; _y1 += _c;   (`lshr`: the chain is non-negative)
  denote_step_reduce v 40 only
    [hv27, hv9, add_ofInt (flags := {nsw := true, nuw := true}) F.fy0 fitsLong_19 (F.hA0 ▸ F.fA 0)
      (fun _ => ⟨F.hb0.1, by norm_num⟩), F.hA0.symm]
  denote_step_reduce v 41 only
    [hv40, hv10, lshr_ofInt (n := 43) (F.fA 0) (F.fA0 0) (by norm_num) (by norm_num)]
  denote_step_reduce v 42 only [hv40, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 43 only
    [hv30, hv41, add_ofInt (flags := {nsw := true, nuw := true}) F.fy1
      (fitsLong_shiftRight (F.fA 0) 43) (F.hA1 ▸ F.fA 1)
      (fun _ => ⟨F.hb1.1, shiftRight_nonneg (F.fA0 0) 43⟩), F.hA1.symm]
  denote_step_reduce v 44 only
    [hv43, hv10, lshr_ofInt (n := 43) (F.fA 1) (F.fA0 1) (by norm_num) (by norm_num)]
  denote_step_reduce v 45 only [hv43, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 46 only
    [hv33, hv44, add_ofInt (flags := {nsw := true, nuw := true}) F.fy2
      (fitsLong_shiftRight (F.fA 1) 43) (F.hA2 ▸ F.fA 2)
      (fun _ => ⟨F.hb2.1, shiftRight_nonneg (F.fA0 1) 43⟩), F.hA2.symm]
  denote_step_reduce v 47 only
    [hv46, hv10, lshr_ofInt (n := 43) (F.fA 2) (F.fA0 2) (by norm_num) (by norm_num)]
  denote_step_reduce v 48 only [hv46, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 49 only
    [hv36, hv47, add_ofInt (flags := {nsw := true, nuw := true}) F.fy3
      (fitsLong_shiftRight (F.fA 2) 43) (F.hA3 ▸ F.fA 3)
      (fun _ => ⟨F.hb3.1, shiftRight_nonneg (F.fA0 2) 43⟩), F.hA3.symm]
  denote_step_reduce v 50 only
    [hv49, hv10, lshr_ofInt (n := 43) (F.fA 3) (F.fA0 3) (by norm_num) (by norm_num)]
  denote_step_reduce v 51 only [hv49, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 52 only
    [hv39, hv50, add_ofInt (flags := {nsw := true, nuw := true}) F.fy4
      (fitsLong_shiftRight (F.fA 3) 43) (F.hA4 ▸ F.fA 4)
      (fun _ => ⟨F.hb4.1, shiftRight_nonneg (F.fA0 3) 43⟩), F.hA4.symm]
  denote_step_reduce v 53 only
    [hv52, hv10, lshr_ofInt (n := 43) (F.fA 4) (F.fA0 4) (by norm_num) (by norm_num)]
  denote_step_reduce v 54 only [hv52, hv11, and_mask_ofInt (k := 43) (by norm_num)]

  -- the carry propagate's `_y5 += _b` and `_y5 += _c`, scheduled here
  denote_step_reduce v 55 only
    [hv23, hv12, add_ofInt (flags := {nsw := true, nuw := true})
      (fitsLong_emod _ (by norm_num)) fitsLong_bias' F.f54
      (fun _ => ⟨Int.emod_nonneg _ (by norm_num), by norm_num⟩)]
  denote_step_reduce v 56 only
    [hv55, hv38, add_ofInt (flags := {nsw := true}) F.f54 (fitsLong_shiftRight (F.fa 4) 43)
      (F.hy5 ▸ F.f55) (by simp), F.hy5.symm]
  denote_step_reduce v 57 only
    [hv56, hv53, add_ofInt (flags := {nsw := true, nuw := true}) F.fy5
      (fitsLong_shiftRight (F.fA 4) 43) (F.hA5 ▸ F.fA 5)
      (fun _ => ⟨F.hy5nn, shiftRight_nonneg (F.fA0 4) 43⟩), F.hA5.symm]
  denote_step_reduce v 58 only [hv57, hv8, and_mask_ofInt (k := 40) (by norm_num)]
  denote_assert_folded v 40 58 [val]
  denote_clear v 8 9
  denote_clear v 12 12
  denote_clear v 23 41
  denote_clear v 43 44
  denote_clear v 46 47
  denote_clear v 49 50
  denote_clear v 52 53
  denote_clear v 55 56

  -- _c = _y5>>40 decided, then `fd_long_if( !_c, 19L, 0L )`
  denote_step_reduce v 59 only
    [hv57, hv13, icmp_ult_ofInt (b := (2 : ℤ) ^ 40) (F.fA 5) (by simp [R43x6.FitsLong]) (F.fA0 5)
      (by positivity)]
  denote_step_reduce v 60 only [hv59, zext_ofBool]
  denote_step_all v 61
  have hv61' : v61 = val (if mnrQ y = 0 then (19 : ℤ) else 0) := by
    simp only [hv61, hv60, Expr.denoteOp1, Expr.denoteOpPure, SLLVM.denoteOp_call]
    show HVector.head (fd_long_if.denote (Ctxt.Valuation.singleton
      (PoisonOr.value ((BitVec.ofBool (decide (mnrA y 5 < 2 ^ 40))).setWidth 32)))) = _
    rw [denote_fd_long_if]
    simp only [HVector.head, fdLongIf, val]
    congr
    simp [F.hqlt, BitVec.ofBool, Bool.cond_decide, apply_ite]

  -- _y0 -= fd_long_if(…), and the borrow chain from there
  denote_step_reduce v 62 only
    [hv42, hv61', sub_ofInt (flags := {nsw := true}) rfl (fitsLong_emod _ (by norm_num)) F.fif
      (F.hE0 ▸ F.fE 0), F.hE0.symm]
  denote_step_reduce v 63 only [hv62, hv10, ashr_ofInt (n := 43) (F.fE 0) (by norm_num)]
  denote_step_reduce v 64 only
    [hv63, hv45, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 0) 43)
      (fitsLong_emod _ (by norm_num)) (F.hE1 ▸ F.fE 1) (by simp), F.hE1]
  denote_step_reduce v 65 only [hv64, hv10, ashr_ofInt (n := 43) (F.fE 1) (by norm_num)]
  denote_step_reduce v 66 only
    [hv65, hv48, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 1) 43)
      (fitsLong_emod _ (by norm_num)) (F.hE2 ▸ F.fE 2) (by simp), F.hE2]
  denote_step_reduce v 67 only [hv66, hv10, ashr_ofInt (n := 43) (F.fE 2) (by norm_num)]
  denote_step_reduce v 68 only
    [hv67, hv51, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 2) 43)
      (fitsLong_emod _ (by norm_num)) (F.hE3 ▸ F.fE 3) (by simp), F.hE3]
  denote_step_reduce v 69 only [hv68, hv10, ashr_ofInt (n := 43) (F.fE 3) (by norm_num)]
  denote_step_reduce v 70 only
    [hv69, hv54, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 3) 43)
      (fitsLong_emod _ (by norm_num)) (F.hE4 ▸ F.fE 4) (by simp), F.hE4]
  denote_step_reduce v 71 only [hv70, hv10, ashr_ofInt (n := 43) (F.fE 4) (by norm_num)]
  denote_step_reduce v 72 only
    [hv71, hv58, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (F.fE 4) 43)
      (fitsLong_emod (mnrA y 5) (k := 40) (by norm_num)) F.f72 (by simp), F.h71]
  denote_assert_folded v 59 60 [val]
  denote_assert_folded v 62 72 [val]
  clear hv61'
  denote_clear v 10 10
  denote_clear v 13 13
  denote_clear v 42 61

  -- !!(l0|l1|l2|l3|l4|l5), with the mask taken across the disjunction
  denote_step_reduce v 73 only [hv64, hv62, or_ofInt]
  denote_step_reduce v 74 only [hv73, hv66, or_val]
  denote_step_reduce v 75 only [hv74, hv68, or_val]
  denote_step_reduce v 76 only [hv75, hv70, or_val]
  denote_step_reduce v 77 only
    [hv76, hv11, val, LLVM.and, PoisonOr.value_bind, LLVM.and?, BitVec.and_or_distrib_right,
      and_mask_bv _ (show (43 : ℕ) < 64 by norm_num),
      F.hm0.symm, F.hm1.symm, F.hm2.symm, F.hm3.symm, F.hm4.symm]
  denote_step_reduce v 78 only [hv77, hv72, or_val]
  denote_assert_folded v 73 78 [val]

  -- zero exactly when every reduced limb is; named, to keep the last four steps short
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
  rw [← ho] at hv78 hzero
  denote_clear v 11 11
  denote_clear v 63 77

  -- `x == 0` decided, limb 0's low bit, and `fd_int_if( !x, l0 & 1, -1 )`
  simp only [cv0] at hv0
  denote_step_reduce v 79 only [hv78, hv0, icmp_eq_val]
  denote_step_reduce v 80 only [hv79, zext_ofBool]
  denote_step_reduce v 81 only [hv62, trunc_val]
  denote_step_reduce v 82 only [hv81, hv14, and32_value, lowbit_setWidth]
  denote_assert_folded v 79 82 [val]
  denote_clear v 0 0
  denote_clear v 14 14
  denote_clear v 62 62
  denote_clear v 78 79
  denote_clear v 81 81
  denote_step_all v 83
  have hv83' : v83 = PoisonOr.value
      (if o = BitVec.ofInt 64 0 then -1#32 else BitVec.ofInt 32 (mnrE y 0 % 2)) := by
    simp only [hv83, hv82, hv80, Expr.denoteOp1, Expr.denoteOpPure, SLLVM.denoteOp_call]
    show HVector.head (fd_int_if.denote (Ctxt.Valuation.ofPair
      (PoisonOr.value (BitVec.ofInt 32 (mnrE y 0 % 2)))
      (PoisonOr.value ((BitVec.ofBool (o == BitVec.ofInt 64 0)).setWidth 32)))) = _
    rw [denote_fd_int_if]
    by_cases hb : o = BitVec.ofInt 64 0
    · simp [hb, fdIntIf, HVector.head]
    · have hb' : ¬ (o = 0#64) := by
        simpa only [show BitVec.ofInt 64 (0 : ℤ) = 0#64 from rfl] using hb
      have hbb : (o == 0#64) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact hb'
      simp [hbb, hb', fdIntIf, HVector.head]

  -- `% 2` of the reduced limb 0 is `% 2` of the borrow chain's, since `2 ∣ 2^43`
  have hmod : mnr y 0 % 2 = mnrE y 0 % 2 := by
    rw [F.hm0]; exact Int.emod_emod_of_dvd _ (by norm_num)
  simp only [Com.denote_rets, hv83', diagnose, isNonzero, hred]
  by_cases hz : mnr y 0 = 0 ∧ mnr y 1 = 0 ∧ mnr y 2 = 0 ∧ mnr y 3 = 0 ∧ mnr y 4 = 0
      ∧ mnr y 5 = 0
  · rw [if_pos hz, if_pos (hzero.mpr hz)]
    rfl
  · rw [if_neg hz, if_neg (fun hc => hz (hzero.mp hc)), hmod]
    rfl

end Firedancer.Avx512
