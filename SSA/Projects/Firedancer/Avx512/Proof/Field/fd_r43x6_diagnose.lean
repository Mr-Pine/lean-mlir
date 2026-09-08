/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Tactic
import SSA.Projects.Firedancer.Avx512.Proof.Long
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_biased_carry_propagate_limbs
import SSA.Projects.Firedancer.Avx512.Proof.Field.fd_r43x6_mod_nearly_reduced_limbs
import SSA.Projects.Firedancer.Avx512.Proof.Util.fd_long_if
import SSA.Projects.Firedancer.Avx512.Proof.Util.fd_int_if
import SSA.Projects.Firedancer.Avx512.Spec.Field.fd_r43x6_diagnose
import SSA.Projects.Firedancer.MLIR.DenoteStep

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
  simp [decodeVals, R43x6.decode'_eq, R43x6.limbs6]

/-- Changing the last lane by `d` moves the decoded value by that lane's
weight, `2^(43*5)`. -/
theorem decodeVals_last {a0 a1 a2 a3 a4 : LLVM.IntW 64} {b c : BitVec 64} {d : ℤ}
    (h : c.toInt = b.toInt - d) :
    decodeVals a0 a1 a2 a3 a4 (.value c)
      = (· - 2 ^ (43 * 5) * d) <$> decodeVals a0 a1 a2 a3 a4 (.value b) := by
  cases a0 using PoisonOr.casesOn' <;> cases a1 using PoisonOr.casesOn' <;>
    cases a2 using PoisonOr.casesOn' <;> cases a3 using PoisonOr.casesOn' <;>
    cases a4 using PoisonOr.casesOn' <;>
    simp [decodeVals, R43x6.limbs6, h]; ring

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

set_option maxHeartbeats 4000000 in
theorem fd_r43x6_diagnose_conforms (x : Vector (BitVec 64) 8) :
    fd_r43x6_diagnose_spec x := by
  simp only [fd_r43x6_diagnose_spec]
  intro inputBounds

  suffices h : fd_r43x6_diagnose.denote (Ctxt.Valuation.singleton (x.map PoisonOr.value))
      = ([PoisonOr.value (diagnose (R43x6.extractLimbs x))]ₕ : HVector TyDenote.toType
          [SLLVM.Ty.arith (.bitvec (.concrete 32))]) by
    rw [h]; rfl

  /- The limbs `fd_r43x6_extract_limbs` returns, opaque: `simp` never unfolds
  `l` back to the vector, so every term below stays limb-sized. -/
  obtain ⟨l, hl⟩ : ∃ l, l = R43x6.extractLimbs x := ⟨_, rfl⟩
  rw [← hl]
  have hpre : BcpPre (2 ^ 20) l := by
    rw [hl]; exact bcpPre_of_s62 (by norm_num) (by norm_num) inputBounds

  /- What the macro proof says about the chain: every `nsw` operand fits a
  `long` (`fa`, `fmul`), which is what keeps the region from denoting poison. -/
  have fl : ∀ i, R43x6.FitsLong (l i) := by
    rw [hl]; exact fun i => fitsLong_toInt _
  have fa := bcpA_fitsLong (b := 2 ^ 20) (x := l) (by norm_num) (by norm_num) hpre
  obtain ⟨fmul, f54, f55⟩ := bcp_aux_fitsLong (b := 2 ^ 20)
    (x := l) (by norm_num) (by norm_num) hpre
  have fmul' : R43x6.FitsLong ((bcpA (2 ^ 20) l 5 >>> 40) * 19) := by
    rw [mul_comm] at fmul; exact fmul
  have fc6 : R43x6.FitsLong (-((2 : ℤ) ^ 20)) := by simp [R43x6.FitsLong]
  have fc9 : R43x6.FitsLong (19 : ℤ) := by simp [R43x6.FitsLong]

  /- The chain as recurrences, one per `_y k` of the macro. -/
  have ha5 : bcpA (2 ^ 20) l 5 = l 5 + (-((2 : ℤ) ^ 20)) := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha0 : bcpA (2 ^ 20) l 0 = (19 : ℤ) * (bcpA (2 ^ 20) l 5 >>> 40) + l 0 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha1 : bcpA (2 ^ 20) l 1 = (bcpA (2 ^ 20) l 0 >>> 43) + l 1 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha2 : bcpA (2 ^ 20) l 2 = (bcpA (2 ^ 20) l 1 >>> 43) + l 2 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha3 : bcpA (2 ^ 20) l 3 = (bcpA (2 ^ 20) l 2 >>> 43) + l 3 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha4 : bcpA (2 ^ 20) l 4 = (bcpA (2 ^ 20) l 3 >>> 43) + l 4 := by
    simp [bcpA, R43x6.limbs6]; ring
  have ha5' := ha5.symm
  have ha0' := ha0.symm
  have ha1' := ha1.symm
  have ha2' := ha2.symm
  have ha3' := ha3.symm
  have ha4' := ha4.symm
  have hmul19 : (bcpA (2 ^ 20) l 5 >>> 40) * (19 : ℤ)
      = (19 : ℤ) * (bcpA (2 ^ 20) l 5 >>> 40) := mul_comm _ _

  /- The macro's output, opaque in the same way as `l`. -/
  obtain ⟨y, hyy⟩ : ∃ y, y = bcp (2 ^ 20) l := ⟨_, rfl⟩
  have hy0 : y 0 = bcpA (2 ^ 20) l 0 % (2 : ℤ) ^ 43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy1 : y 1 = bcpA (2 ^ 20) l 1 % (2 : ℤ) ^ 43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy2 : y 2 = bcpA (2 ^ 20) l 2 % (2 : ℤ) ^ 43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy3 : y 3 = bcpA (2 ^ 20) l 3 % (2 : ℤ) ^ 43 := by rw [hyy]; simp [bcp, R43x6.limbs6]
  have hy4 : y 4 = bcpA (2 ^ 20) l 4 % (2 : ℤ) ^ 43 := by rw [hyy]; simp [bcp, R43x6.limbs6]

  have hy0' := hy0.symm
  have hy1' := hy1.symm
  have hy2' := hy2.symm
  have hy3' := hy3.symm
  have hy4' := hy4.symm

  /- `fd_r43x6_mod_nearly_reduced_limbs` runs on `y`, which the macro proof
  says is nearly reduced. Its own chains fit a `long` and the `_y0 += 19` one
  is non-negative, which is what the `nuw` adds and the `lshr`s need. -/
  have hmnr := bcp_nearlyReduced hpre
  rw [← hyy] at hmnr
  have hlimbs := bcp_limbs (b := 2 ^ 20) (x := l) (by norm_num) (by norm_num) hpre
  rw [← hyy] at hlimbs
  obtain ⟨hbl, hb5⟩ := hlimbs
  have hb0 := hbl 0 (by decide)
  have hb1 := hbl 1 (by decide)
  have hb2 := hbl 2 (by decide)
  have hb3 := hbl 3 (by decide)
  have hb4 := hbl 4 (by decide)
  have fA := mnrA_fitsLong hmnr
  have fE := mnrE_fitsLong hmnr
  have fA0 := mnrA_nonneg hmnr
  have f71 := mnr_limb5_fitsLong hmnr
  have fc12 : R43x6.FitsLong ((2 : ℤ) ^ 20) := by simp [R43x6.FitsLong]
  have fy0 : R43x6.FitsLong (y 0) := by simp only [R43x6.FitsLong]; omega
  have fy1 : R43x6.FitsLong (y 1) := by simp only [R43x6.FitsLong]; omega
  have fy2 : R43x6.FitsLong (y 2) := by simp only [R43x6.FitsLong]; omega
  have fy3 : R43x6.FitsLong (y 3) := by simp only [R43x6.FitsLong]; omega
  have fy4 : R43x6.FitsLong (y 4) := by simp only [R43x6.FitsLong]; omega
  have fy5 : R43x6.FitsLong (y 5) := by simp only [R43x6.FitsLong]; omega
  have hy5 : y 5 = bcpA (2 ^ 20) l 5 % (2 : ℤ) ^ 40 + (2 : ℤ) ^ 20
      + (bcpA (2 ^ 20) l 4 >>> 43) := by rw [hyy]; simp [bcp, R43x6.limbs6]; ring
  have hy5' := hy5.symm
  have hA0 : mnrA y 0 = y 0 + 19 := by simp [mnrA, R43x6.limbs6]
  have hA1 : mnrA y 1 = y 1 + (mnrA y 0 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA2 : mnrA y 2 = y 2 + (mnrA y 1 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA3 : mnrA y 3 = y 3 + (mnrA y 2 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA4 : mnrA y 4 = y 4 + (mnrA y 3 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA5 : mnrA y 5 = y 5 + (mnrA y 4 >>> 43) := by simp [mnrA, R43x6.limbs6]
  have hA5nn : (0 : ℤ) ≤ mnrA y 5 := fA0 5
  have hqlt : mnrQ y = 0 ↔ mnrA y 5 < 2 ^ 40 := by
    simp only [mnrQ, R43x6.shiftRight_eq]; omega
  have fif : R43x6.FitsLong (if mnrQ y = 0 then (19 : ℤ) else 0) := by
    split <;> simp [R43x6.FitsLong]
  have hE0 : mnrE y 0 = mnrA y 0 % (2 : ℤ) ^ 43 - (if mnrQ y = 0 then 19 else 0) := by
    simp [mnrE, R43x6.limbs6]
  have hE0' := hE0.symm
  have hE1 : (mnrE y 0 >>> 43) + mnrA y 1 % (2 : ℤ) ^ 43 = mnrE y 1 := by
    simp [mnrE, R43x6.limbs6]; ring
  have hE2 : (mnrE y 1 >>> 43) + mnrA y 2 % (2 : ℤ) ^ 43 = mnrE y 2 := by
    simp [mnrE, R43x6.limbs6]; ring
  have hE3 : (mnrE y 2 >>> 43) + mnrA y 3 % (2 : ℤ) ^ 43 = mnrE y 3 := by
    simp [mnrE, R43x6.limbs6]; ring
  have hE4 : (mnrE y 3 >>> 43) + mnrA y 4 % (2 : ℤ) ^ 43 = mnrE y 4 := by
    simp [mnrE, R43x6.limbs6]; ring
  have h71 : (mnrE y 4 >>> 43) + mnrA y 5 % (2 : ℤ) ^ 40 = mnr y 5 := by
    simp [mnr, R43x6.limbs6]; ring
  have f72 : R43x6.FitsLong ((mnrE y 4 >>> 43) + mnrA y 5 % (2 : ℤ) ^ 40) := by
    rw [h71]; exact f71
  have hm0 : mnr y 0 = mnrE y 0 % (2 : ℤ) ^ 43 := by simp [mnr, R43x6.limbs6]
  have hm1 : mnr y 1 = mnrE y 1 % (2 : ℤ) ^ 43 := by simp [mnr, R43x6.limbs6]
  have hm2 : mnr y 2 = mnrE y 2 % (2 : ℤ) ^ 43 := by simp [mnr, R43x6.limbs6]
  have hm3 : mnr y 3 = mnrE y 3 % (2 : ℤ) ^ 43 := by simp [mnr, R43x6.limbs6]
  have hm4 : mnr y 4 = mnrE y 4 % (2 : ℤ) ^ 43 := by simp [mnr, R43x6.limbs6]
  have hm0' := hm0.symm
  have hm1' := hm1.symm
  have hm2' := hm2.symm
  have hm3' := hm3.symm
  have hm4' := hm4.symm
  have fm0 : R43x6.FitsLong (mnr y 0) := by rw [hm0]; exact fitsLong_emod _ (by norm_num)
  have fm1 : R43x6.FitsLong (mnr y 1) := by rw [hm1]; exact fitsLong_emod _ (by norm_num)
  have fm2 : R43x6.FitsLong (mnr y 2) := by rw [hm2]; exact fitsLong_emod _ (by norm_num)
  have fm3 : R43x6.FitsLong (mnr y 3) := by rw [hm3]; exact fitsLong_emod _ (by norm_num)
  have fm4 : R43x6.FitsLong (mnr y 4) := by rw [hm4]; exact fitsLong_emod _ (by norm_num)
  have fm5 : R43x6.FitsLong (mnr y 5) := by rw [← h71, add_comm]; simpa using f71
  have hred : ∀ k, reduce l k = mnr y k := by intro k; rw [hyy]; rfl
  have cv0 : (PoisonOr.value 0#64 : LLVM.IntW 64) = val 0 := by decide

  have hA0' := hA0.symm
  have hA1' := hA1.symm
  have hA2' := hA2.symm
  have hA3' := hA3.symm
  have hA4' := hA4.symm
  have hA5' := hA5.symm

  /- The constants and the extracts, as `val`s of the model's integers. -/
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

  /-
  long _y0 = (x##0); … long _y5 = (x##5);
  -/
  denote_step_reduce v 20 [LLVM.const?, LLVM.Ty.extractelement, Ctxt.Valuation.singleton] fold
  -- `simp only`: the plain `simp` of the step normalises `2^40 - 1` to its
  -- numeral, and then no `val`-level lemma below matches
  simp only [cv6, cv7, cv8, cv9, cv10, cv11, cv12, cv13, ev0, ev1, ev2, ev3, ev4, ev5]
    at hv6 hv7 hv8 hv9 hv10 hv11 hv12 hv13 hv15 hv16 hv17 hv18 hv19 hv20

  /-
  _y5 -= _b;
  _c = _y5>>40; _y5 &= _m40; _y0 += 19L*_c;
  -/
  denote_step_reduce v 21 only
    [hv20, hv6, add_ofInt (flags := {nsw := true}) (fl 5) fc6 (ha5 ▸ fa 5) (by simp), ha5']
  denote_step_reduce v 22 only [hv21, hv7, ashr_ofInt (n := 40) (fa 5) (by norm_num)]
  denote_step_reduce v 23 only [hv21, hv8, and_mask_ofInt (k := 40) (by norm_num)]
  denote_step_reduce v 24 only
    [hv22, hv9, mul_ofInt (flags := {nsw := true}) rfl (fitsLong_shiftRight (fa 5) 40) fc9 fmul',
      hmul19]
  denote_step_reduce v 25 only
    [hv24, hv15, add_ofInt (flags := {nsw := true}) fmul (fl 0) (ha0 ▸ fa 0) (by simp), ha0']

  /-
  _c = _y0>>43; _y0 &= _m43; _y1 += _c;
  -/
  denote_step_reduce v 26 only [hv25, hv10, ashr_ofInt (n := 43) (fa 0) (by norm_num)]
  denote_step_reduce v 27 only [hv25, hv11, and_mask_ofInt (k := 43) (by norm_num), hy0']
  denote_step_reduce v 28 only
    [hv26, hv16, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fa 0) 43) (fl 1)
      (ha1 ▸ fa 1) (by simp), ha1']

  /-
  _c = _y1>>43; _y1 &= _m43; _y2 += _c;
  -/
  denote_step_reduce v 29 only [hv28, hv10, ashr_ofInt (n := 43) (fa 1) (by norm_num)]
  denote_step_reduce v 30 only [hv28, hv11, and_mask_ofInt (k := 43) (by norm_num), hy1']
  denote_step_reduce v 31 only
    [hv29, hv17, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fa 1) 43) (fl 2)
      (ha2 ▸ fa 2) (by simp), ha2']

  /-
  _c = _y2>>43; _y2 &= _m43; _y3 += _c;
  -/
  denote_step_reduce v 32 only [hv31, hv10, ashr_ofInt (n := 43) (fa 2) (by norm_num)]
  denote_step_reduce v 33 only [hv31, hv11, and_mask_ofInt (k := 43) (by norm_num), hy2']
  denote_step_reduce v 34 only
    [hv32, hv18, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fa 2) 43) (fl 3)
      (ha3 ▸ fa 3) (by simp), ha3']

  /-
  _c = _y3>>43; _y3 &= _m43; _y4 += _c;
  -/
  denote_step_reduce v 35 only [hv34, hv10, ashr_ofInt (n := 43) (fa 3) (by norm_num)]
  denote_step_reduce v 36 only [hv34, hv11, and_mask_ofInt (k := 43) (by norm_num), hy3']
  denote_step_reduce v 37 only
    [hv35, hv19, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fa 3) 43) (fl 4)
      (ha4 ▸ fa 4) (by simp), ha4']

  /-
  _c = _y4>>43; _y4 &= _m43;   (`_y5 += _c` and `_y5 += _b` are scheduled later)
  -/
  denote_step_reduce v 38 only [hv37, hv10, ashr_ofInt (n := 43) (fa 4) (by norm_num)]
  denote_step_reduce v 39 only [hv37, hv11, and_mask_ofInt (k := 43) (by norm_num), hy4']
  -- the lane indices, the bias and its shift, the limbs and every carry are
  -- spent; what the second macro still reads is the masked limbs and the
  -- shift/mask constants
  denote_clear v 1 7
  denote_clear v 15 22
  denote_clear v 24 26
  denote_clear v 28 29
  denote_clear v 31 32
  denote_clear v 34 35
  denote_clear v 37 37

  /-
  _y0 += 19L;
  _c = _y0>>43; _y0 &= _m43; _y1 += _c;   (`lshr`: the chain is non-negative)
  -/
  denote_step_reduce v 40 only
    [hv27, hv9, add_ofInt (flags := {nsw := true, nuw := true}) fy0 fc9 (hA0 ▸ fA 0)
      (fun _ => ⟨hb0.1, by norm_num⟩), hA0']
  denote_step_reduce v 41 only
    [hv40, hv10, lshr_ofInt (n := 43) (fA 0) (fA0 0) (by norm_num) (by norm_num)]
  denote_step_reduce v 42 only [hv40, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 43 only
    [hv30, hv41, add_ofInt (flags := {nsw := true, nuw := true}) fy1
      (fitsLong_shiftRight (fA 0) 43) (hA1 ▸ fA 1)
      (fun _ => ⟨hb1.1, shiftRight_nonneg (fA0 0) 43⟩), hA1']
  denote_step_reduce v 44 only
    [hv43, hv10, lshr_ofInt (n := 43) (fA 1) (fA0 1) (by norm_num) (by norm_num)]
  denote_step_reduce v 45 only [hv43, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 46 only
    [hv33, hv44, add_ofInt (flags := {nsw := true, nuw := true}) fy2
      (fitsLong_shiftRight (fA 1) 43) (hA2 ▸ fA 2)
      (fun _ => ⟨hb2.1, shiftRight_nonneg (fA0 1) 43⟩), hA2']
  denote_step_reduce v 47 only
    [hv46, hv10, lshr_ofInt (n := 43) (fA 2) (fA0 2) (by norm_num) (by norm_num)]
  denote_step_reduce v 48 only [hv46, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 49 only
    [hv36, hv47, add_ofInt (flags := {nsw := true, nuw := true}) fy3
      (fitsLong_shiftRight (fA 2) 43) (hA3 ▸ fA 3)
      (fun _ => ⟨hb3.1, shiftRight_nonneg (fA0 2) 43⟩), hA3']
  denote_step_reduce v 50 only
    [hv49, hv10, lshr_ofInt (n := 43) (fA 3) (fA0 3) (by norm_num) (by norm_num)]
  denote_step_reduce v 51 only [hv49, hv11, and_mask_ofInt (k := 43) (by norm_num)]
  denote_step_reduce v 52 only
    [hv39, hv50, add_ofInt (flags := {nsw := true, nuw := true}) fy4
      (fitsLong_shiftRight (fA 3) 43) (hA4 ▸ fA 4)
      (fun _ => ⟨hb4.1, shiftRight_nonneg (fA0 3) 43⟩), hA4']
  denote_step_reduce v 53 only
    [hv52, hv10, lshr_ofInt (n := 43) (fA 4) (fA0 4) (by norm_num) (by norm_num)]
  denote_step_reduce v 54 only [hv52, hv11, and_mask_ofInt (k := 43) (by norm_num)]

  /-
  the carry propagate's own `_y5 += _b` and `_y5 += _c`, scheduled here, and
  then `_y5 += 19`'s carry
  -/
  denote_step_reduce v 55 only
    [hv23, hv12, add_ofInt (flags := {nsw := true, nuw := true})
      (fitsLong_emod _ (by norm_num)) fc12 f54
      (fun _ => ⟨Int.emod_nonneg _ (by norm_num), by norm_num⟩)]
  denote_step_reduce v 56 only
    [hv55, hv38, add_ofInt (flags := {nsw := true}) f54 (fitsLong_shiftRight (fa 4) 43)
      (hy5 ▸ f55) (by simp), hy5']
  denote_step_reduce v 57 only
    [hv56, hv53, add_ofInt (flags := {nsw := true, nuw := true}) fy5
      (fitsLong_shiftRight (fA 4) 43) (hA5 ▸ fA 5)
      (fun _ => ⟨by omega, shiftRight_nonneg (fA0 4) 43⟩), hA5']
  denote_step_reduce v 58 only [hv57, hv8, and_mask_ofInt (k := 40) (by norm_num)]
  -- the carry propagate is finished with; the borrow chain reads only the
  -- masked `mnrA` limbs
  denote_clear v 8 9
  denote_clear v 12 12
  denote_clear v 23 41
  denote_clear v 43 44
  denote_clear v 46 47
  denote_clear v 49 50
  denote_clear v 52 53
  denote_clear v 55 56

  /-
  _c = _y5>>40, decided, and `fd_long_if( !_c, 19L, 0L )`: the callee is not
  stepped through again, `denote_fd_long_if` is what it computes
  -/
  denote_step_reduce v 59 only
    [hv57, hv13, icmp_ult_ofInt (b := (2 : ℤ) ^ 40) (fA 5) (by simp [R43x6.FitsLong]) hA5nn
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
    simp [hqlt, BitVec.ofBool, Bool.cond_decide, apply_ite]

  /-
  _y0 -= fd_long_if(…), and the borrow chain from there
  -/
  denote_step_reduce v 62 only
    [hv42, hv61', sub_ofInt (flags := {nsw := true}) rfl (fitsLong_emod _ (by norm_num)) fif
      (hE0 ▸ fE 0), hE0']
  denote_step_reduce v 63 only [hv62, hv10, ashr_ofInt (n := 43) (fE 0) (by norm_num)]
  denote_step_reduce v 64 only
    [hv63, hv45, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fE 0) 43)
      (fitsLong_emod _ (by norm_num)) (hE1 ▸ fE 1) (by simp), hE1]
  denote_step_reduce v 65 only [hv64, hv10, ashr_ofInt (n := 43) (fE 1) (by norm_num)]
  denote_step_reduce v 66 only
    [hv65, hv48, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fE 1) 43)
      (fitsLong_emod _ (by norm_num)) (hE2 ▸ fE 2) (by simp), hE2]
  denote_step_reduce v 67 only [hv66, hv10, ashr_ofInt (n := 43) (fE 2) (by norm_num)]
  denote_step_reduce v 68 only
    [hv67, hv51, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fE 2) 43)
      (fitsLong_emod _ (by norm_num)) (hE3 ▸ fE 3) (by simp), hE3]
  denote_step_reduce v 69 only [hv68, hv10, ashr_ofInt (n := 43) (fE 3) (by norm_num)]
  denote_step_reduce v 70 only
    [hv69, hv54, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fE 3) 43)
      (fitsLong_emod _ (by norm_num)) (hE4 ▸ fE 4) (by simp), hE4]
  denote_step_reduce v 71 only [hv70, hv10, ashr_ofInt (n := 43) (fE 4) (by norm_num)]
  denote_step_reduce v 72 only
    [hv71, hv58, add_ofInt (flags := {nsw := true}) (fitsLong_shiftRight (fE 4) 43)
      (fitsLong_emod (mnrA y 5) (k := 40) (by norm_num)) f72 (by simp), h71]
  -- only the `mnrE` limbs the zero test ORs, and limb 0 for its low bit,
  -- outlive the chain
  clear hv61'
  denote_clear v 10 10
  denote_clear v 13 13
  denote_clear v 42 61

  /-
  !!(l0|l1|l2|l3|l4|l5), with the mask taken across the disjunction
  -/
  denote_step_reduce v 73 only [hv64, hv62, or_ofInt]
  denote_step_reduce v 74 only [hv73, hv66, or_val]
  denote_step_reduce v 75 only [hv74, hv68, or_val]
  denote_step_reduce v 76 only [hv75, hv70, or_val]
  denote_step_reduce v 77 only
    [hv76, hv11, val, LLVM.and, PoisonOr.value_bind, LLVM.and?, BitVec.and_or_distrib_right,
      and_mask_bv _ (show (43 : ℕ) < 64 by norm_num), hm0', hm1', hm2', hm3', hm4']
  denote_step_reduce v 78 only [hv77, hv72, or_val]

  /- The disjunction is zero exactly when every reduced limb is: the bounds are
  what makes a limb-wise test decide the element. Naming it keeps the last four
  instructions readable. -/
  have hzero : (BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0) ||| BitVec.ofInt 64 (mnr y 2)
      ||| BitVec.ofInt 64 (mnr y 3) ||| BitVec.ofInt 64 (mnr y 4) ||| BitVec.ofInt 64 (mnr y 5))
        = BitVec.ofInt 64 0
      ↔ (mnr y 0 = 0 ∧ mnr y 1 = 0 ∧ mnr y 2 = 0 ∧ mnr y 3 = 0 ∧ mnr y 4 = 0 ∧ mnr y 5 = 0) := by
    simp only [show BitVec.ofInt 64 (0 : ℤ) = 0#64 from rfl, BitVec.or_eq_zero_iff,
      ofInt_eq_zero_iff fm0, ofInt_eq_zero_iff fm1, ofInt_eq_zero_iff fm2,
      ofInt_eq_zero_iff fm3, ofInt_eq_zero_iff fm4, ofInt_eq_zero_iff fm5]
    tauto
  obtain ⟨o, ho⟩ : ∃ o : BitVec 64, o = (BitVec.ofInt 64 (mnr y 1) ||| BitVec.ofInt 64 (mnr y 0)
      ||| BitVec.ofInt 64 (mnr y 2) ||| BitVec.ofInt 64 (mnr y 3) ||| BitVec.ofInt 64 (mnr y 4)
      ||| BitVec.ofInt 64 (mnr y 5)) := ⟨_, rfl⟩
  rw [← ho] at hv78 hzero
  denote_clear v 11 11
  denote_clear v 63 77

  /-
  the sign: `x == 0` decided, the low bit of the reduced limb 0, and
  `fd_int_if( !x, l0 & 1, -1 )`
  -/
  simp only [cv0] at hv0
  denote_step_reduce v 79 only [hv78, hv0, icmp_eq_val]
  denote_step_reduce v 80 only [hv79, zext_ofBool]
  denote_step_reduce v 81 only [hv62, trunc_val]
  denote_step_reduce v 82 only [hv81, hv14, and32_value, lowbit_setWidth]
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

  /- The answer: `-1` when the element is zero, its low bit otherwise. `% 2` of
  the reduced limb 0 is `% 2` of the borrow chain's, since `2 ∣ 2^43`. -/
  have hmod : mnr y 0 % 2 = mnrE y 0 % 2 := by
    rw [hm0]; exact Int.emod_emod_of_dvd _ (by norm_num)
  simp only [Com.denote_rets, hv83', diagnose, isNonzero, hred]
  by_cases hz : mnr y 0 = 0 ∧ mnr y 1 = 0 ∧ mnr y 2 = 0 ∧ mnr y 3 = 0 ∧ mnr y 4 = 0
      ∧ mnr y 5 = 0
  · rw [if_pos hz, if_pos (hzero.mpr hz)]
    rfl
  · rw [if_neg hz, if_neg (fun hc => hz (hzero.mp hc)), hmod]
    rfl

end Firedancer.Avx512
