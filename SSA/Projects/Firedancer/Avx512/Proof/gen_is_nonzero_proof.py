#!/usr/bin/env python3
"""Emit the denotation derivation of `fd_r43x6_is_nonzero`.

The middle of the proof -- the two carry chains, `%20`-`%57` -- is eighty
near-identical steps: one rewrite with the `Proof/Long.lean` lemma for the
opcode, the `R43x6.FitsLong` facts for its operands, and the model equation
naming the result. This writes them out. The preamble (the facts the two macro
proofs supply) and the tail (the conditional subtract, the borrow chain and the
final zero test) are literals below, since neither repeats.

Run from the repository root:

    python3 SSA/Projects/Firedancer/Avx512/Proof/gen_is_nonzero_proof.py

It prints the `denote_fd_r43x6_is_nonzero` of `Proof/fd_r43x6_is_nonzero.lean`.
"""

HEAD = r'''set_option maxHeartbeats 4000000 in
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
'''

TAIL = r'''
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
'''

out = []
def e(s=""): e_(s)
def e_(s): out.append(s)

A = "bcpA (2^20) l"

def step(i, name, value, tac, comment=None):
    """One instruction: `let` its value under the macro's name for it, name the
    stepped variable, and `subst` the two together. The valuation spine then
    holds the `let`, so the terms stay shared."""
    if comment:
        e(f"  -- {comment}")
    e(f"  let {name} := {value}")
    e(f"  have v{i}Value : v{i} = {name} := by")
    for line in tac:
        e(f"    {line}")
    e(f"  subst v{i}Value")

# ---- the constants ---------------------------------------------------
consts = {0:"0", 1:"1", 2:"2", 3:"3", 4:"4", 5:"5",
          6:"(-(2^20))", 7:"((40:ℕ) : ℤ)", 8:"(2^40 - 1)", 9:"19",
          10:"((43:ℕ) : ℤ)", 11:"(2^43 - 1)", 12:"(2^20)", 13:"(2^40)"}
e("  denote_step_all v 13")
for i, c in consts.items():
    tac = [f"long_op hv{i}"] + ([] if i not in (6, 7, 8, 10, 11, 12, 13) else ["norm_num"])
    e(f"  have v{i}Value : v{i} = val {c} := by")
    for line in tac:
        e(f"    {line}")
    e(f"  subst v{i}Value")
e("  denote_clear v 0 13")
# ---- fd_r43x6_extract_limbs ------------------------------------------
e("  denote_step_all v 19")
e("  -- `fd_r43x6_extract_limbs( x, l )`")
for k in range(6):
    step(14 + k, f"l{k}", f"val (l {k})",
         [f"long_op hv{14+k}",
          "simp [hl, val, LLVM.Ty.extractelement, Ctxt.Valuation.singleton,",
          "  R43x6.extractLimbs, LimbRepresentations.toInts]"])
e("  denote_clear v 14 19")
# ---- fd_r43x6_biased_carry_propagate_limbs ---------------------------
e("  denote_step_all v 38")
step(20, "y5", f"val ({A} 5)",
     ["long_op hv20",
      "rw [add_ofInt (fl 5) fc6 (ha5 ▸ fa 5) (by simp), ha5]"],
     "`_y5 -= _b`, and the carry chain from there")
step(21, "c5", f"val ({A} 5 >>> 40)",
     ["long_op hv21; rw [ashr_ofInt (fa 5) (by norm_num)]"])
step(22, "y5m", f"val ({A} 5 % 2^40)",
     ["long_op hv22; rw [and_mask_ofInt (k := 40) (by norm_num)]"])
step(23, "c5x19", f"val ((19:ℤ) * ({A} 5 >>> 40))",
     ["long_op hv23",
      "rw [mul_ofInt rfl (fitsLong_shiftRight (fa 5) 40) fc9 fmul', mul_comm]"])
for k in range(5):
    add, shr, msk = 24 + 3*k, 25 + 3*k, 26 + 3*k
    srcfits = "fmul" if k == 0 else f"(fitsLong_shiftRight (fa {k-1}) 43)"
    step(add, f"y{k}", f"val ({A} {k})",
         [f"long_op hv{add}",
          f"rw [add_ofInt {srcfits} (fl {k}) (ha{k} ▸ fa {k}) (by simp), ha{k}]"])
    step(shr, f"c{k}", f"val ({A} {k} >>> 43)",
         [f"long_op hv{shr}; rw [ashr_ofInt (fa {k}) (by norm_num)]"])
    step(msk, f"l{k}'", f"val (y {k})",
         [f"long_op hv{msk}",
          f"rw [and_mask_ofInt (k := 43) (by norm_num), ← hy{k}]"])
e("  denote_clear v 20 38")
# ---- fd_r43x6_mod_nearly_reduced_limbs, `y = x + 19` -----------------
e("  denote_step_all v 57")
for k in range(5):
    add, shr, msk = 39 + 3*k, 40 + 3*k, 41 + 3*k
    if k == 0:
        nn, fits2 = "(fun _ => ⟨hb0.1, by norm_num⟩)", "fc9"
        comment = "`_y0 += 19L`, and the carry chain from there"
    else:
        nn = f"(fun _ => ⟨hb{k}.1, shiftRight_nonneg (fA0 {k-1}) 43⟩)"
        fits2 = f"(fitsLong_shiftRight (fA {k-1}) 43)"
        comment = None
    step(add, f"y{k}'", f"val (mnrA y {k})",
         [f"long_op hv{add}",
          f"rw [add_ofInt fy{k} {fits2} (hA{k} ▸ fA {k}) {nn}, hA{k}]"], comment)
    step(shr, f"c{k}'", f"val (mnrA y {k} >>> 43)",
         [f"long_op hv{shr}",
          f"rw [lshr_ofInt (fA {k}) (fA0 {k}) (by norm_num) (by norm_num)]"])
    step(msk, f"y{k}m'", f"val (mnrA y {k} % 2^43)",
         [f"long_op hv{msk}; rw [and_mask_ofInt (k := 43) (by norm_num)]"])
step(54, "y5b", f"val ({A} 5 % 2^40 + 2^20)",
     ["long_op hv54",
      "rw [add_ofInt (fitsLong_emod _ (by norm_num)) fc12 f54",
      "  (fun _ => ⟨Int.emod_nonneg _ (by norm_num), by norm_num⟩)]"],
     "the carry propagate's `_y5 += _b` and `_y5 += _c`, scheduled here")
step(55, "l5'", "val (y 5)",
     ["long_op hv55",
      "rw [add_ofInt f54 (fitsLong_shiftRight (fa 4) 43) (hy5 ▸ f55) (by simp), ← hy5]"])
step(56, "y5'", "val (mnrA y 5)",
     ["long_op hv56",
      "rw [add_ofInt fy5 (fitsLong_shiftRight (fA 4) 43) (hA5 ▸ fA 5)",
      "  (fun _ => ⟨by omega, shiftRight_nonneg (fA0 4) 43⟩), hA5]"])
step(57, "y5m'", "val (mnrA y 5 % 2^40)",
     ["long_op hv57; rw [and_mask_ofInt (k := 40) (by norm_num)]"])
e("  denote_clear v 39 57")
e("  denote_step_all v 71")
print(HEAD + "\n".join(out) + TAIL)
