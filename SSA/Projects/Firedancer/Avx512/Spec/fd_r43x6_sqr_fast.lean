import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Denote.fd_r43x6_sqr_fast
import SSA.Projects.Firedancer.Avx512.Spec.Common
import SSA.Projects.Firedancer.MLIR.Poison
import SSA.Projects.Firedancer.Ed25519
import Mathlib.Tactic.IntervalCases

/-!
# `fd_r43x6_sqr_fast` squares its input in `ZMod p`

Denoting the lifted SLLVM program and decoding the six output limbs yields the
square of the decoded input in `GF(2^255 - 19)`.

The proof composes three layers:

* `denote_fd_r43x6_sqr_fast` (`Avx512/Denote/`): the denotation is the lane
  expression `sqrFastResult`;
* `pack_sqLimb_zmod`: ring correctness of the ℕ-level limbs `sqLimb`;
* `sqrFastResult_eq`: each output lane is `BitVec.ofNat 64` of `sqLimb`.

`fd_r43x6_sqr_fast` is *not* `fd_r43x6_mul_fast x x`: doubling of the
off-diagonal partial products happens *before* the multiplications rather than
after. The products formed are therefore `x i * x i` on the diagonal and
`(2 * x i) * x j` for `i < j` — twenty-one, against the thirty-six of a general
multiply.

## Hypotheses

Both are required, and both are the contract stated in `fd_r43x6.h` ("x is an
unreduced fd_r43x6_t (i.e. in u47).  Assumes lanes 6 and 7 of x are zero"):

* `hx : Unreduced x`. At `2^50` limbs the output limbs exceed `2^63` and
  `BitVec.toInt` reads them as negative.
* `h7 : x[7] = 0`. Lane 7 is a don't-care slot of the `wwl_permute` masks, so
  its square reaches output lanes 1-4. On `x = ⟨0,…,0,1⟩` the program returns
  `⟨0,306,0,2,0,0,0,0⟩`, decoding to `306·2^43 + 2·2^129` rather than `0`.

`h6` belongs to that contract but is unused: `x[6]` occurs in no output lane.
-/

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-! ## The ℕ-level specification

Every product formed by the implementation is split by the `vpmadd52lo`/`hi`
pair into `pl`/`ph` (see `Spec/Common.lean`), so that
`pl a b + 2^43·(ph a b) = a·b`. Grouping by scale factor `2^43k` gives twelve
column sums, and the fold uses `2^258 ≡ 152 (mod p)` to produce the six output
limbs

    sqLimb k = sqCol k + 152·sqCol (k+6),   k = 0,…,5.
-/

/-- The column sums of the squaring: `sqCol x k` is the coefficient of
`2^(43k)` before folding, read off the lanes of `sqrFastResult`. For `k < 6`
this is the `za` half of lane `k`, and `sqCol (k+6)` is the `zb` half. -/
def sqCol (x : ℕ → ℕ) : ℕ → ℕ
  | 0 => pl (x 0) (x 0)
  | 1 => pl (2 * x 0) (x 1)
      + ph (x 0) (x 0)
  | 2 => pl (x 1) (x 1) + pl (2 * x 0) (x 2)
      + ph (2 * x 0) (x 1)
  | 3 => pl (2 * x 1) (x 2) + pl (2 * x 0) (x 3)
      + ph (x 1) (x 1) + ph (2 * x 0) (x 2)
  | 4 => pl (2 * x 1) (x 3) + pl (2 * x 0) (x 4) + pl (x 2) (x 2)
      + ph (2 * x 1) (x 2) + ph (2 * x 0) (x 3)
  | 5 => pl (2 * x 1) (x 4) + pl (2 * x 0) (x 5) + pl (2 * x 2) (x 3)
      + ph (2 * x 1) (x 3) + ph (2 * x 0) (x 4) + ph (x 2) (x 2)
  | 6 => pl (2 * x 1) (x 5) + pl (x 3) (x 3) + pl (2 * x 2) (x 4)
      + ph (2 * x 1) (x 4) + ph (2 * x 0) (x 5) + ph (2 * x 2) (x 3)
  | 7 => pl (2 * x 3) (x 4) + pl (2 * x 2) (x 5)
      + ph (2 * x 1) (x 5) + ph (x 3) (x 3) + ph (2 * x 2) (x 4)
  | 8 => pl (2 * x 3) (x 5) + pl (x 4) (x 4)
      + ph (2 * x 3) (x 4) + ph (2 * x 2) (x 5)
  | 9 => pl (2 * x 4) (x 5)
      + ph (2 * x 3) (x 5) + ph (x 4) (x 4)
  | 10 => pl (x 5) (x 5)
      + ph (2 * x 4) (x 5)
  | 11 => ph (x 5) (x 5)
  | _ => 0

/-- The output limbs of `fd_r43x6_sqr_fast`: the low six columns, plus the
high six folded in with weight `152 = 2^258 mod p`. -/
def sqLimb (x : ℕ → ℕ) (k : ℕ) : ℕ :=
  sqCol x k + 152 * sqCol x (k + 6)

/-! ## Ring correctness -/

set_option exponentiation.threshold 600 in
/-- The twelve columns decode to the full square: each of the twenty-one
products appears exactly once, at the weight `2^(43(i+j))` of its column. -/
theorem sqCols_sq (x : ℕ → ℕ) :
    (pack x) ^ 2 =
      sqCol x 0 + 2^43 * sqCol x 1 + 2^86 * sqCol x 2 + 2^129 * sqCol x 3
      + 2^172 * sqCol x 4 + 2^215 * sqCol x 5 + 2^258 * sqCol x 6
      + 2^301 * sqCol x 7 + 2^344 * sqCol x 8 + 2^387 * sqCol x 9
      + 2^430 * sqCol x 10 + 2^473 * sqCol x 11 := by
  simp only [pack, sqCol]
  -- The twenty-one products formed by the implementation.
  have d0 := pl_add_shift_ph (x 0) (x 0)
  have d1 := pl_add_shift_ph (x 1) (x 1)
  have d2 := pl_add_shift_ph (x 2) (x 2)
  have d3 := pl_add_shift_ph (x 3) (x 3)
  have d4 := pl_add_shift_ph (x 4) (x 4)
  have d5 := pl_add_shift_ph (x 5) (x 5)
  have h01 := pl_add_shift_ph (2 * x 0) (x 1)
  have h02 := pl_add_shift_ph (2 * x 0) (x 2)
  have h03 := pl_add_shift_ph (2 * x 0) (x 3)
  have h04 := pl_add_shift_ph (2 * x 0) (x 4)
  have h05 := pl_add_shift_ph (2 * x 0) (x 5)
  have h12 := pl_add_shift_ph (2 * x 1) (x 2)
  have h13 := pl_add_shift_ph (2 * x 1) (x 3)
  have h14 := pl_add_shift_ph (2 * x 1) (x 4)
  have h15 := pl_add_shift_ph (2 * x 1) (x 5)
  have h23 := pl_add_shift_ph (2 * x 2) (x 3)
  have h24 := pl_add_shift_ph (2 * x 2) (x 4)
  have h25 := pl_add_shift_ph (2 * x 2) (x 5)
  have h34 := pl_add_shift_ph (2 * x 3) (x 4)
  have h35 := pl_add_shift_ph (2 * x 3) (x 5)
  have h45 := pl_add_shift_ph (2 * x 4) (x 5)
  calc (x 0 + 2^43 * x 1 + 2^86 * x 2 + 2^129 * x 3 + 2^172 * x 4 + 2^215 * x 5) ^ 2
      = (x 0 * x 0)
        + 2^43 * ((2 * x 0) * x 1)
        + 2^86 * (x 1 * x 1 + (2 * x 0) * x 2)
        + 2^129 * ((2 * x 1) * x 2 + (2 * x 0) * x 3)
        + 2^172 * ((2 * x 1) * x 3 + (2 * x 0) * x 4 + x 2 * x 2)
        + 2^215 * ((2 * x 1) * x 4 + (2 * x 0) * x 5 + (2 * x 2) * x 3)
        + 2^258 * ((2 * x 1) * x 5 + x 3 * x 3 + (2 * x 2) * x 4)
        + 2^301 * ((2 * x 3) * x 4 + (2 * x 2) * x 5)
        + 2^344 * ((2 * x 3) * x 5 + x 4 * x 4)
        + 2^387 * ((2 * x 4) * x 5)
        + 2^430 * (x 5 * x 5) := by ring
    _ = _ := by
        rw [← d0, ← d1, ← d2, ← d3, ← d4, ← d5,
            ← h01, ← h02, ← h03, ← h04, ← h05,
            ← h12, ← h13, ← h14, ← h15,
            ← h23, ← h24, ← h25,
            ← h34, ← h35, ← h45]
        ring

/-- **Ring correctness**: decoding the output limbs of `fd_r43x6_sqr_fast`
yields the square of the decoded input modulo `p = 2^255 - 19`. -/
theorem pack_sqLimb_modEq (x : ℕ → ℕ) :
    pack (sqLimb x) ≡ (pack x) ^ 2 [MOD p] := by
  -- The high columns contribute a multiple of `p`, since `2^258 - 152 = 8·p`.
  have hsplit : pack (sqLimb x)
      + p * (8 * (sqCol x 6 + 2^43 * sqCol x 7 + 2^86 * sqCol x 8
          + 2^129 * sqCol x 9 + 2^172 * sqCol x 10 + 2^215 * sqCol x 11))
      = (pack x) ^ 2 := by
    rw [sqCols_sq]
    simp only [pack, sqLimb, p]
    generalize sqCol x 0 = c0; generalize sqCol x 1 = c1
    generalize sqCol x 2 = c2; generalize sqCol x 3 = c3
    generalize sqCol x 4 = c4; generalize sqCol x 5 = c5
    generalize sqCol x 6 = c6; generalize sqCol x 7 = c7
    generalize sqCol x 8 = c8; generalize sqCol x 9 = c9
    generalize sqCol x 10 = c10; generalize sqCol x 11 = c11
    omega
  show _ % _ = _ % _
  conv_rhs => rw [← hsplit]
  rw [Nat.add_mul_mod_self_left]

/-- Ring correctness, stated in `ZMod p`. -/
theorem pack_sqLimb_zmod (x : ℕ → ℕ) :
    ((pack (sqLimb x) : ℕ) : ZMod p) = ((pack x : ℕ) : ZMod p) ^ 2 := by
  have h := pack_sqLimb_modEq x
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simpa [Nat.cast_pow] using this

/-! ## Bounds

Every `pl` is `< 2^52`. A `ph` bound depends on the input width, since its
operands are `2 * x i` and `x j`. Collecting coefficients from `sqCol`, no
output limb uses more than 457 `pl`s, 456 off-diagonal `ph`s and 153 diagonal
`ph`s — the worst case is limb 0 for the first two and limb 1 for the third.
`sqLimb_lt_of_bounds` is that count; the four rows of the table in
`fd_r43x6.h` (`u44/u45/u46/u47` in, `u61/u61/u62/u62` out) are instances. -/

set_option maxHeartbeats 1000000 in
/-- Every output limb, in terms of an off-diagonal `ph` bound `Bo` and a
diagonal one `Bd`. -/
private theorem sqLimb_lt_of_bounds (x : ℕ → ℕ) (Bo Bd L : ℕ)
    (hph : ∀ i < 6, ∀ j < 6, ph (2 * x i) (x j) < Bo)
    (hphd : ∀ i < 6, ph (x i) (x i) < Bd)
    (hL : 457 * 2^52 + 456 * Bo + 153 * Bd ≤ L)
    (k : ℕ) (hk : k < 6) :
    sqLimb x k < L := by
  have hpl : ∀ a b : ℕ, pl a b < 2^52 := fun a b => pl_lt a b
  interval_cases k <;>
  · simp only [sqLimb, sqCol]
    have := hpl (x 0) (x 0); have := hpl (x 1) (x 1); have := hpl (x 2) (x 2)
    have := hpl (x 3) (x 3); have := hpl (x 4) (x 4); have := hpl (x 5) (x 5)
    have := hpl (2 * x 0) (x 1); have := hpl (2 * x 0) (x 2)
    have := hpl (2 * x 0) (x 3); have := hpl (2 * x 0) (x 4)
    have := hpl (2 * x 0) (x 5); have := hpl (2 * x 1) (x 2)
    have := hpl (2 * x 1) (x 3); have := hpl (2 * x 1) (x 4)
    have := hpl (2 * x 1) (x 5); have := hpl (2 * x 2) (x 3)
    have := hpl (2 * x 2) (x 4); have := hpl (2 * x 2) (x 5)
    have := hpl (2 * x 3) (x 4); have := hpl (2 * x 3) (x 5)
    have := hpl (2 * x 4) (x 5)
    have h0 := hphd 0 (by omega); have h1 := hphd 1 (by omega)
    have h2 := hphd 2 (by omega); have h3 := hphd 3 (by omega)
    have h4 := hphd 4 (by omega); have h5 := hphd 5 (by omega)
    have := hph 0 (by omega) 1 (by omega); have := hph 0 (by omega) 2 (by omega)
    have := hph 0 (by omega) 3 (by omega); have := hph 0 (by omega) 4 (by omega)
    have := hph 0 (by omega) 5 (by omega); have := hph 1 (by omega) 2 (by omega)
    have := hph 1 (by omega) 3 (by omega); have := hph 1 (by omega) 4 (by omega)
    have := hph 1 (by omega) 5 (by omega); have := hph 2 (by omega) 3 (by omega)
    have := hph 2 (by omega) 4 (by omega); have := hph 2 (by omega) 5 (by omega)
    have := hph 3 (by omega) 4 (by omega); have := hph 3 (by omega) 5 (by omega)
    have := hph 4 (by omega) 5 (by omega)
    omega

/-- **`u44` in, `u61` out.** -/
theorem sqLimb_lt_u44 (x : ℕ → ℕ) (hx : ∀ i < 6, x i < 2^44) (k : ℕ) (hk : k < 6) :
    sqLimb x k < 2^61 :=
  sqLimb_lt_of_bounds x (2^37 * 2^9) (2^36 * 2^9) (2^61)
    (fun i hi j hj => ph_lt_bound (u := 2^45) (v := 2^44)
      (by have := hx i hi; omega) (hx j hj) (by omega))
    (fun i hi => ph_lt_bound (u := 2^44) (v := 2^44) (hx i hi) (hx i hi) (by omega))
    (by omega) k hk

/-- **`u45` in, `u61` out.** The tightest of the four: the bound comes to
`15689 · 2^47` against `2^61 = 16384 · 2^47`. -/
theorem sqLimb_lt_u45 (x : ℕ → ℕ) (hx : ∀ i < 6, x i < 2^45) (k : ℕ) (hk : k < 6) :
    sqLimb x k < 2^61 :=
  sqLimb_lt_of_bounds x (2^39 * 2^9) (2^38 * 2^9) (2^61)
    (fun i hi j hj => ph_lt_bound (u := 2^46) (v := 2^45)
      (by have := hx i hi; omega) (hx j hj) (by omega))
    (fun i hi => ph_lt_bound (u := 2^45) (v := 2^45) (hx i hi) (hx i hi) (by omega))
    (by omega) k hk

/-- **`u46` in, `u62` out.** -/
theorem sqLimb_lt_u46 (x : ℕ → ℕ) (hx : ∀ i < 6, x i < 2^46) (k : ℕ) (hk : k < 6) :
    sqLimb x k < 2^62 :=
  sqLimb_lt_of_bounds x (2^41 * 2^9) (2^40 * 2^9) (2^62)
    (fun i hi j hj => ph_lt_bound (u := 2^47) (v := 2^46)
      (by have := hx i hi; omega) (hx j hj) (by omega))
    (fun i hi => ph_lt_bound (u := 2^46) (v := 2^46) (hx i hi) (hx i hi) (by omega))
    (by omega) k hk

/-- **`u47` in, `u62` out.** -/
theorem sqLimb_lt_u47 (x : ℕ → ℕ) (hx : ∀ i < 6, x i < 2^47) (k : ℕ) (hk : k < 6) :
    sqLimb x k < 2^62 :=
  sqLimb_lt_of_bounds x (2^43 * 2^9) (2^42 * 2^9) (2^62)
    (fun i hi j hj => ph_lt_bound (u := 2^48) (v := 2^47)
      (by have := hx i hi; omega) (hx j hj) (by omega))
    (fun i hi => ph_lt_bound (u := 2^47) (v := 2^47) (hx i hi) (hx i hi) (by omega))
    (by omega) k hk

/-- The bound the `BitVec.toInt` transfer needs: below `2^63`, a lane is not
read back as negative. -/
theorem sqLimb_lt_two_pow_63 (x : ℕ → ℕ) (hx : ∀ i < 6, x i < 2^47)
    (k : ℕ) (hk : k < 6) :
    sqLimb x k < 2^63 := by
  have := sqLimb_lt_u47 x hx k hk
  omega

/-! ## The lanes -/

/-- The result vector predicted by the ℕ-level specification. -/
def sqrVec (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  limbVec (sqLimb (limbNat x))

set_option maxHeartbeats 4000000 in
/-- **Lane derivation**: on an unreduced input with lane 7 zero, every output
lane of `fd_r43x6_sqr_fast` is the corresponding ℕ-level limb reduced mod
`2^64`. The reduction is the identity, by `sqLimb_lt_two_pow_63`. -/
theorem sqrFastResult_eq (x : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x) (h7 : x[7] = 0) :
    sqrFastResult x = (sqrVec x).map PoisonOr.value := by
  have b0 : x[0].toNat < 2^47 := unn_toNat x 47 (by omega) hx 0 (by omega)
  have b1 : x[1].toNat < 2^47 := unn_toNat x 47 (by omega) hx 1 (by omega)
  have b2 : x[2].toNat < 2^47 := unn_toNat x 47 (by omega) hx 2 (by omega)
  have b3 : x[3].toNat < 2^47 := unn_toNat x 47 (by omega) hx 3 (by omega)
  have b4 : x[4].toNat < 2^47 := unn_toNat x 47 (by omega) hx 4 (by omega)
  have b5 : x[5].toNat < 2^47 := unn_toNat x 47 (by omega) hx 5 (by omega)
  have b7 : x[7].toNat = 0 := by rw [h7]; rfl
  have b7' : x[7].toNat < 2^47 := by omega
  have s0 : 2 * x[0].toNat < 2^52 := by omega
  have s1 : 2 * x[1].toNat < 2^52 := by omega
  have s2 : 2 * x[2].toNat < 2^52 := by omega
  have s3 : 2 * x[3].toNat < 2^52 := by omega
  have s4 : 2 * x[4].toNat < 2^52 := by omega
  have s7 : 2 * x[7].toNat < 2^52 := by omega
  have t0 : x[0].toNat < 2^52 := by omega
  have t1 : x[1].toNat < 2^52 := by omega
  have t2 : x[2].toNat < 2^52 := by omega
  have t3 : x[3].toNat < 2^52 := by omega
  have t4 : x[4].toNat < 2^52 := by omega
  have t5 : x[5].toNat < 2^52 := by omega
  have t7 : x[7].toNat < 2^52 := by omega
  apply Vector.ext
  intro i hi
  -- Lanes 6 and 7 are identically zero and close on the first `simp only`, so
  -- the later steps are `try`ed and the six real lanes share one script.
  interval_cases i <;>
    · simp only [sqrFastResult, sqrVec, limbVec, Vector.getElem_map, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      try congr 1
      try simp only [lo_eq, hi_eq, s0, s1, s2, s3, s4, s7, t0, t1, t2, t3, t4, t5, t7,
        toNat_shl1, b0, b1, b2, b3, b4, b7',
        natCast_bv, bv_zero, ← BitVec.ofNat_add, ofNat_mul24, ofNat_shl7]
      try congr 1
      try simp only [sqLimb, sqCol, limbNat, b7, Nat.mul_zero, pl_zero_right, ph_zero_right]
      try ring

abbrev sqrValue (x: Vector (BitVec 64) 8) := (fd_r43x6_sqr_fast.denote
          (Ctxt.Valuation.singleton (x.map PoisonOr.value))).head.getValues

abbrev sqrIsSqr (x: Vector (BitVec 64) 8) := (fun l => (R43x6.decode' l : ZMod p)) <$> sqrValue x
      = .value ((R43x6.decode' x : ZMod p)^2)

private def output_bounds_u44_u61 (x: Vector (BitVec 64) 8) := R43x6.U44 x → R43x6.U61 (sqrValue x).getValue
private def output_bounds_u45_u61 (x: Vector (BitVec 64) 8) := R43x6.U45 x → R43x6.U61 (sqrValue x).getValue
private def output_bounds_u46_u62 (x: Vector (BitVec 64) 8) := R43x6.U46 x → R43x6.U62 (sqrValue x).getValue
private def output_bounds_u47_u62 (x: Vector (BitVec 64) 8) := R43x6.U47 x → R43x6.U62 (sqrValue x).getValue

set_option maxHeartbeats 1000000 in
private theorem sqrIsSqrThm (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h6 : x[6] = 0) (h7 : x[7] = 0) :
    sqrIsSqr x := by
  have b0 : x[0].toNat < 2^47 := unn_toNat x 47 (by omega) hx 0 (by omega)
  have b1 : x[1].toNat < 2^47 := unn_toNat x 47 (by omega) hx 1 (by omega)
  have b2 : x[2].toNat < 2^47 := unn_toNat x 47 (by omega) hx 2 (by omega)
  have b3 : x[3].toNat < 2^47 := unn_toNat x 47 (by omega) hx 3 (by omega)
  have b4 : x[4].toNat < 2^47 := unn_toNat x 47 (by omega) hx 4 (by omega)
  have b5 : x[5].toNat < 2^47 := unn_toNat x 47 (by omega) hx 5 (by omega)
  have hbnd : ∀ i < 6, limbNat x i < 2^47 := by
    intro i hi
    interval_cases i <;> simpa [limbNat] using ‹_›
  -- 1. denotation to lanes to specified limbs; the poison layer collapses
  rw [sqrIsSqr, sqrValue, denote_fd_r43x6_sqr_fast, sqrFastResult_eq x hx h7]
  simp only [HVector.head, Vector.getValues_map_value, PoisonOr.map_value,
    PoisonOr.value_inj]
  -- 2. decode both sides into explicit sums
  have hx8 : x = #v[x[0],x[1],x[2],x[3],x[4],x[5],x[6],x[7]] := by
    apply Vector.ext; intro i hi; interval_cases i <;> rfl
  have hdx : R43x6.decode' x = (limbNat x 0 : Int) + 2^43 * limbNat x 1
      + 2^86 * limbNat x 2 + 2^129 * limbNat x 3 + 2^172 * limbNat x 4
      + 2^215 * limbNat x 5 := by
    conv_lhs => rw [hx8]
    rw [decode'_lit, toInt_of_lt b0, toInt_of_lt b1, toInt_of_lt b2,
      toInt_of_lt b3, toInt_of_lt b4, toInt_of_lt b5]
    simp [limbNat]
  rw [sqrVec, decode'_limbVec _ (sqLimb_lt_two_pow_63 _ hbnd), hdx,
    show ((limbNat x 0 : Int) + 2^43 * limbNat x 1 + 2^86 * limbNat x 2
        + 2^129 * limbNat x 3 + 2^172 * limbNat x 4 + 2^215 * limbNat x 5)
      = ((pack (limbNat x) : ℕ) : Int) from by simp [pack]; try ring]
  -- 3. both sides are now casts of `pack`, so `pack_sqLimb_zmod` applies
  push_cast
  exact pack_sqLimb_zmod (limbNat x)

/-! ## Output bounds

The four rows of the `fd_r43x6.h` table, each `sqLimb_lt_u4x` transported
through `sqrFastResult_eq`: output lane `k < 6` is the specified limb, lanes 6
and 7 are zero, and none is read back as negative. -/

/-- The program's result, with the poison layer discharged. -/
private theorem sqrValue_eq (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) :
    sqrValue x = .value (sqrVec x) := by
  rw [sqrValue, denote_fd_r43x6_sqr_fast, sqrFastResult_eq x hx h7]
  simp only [HVector.head, Vector.getValues_map_value]

/-- Two-sided lane bounds from a ceiling `N` on the ℕ-level limbs. -/
private theorem output_bounds_of (x : Vector (BitVec 64) 8) (N : ℕ) (hN : N ≤ 2^62)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0)
    (hb : ∀ k < 6, sqLimb (limbNat x) k < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (sqrValue x).getValue
      ∧ R43x6.BoundedLower 0 (sqrValue x).getValue := by
  have hv : (sqrValue x).getValue = sqrVec x := by rw [sqrValue_eq x hx h7]; rfl
  rw [hv, sqrVec]
  exact limbVec_bounds _ N (by omega) hb

private theorem output_u44 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u44_u61 x := by
  intro hin
  have hb : ∀ k < 6, sqLimb (limbNat x) k < 2^61 := fun k hk =>
    sqLimb_lt_u44 _ (fun i hi => by
      interval_cases i <;> exact unn_toNat x 44 (by omega) hin _ (by omega)) k hk
  exact_mod_cast output_bounds_of x (2^61) (by omega) hx h7 hb

private theorem output_u45 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u45_u61 x := by
  intro hin
  have hb : ∀ k < 6, sqLimb (limbNat x) k < 2^61 := fun k hk =>
    sqLimb_lt_u45 _ (fun i hi => by
      interval_cases i <;> exact unn_toNat x 45 (by omega) hin _ (by omega)) k hk
  exact_mod_cast output_bounds_of x (2^61) (by omega) hx h7 hb

private theorem output_u46 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u46_u62 x := by
  intro hin
  have hb : ∀ k < 6, sqLimb (limbNat x) k < 2^62 := fun k hk =>
    sqLimb_lt_u46 _ (fun i hi => by
      interval_cases i <;> exact unn_toNat x 46 (by omega) hin _ (by omega)) k hk
  exact_mod_cast output_bounds_of x (2^62) (by omega) hx h7 hb

private theorem output_u47 (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h7 : x[7] = 0) : output_bounds_u47_u62 x := by
  intro hin
  have hb : ∀ k < 6, sqLimb (limbNat x) k < 2^62 := fun k hk =>
    sqLimb_lt_u47 _ (fun i hi => by
      interval_cases i <;> exact unn_toNat x 47 (by omega) hin _ (by omega)) k hk
  exact_mod_cast output_bounds_of x (2^62) (by omega) hx h7 hb

/-- **Specification of `fd_r43x6_sqr_fast`**: on an unreduced input whose two
high lanes are zero, the six output limbs decode to the square of the decoded
input in `GF(2^255 - 19)`, and the four input/output width guarantees of
`fd_r43x6.h` hold. -/
theorem spec_fd_r43x6_sqr_fast (x : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (h6 : x[6] = 0) (h7 : x[7] = 0) :
    sqrIsSqr x ∧ output_bounds_u44_u61 x ∧ output_bounds_u45_u61 x
      ∧ output_bounds_u46_u62 x ∧ output_bounds_u47_u62 x :=
  ⟨sqrIsSqrThm x hx h6 h7, output_u44 x hx h7, output_u45 x hx h7,
    output_u46 x hx h7, output_u47 x hx h7⟩

end Firedancer.Avx512
