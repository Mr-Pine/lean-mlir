import SSA.Projects.Firedancer.Avx512.Spec.Common
import SSA.Projects.Firedancer.MLIR.Poison
import SSA.Projects.Firedancer.Ed25519
import Mathlib.Tactic.IntervalCases

/-!
# What `fd_r43x6_sqr_fast` is specified to compute

The ℕ-level model of the squaring, and its two properties: decoding the
output limbs gives the square in `GF(2^255 - 19)` (`decodeLimbs_sqLimb_zmod`), and
each limb stays under the width the `fd_r43x6.h` table promises
(`sqLimb_lt_u4x`).

Nothing here mentions the program: `Avx512/Proof/fd_r43x6_sqr_fast.lean`
derives the denotation *into* `sqrVec` and combines it with these two.

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
def sqCol (x : Fin 6 → ℕ) : Fin 12 → ℕ
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

/-- The output limbs of `fd_r43x6_sqr_fast`: the low six columns, plus the
high six folded in with weight `152 = 2^258 mod p`. -/
def sqLimb (x : Fin 6 → ℕ) (k : Fin 6) : ℕ :=
  sqCol x (k.castAdd 6) + 152 * sqCol x (k.addNat 6)

/-! ## Ring correctness -/

set_option exponentiation.threshold 600 in
/-- The twelve columns decode to the full square: each of the twenty-one
products appears exactly once, at the weight `2^(43(i+j))` of its column. -/
theorem sqCols_sq (x : Fin 6 → ℕ) :
    (decodeNat x) ^ 2 =
      sqCol x 0 + 2^43 * sqCol x 1 + 2^86 * sqCol x 2 + 2^129 * sqCol x 3
      + 2^172 * sqCol x 4 + 2^215 * sqCol x 5 + 2^258 * sqCol x 6
      + 2^301 * sqCol x 7 + 2^344 * sqCol x 8 + 2^387 * sqCol x 9
      + 2^430 * sqCol x 10 + 2^473 * sqCol x 11 := by
  simp only [decodeNat_eq, sqCol]
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
theorem decodeLimbs_sqLimb_modEq (x : Fin 6 → ℕ) :
    decodeNat (sqLimb x) ≡ (decodeNat x) ^ 2 [MOD p] := by
  -- The high columns contribute a multiple of `p`, since `2^258 - 152 = 8·p`.
  have hsplit : decodeNat (sqLimb x)
      + p * (8 * (sqCol x 6 + 2^43 * sqCol x 7 + 2^86 * sqCol x 8
          + 2^129 * sqCol x 9 + 2^172 * sqCol x 10 + 2^215 * sqCol x 11))
      = (decodeNat x) ^ 2 := by
    rw [sqCols_sq]
    simp only [decodeNat_eq, sqLimb, p, Fin.reduceAddNat, Fin.reduceCastAdd]
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
theorem decodeLimbs_sqLimb_zmod (x : Fin 6 → ℕ) :
    ((decodeNat (sqLimb x) : ℕ) : ZMod p) = ((decodeNat x : ℕ) : ZMod p) ^ 2 := by
  have h := decodeLimbs_sqLimb_modEq x
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
private theorem sqLimb_lt_of_bounds (x : Fin 6 → ℕ) (Bo Bd L : ℕ)
    (hph : ∀ i j, ph (2 * x i) (x j) < Bo)
    (hphd : ∀ i, ph (x i) (x i) < Bd)
    (hL : 457 * 2^52 + 456 * Bo + 153 * Bd ≤ L)
    (k : Fin 6) :
    sqLimb x k < L := by
  have hpl : ∀ a b : ℕ, pl a b < 2^52 := fun a b => pl_lt a b
  fin_cases k <;>
  · simp [sqLimb, sqCol]
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
    have h0 := hphd 0; have h1 := hphd 1
    have h2 := hphd 2; have h3 := hphd 3
    have h4 := hphd 4; have h5 := hphd 5
    have := hph 0 1; have := hph 0 2
    have := hph 0 3; have := hph 0 4
    have := hph 0 5; have := hph 1 2
    have := hph 1 3; have := hph 1 4
    have := hph 1 5; have := hph 2 3
    have := hph 2 4; have := hph 2 5
    have := hph 3 4; have := hph 3 5
    have := hph 4 5
    omega

/-- **`u44` in, `u61` out.** -/
theorem sqLimb_lt_u44 (x : Fin 6 → ℕ) (hx : ∀ i, x i < 2^44) (k : Fin 6) :
    sqLimb x k < 2^61 :=
  sqLimb_lt_of_bounds x (2^37 * 2^9) (2^36 * 2^9) (2^61)
    (fun i j => ph_lt_bound (u := 2^45) (v := 2^44)
      (by have := hx i; omega) (hx j) (by omega))
    (fun i => ph_lt_bound (u := 2^44) (v := 2^44) (hx i) (hx i) (by omega))
    (by omega) k

/-- **`u45` in, `u61` out.** The tightest of the four: the bound comes to
`15689 · 2^47` against `2^61 = 16384 · 2^47`. -/
theorem sqLimb_lt_u45 (x : Fin 6 → ℕ) (hx : ∀ i, x i < 2^45) (k : Fin 6) :
    sqLimb x k < 2^61 :=
  sqLimb_lt_of_bounds x (2^39 * 2^9) (2^38 * 2^9) (2^61)
    (fun i j => ph_lt_bound (u := 2^46) (v := 2^45)
      (by have := hx i; omega) (hx j) (by omega))
    (fun i => ph_lt_bound (u := 2^45) (v := 2^45) (hx i) (hx i) (by omega))
    (by omega) k

/-- **`u46` in, `u62` out.** -/
theorem sqLimb_lt_u46 (x : Fin 6 → ℕ) (hx : ∀ i, x i < 2^46) (k : Fin 6) :
    sqLimb x k < 2^62 :=
  sqLimb_lt_of_bounds x (2^41 * 2^9) (2^40 * 2^9) (2^62)
    (fun i j => ph_lt_bound (u := 2^47) (v := 2^46)
      (by have := hx i; omega) (hx j) (by omega))
    (fun i => ph_lt_bound (u := 2^46) (v := 2^46) (hx i) (hx i) (by omega))
    (by omega) k

/-- **`u47` in, `u62` out.** -/
theorem sqLimb_lt_u47 (x : Fin 6 → ℕ) (hx : ∀ i, x i < 2^47) (k : Fin 6) :
    sqLimb x k < 2^62 :=
  sqLimb_lt_of_bounds x (2^43 * 2^9) (2^42 * 2^9) (2^62)
    (fun i j => ph_lt_bound (u := 2^48) (v := 2^47)
      (by have := hx i; omega) (hx j) (by omega))
    (fun i => ph_lt_bound (u := 2^47) (v := 2^47) (hx i) (hx i) (by omega))
    (by omega) k

/-- The bound the `BitVec.toInt` transfer needs: below `2^63`, a lane is not
read back as negative. -/
theorem sqLimb_lt_two_pow_63 (x : Fin 6 → ℕ) (hx : ∀ i, x i < 2^47)
    (k : Fin 6) :
    sqLimb x k < 2^63 := by
  have := sqLimb_lt_u47 x hx k
  omega

/-! ## The lanes -/

/-- The result vector predicted by the ℕ-level specification. -/
def sqrVec (x : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  limbVec (sqLimb (limbNat x))

end Firedancer.Avx512
