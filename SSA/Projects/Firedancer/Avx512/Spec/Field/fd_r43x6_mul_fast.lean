import SSA.Projects.Firedancer.Avx512.Spec.Common
import SSA.Projects.Firedancer.Ed25519
import Mathlib.Tactic.IntervalCases

/-!
# What `fd_r43x6_mul_fast` is specified to compute

The ℕ-level model of the multiplication, and its two properties: decoding the
output limbs gives the product in `GF(2^255 - 19)` (`decodeLimbs_limb_zmod`), and
each limb stays under the width the `fd_r43x6.h` table promises
(`limb_lt_u4x`).

Nothing here mentions the program: `Avx512/Proof/fd_r43x6_mul_fast.lean`
derives the denotation *into* `mulVec` and combines it with these two.

## Hypotheses

All are the contract stated in `fd_r43x6.h` ("x and y are unreduced
fd_r43x6_t's (i.e. in u47).  Ignores lanes 6 and 7 of x and assumes lanes 6
and 7 of y are zero"):

* `hx : Unreduced x`, `hy : Unreduced y`. At `2^50` limbs the output limbs
  exceed `2^63` and `BitVec.toInt` reads them as negative.
* `hy6 : y[6] = 0`, `hy7 : y[7] = 0`. The `t` accumulators multiply the
  broadcast `x` limbs against *all* lanes of `y`, and the slides move the
  lane-6/7 products into output lanes 0-4.

Lanes 6 and 7 of `x` need no hypothesis beyond `hx`: the `wwl_permute` masks
select only lanes 0-5 of `x`.
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

    limb k = col k + 152·col (k+6),   k = 0,…,5.
-/

/-- The column sums of the grade-school multiplication: `col x y k` collects
every `pl i j` with `i+j = k` and every `ph i j` with `i+j+1 = k`, i.e. the
coefficient of `2^43k` before any folding. This is the `z0`,…,`z11` diagram in
the comments of `fd_r43x6_mul_fast`. -/
def col (x y : Fin 6 → ℕ) : Fin 12 → ℕ
  | 0 => pl (x 0) (y 0)
  | 1 => pl (x 0) (y 1) + pl (x 1) (y 0) + ph (x 0) (y 0)
  | 2 => pl (x 0) (y 2) + pl (x 1) (y 1) + pl (x 2) (y 0) + ph (x 0) (y 1) + ph (x 1) (y 0)
  | 3 =>
    pl (x 0) (y 3) + pl (x 1) (y 2) + pl (x 2) (y 1) + pl (x 3) (y 0) + ph (x 0) (y 2) +
      ph (x 1) (y 1) +
      ph (x 2) (y 0)
  | 4 =>
    pl (x 0) (y 4) + pl (x 1) (y 3) + pl (x 2) (y 2) + pl (x 3) (y 1) + pl (x 4) (y 0) +
      ph (x 0) (y 3) +
      ph (x 1) (y 2) +
      ph (x 2) (y 1) +
      ph (x 3) (y 0)
  | 5 =>
    pl (x 0) (y 5) + pl (x 1) (y 4) + pl (x 2) (y 3) + pl (x 3) (y 2) + pl (x 4) (y 1) +
      pl (x 5) (y 0) +
      ph (x 0) (y 4) +
      ph (x 1) (y 3) +
      ph (x 2) (y 2) +
      ph (x 3) (y 1) +
      ph (x 4) (y 0)
  | 6 =>
    pl (x 1) (y 5) + pl (x 2) (y 4) + pl (x 3) (y 3) + pl (x 4) (y 2) + pl (x 5) (y 1) +
      ph (x 0) (y 5) +
      ph (x 1) (y 4) +
      ph (x 2) (y 3) +
      ph (x 3) (y 2) +
      ph (x 4) (y 1) +
      ph (x 5) (y 0)
  | 7 =>
    pl (x 2) (y 5) + pl (x 3) (y 4) + pl (x 4) (y 3) + pl (x 5) (y 2) + ph (x 1) (y 5) +
      ph (x 2) (y 4) +
      ph (x 3) (y 3) +
      ph (x 4) (y 2) +
      ph (x 5) (y 1)
  | 8 =>
    pl (x 3) (y 5) + pl (x 4) (y 4) + pl (x 5) (y 3) + ph (x 2) (y 5) + ph (x 3) (y 4) +
      ph (x 4) (y 3) +
      ph (x 5) (y 2)
  | 9 => pl (x 4) (y 5) + pl (x 5) (y 4) + ph (x 3) (y 5) + ph (x 4) (y 4) + ph (x 5) (y 3)
  | 10 => pl (x 5) (y 5) + ph (x 4) (y 5) + ph (x 5) (y 4)
  | 11 => ph (x 5) (y 5)

/-- The output limbs of `fd_r43x6_mul_fast`: the low six columns, plus the
high six folded in with weight `152 = 2^258 mod p`. -/
def limb (x y : Fin 6 → ℕ) (k : Fin 6) : ℕ :=
  col x y (k.castAdd 6) + 152 * col x y (k.addNat 6)

/-! ## Ring correctness -/

set_option exponentiation.threshold 600 in
/-- The twelve columns decode to the full product: each of the thirty-six
products appears exactly once, at the weight `2^(43(i+j))` of its column. -/
theorem cols_mul (x y : Fin 6 → ℕ) :
    (decodeNat x) * (decodeNat y) =
      col x y 0 + 2 ^ 43 * col x y 1 + 2 ^ 86 * col x y 2 + 2 ^ 129 * col x y 3 +
        2 ^ 172 * col x y 4 +
        2 ^ 215 * col x y 5 +
        2 ^ 258 * col x y 6 +
        2 ^ 301 * col x y 7 +
        2 ^ 344 * col x y 8 +
        2 ^ 387 * col x y 9 +
        2 ^ 430 * col x y 10 +
        2 ^ 473 * col x y 11 := by
  simp only [decodeNat_eq, col]
  -- The thirty-six products formed by the implementation.
  have h00 := pl_add_shift_ph (x 0) (y 0)
  have h01 := pl_add_shift_ph (x 0) (y 1)
  have h02 := pl_add_shift_ph (x 0) (y 2)
  have h03 := pl_add_shift_ph (x 0) (y 3)
  have h04 := pl_add_shift_ph (x 0) (y 4)
  have h05 := pl_add_shift_ph (x 0) (y 5)
  have h10 := pl_add_shift_ph (x 1) (y 0)
  have h11 := pl_add_shift_ph (x 1) (y 1)
  have h12 := pl_add_shift_ph (x 1) (y 2)
  have h13 := pl_add_shift_ph (x 1) (y 3)
  have h14 := pl_add_shift_ph (x 1) (y 4)
  have h15 := pl_add_shift_ph (x 1) (y 5)
  have h20 := pl_add_shift_ph (x 2) (y 0)
  have h21 := pl_add_shift_ph (x 2) (y 1)
  have h22 := pl_add_shift_ph (x 2) (y 2)
  have h23 := pl_add_shift_ph (x 2) (y 3)
  have h24 := pl_add_shift_ph (x 2) (y 4)
  have h25 := pl_add_shift_ph (x 2) (y 5)
  have h30 := pl_add_shift_ph (x 3) (y 0)
  have h31 := pl_add_shift_ph (x 3) (y 1)
  have h32 := pl_add_shift_ph (x 3) (y 2)
  have h33 := pl_add_shift_ph (x 3) (y 3)
  have h34 := pl_add_shift_ph (x 3) (y 4)
  have h35 := pl_add_shift_ph (x 3) (y 5)
  have h40 := pl_add_shift_ph (x 4) (y 0)
  have h41 := pl_add_shift_ph (x 4) (y 1)
  have h42 := pl_add_shift_ph (x 4) (y 2)
  have h43 := pl_add_shift_ph (x 4) (y 3)
  have h44 := pl_add_shift_ph (x 4) (y 4)
  have h45 := pl_add_shift_ph (x 4) (y 5)
  have h50 := pl_add_shift_ph (x 5) (y 0)
  have h51 := pl_add_shift_ph (x 5) (y 1)
  have h52 := pl_add_shift_ph (x 5) (y 2)
  have h53 := pl_add_shift_ph (x 5) (y 3)
  have h54 := pl_add_shift_ph (x 5) (y 4)
  have h55 := pl_add_shift_ph (x 5) (y 5)
  calc
    (x 0 + 2 ^ 43 * x 1 + 2 ^ 86 * x 2 + 2 ^ 129 * x 3 + 2 ^ 172 * x 4 + 2 ^ 215 * x 5) *
          (y 0 + 2 ^ 43 * y 1 + 2 ^ 86 * y 2 + 2 ^ 129 * y 3 + 2 ^ 172 * y 4 + 2 ^ 215 * y 5) =
        (x 0 * y 0) + 2 ^ 43 * (x 0 * y 1 + x 1 * y 0) +
          2 ^ 86 * (x 0 * y 2 + x 1 * y 1 + x 2 * y 0) +
          2 ^ 129 * (x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0) +
          2 ^ 172 * (x 0 * y 4 + x 1 * y 3 + x 2 * y 2 + x 3 * y 1 + x 4 * y 0) +
          2 ^ 215 * (x 0 * y 5 + x 1 * y 4 + x 2 * y 3 + x 3 * y 2 + x 4 * y 1 + x 5 * y 0) +
          2 ^ 258 * (x 1 * y 5 + x 2 * y 4 + x 3 * y 3 + x 4 * y 2 + x 5 * y 1) +
          2 ^ 301 * (x 2 * y 5 + x 3 * y 4 + x 4 * y 3 + x 5 * y 2) +
          2 ^ 344 * (x 3 * y 5 + x 4 * y 4 + x 5 * y 3) +
          2 ^ 387 * (x 4 * y 5 + x 5 * y 4) +
          2 ^ 430 * (x 5 * y 5) :=
      by ring
    _ = _ := by
      rw [← h00, ← h01, ← h02, ← h03, ← h04, ← h05, ← h10, ← h11, ← h12, ← h13, ← h14, ← h15, ← h20,
        ← h21, ← h22, ← h23, ← h24, ← h25, ← h30, ← h31, ← h32, ← h33, ← h34, ← h35, ← h40, ← h41, ←
        h42, ← h43, ← h44, ← h45, ← h50, ← h51, ← h52, ← h53, ← h54, ← h55]
      ring

/-- **Ring correctness**: decoding the output limbs of `fd_r43x6_mul_fast`
yields the product of the decoded inputs modulo `p = 2^255 - 19`. -/
theorem decodeLimbs_limb_modEq (x y : Fin 6 → ℕ) :
    decodeNat (limb x y) ≡ (decodeNat x) * (decodeNat y) [MOD p] := by
  -- The high columns contribute a multiple of `p`, since `2^258 - 152 = 8·p`.
  have hsplit :
    decodeNat (limb x y) +
        p *
          (8 *
            (col x y 6 + 2 ^ 43 * col x y 7 + 2 ^ 86 * col x y 8 + 2 ^ 129 * col x y 9 +
              2 ^ 172 * col x y 10 +
              2 ^ 215 * col x y 11)) =
      (decodeNat x) * (decodeNat y) := by
    rw [cols_mul]
    simp only [decodeNat_eq, limb, p, Fin.reduceCastAdd, Fin.reduceAddNat]
    generalize col x y 0 = c0; generalize col x y 1 = c1
    generalize col x y 2 = c2; generalize col x y 3 = c3
    generalize col x y 4 = c4; generalize col x y 5 = c5
    generalize col x y 6 = c6; generalize col x y 7 = c7
    generalize col x y 8 = c8; generalize col x y 9 = c9
    generalize col x y 10 = c10; generalize col x y 11 = c11
    omega
  show _ % _ = _ % _
  conv_rhs => rw [← hsplit]
  rw [Nat.add_mul_mod_self_left]

/-- Ring correctness, stated in `ZMod p`. -/
theorem decodeLimbs_limb_zmod (x y : Fin 6 → ℕ) :
    ((decodeNat (limb x y) : ℕ) : ZMod p) =
      ((decodeNat x : ℕ) : ZMod p) * ((decodeNat y : ℕ) : ZMod p) := by
  have h := decodeLimbs_limb_modEq x y
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simpa [Nat.cast_mul] using this

/-! ## Bounds

Every `pl` is `< 2^52`; a `ph` bound comes from the input widths. Collecting
coefficients from `col`, no output limb uses more than 761 `pl`s and 912
`ph`s — both worst cases are limb 0 (`1 + 152·5` and `0 + 152·6`).
`limb_lt_of_bounds` is that count; the four rows of the table in `fd_r43x6.h`
(`u44/u45/u46/u47` in, `u62/u62/u62/u63` out) are instances. On `u47` inputs
the count reproduces the `{2434,1981,1528,1075,622,169}·2^51` analysis in the
source comments. -/

set_option maxHeartbeats 1000000 in
/-- Every output limb, in terms of a `ph` bound `Bo`. -/
private theorem limb_lt_of_bounds (x y : Fin 6 → ℕ) (Bo L : ℕ) (hph : ∀ i j, ph (x i) (y j) < Bo)
    (hL : 761 * 2 ^ 52 + 912 * Bo ≤ L) (k : Fin 6) : limb x y k < L := by
  have hpl : ∀ a b : ℕ, pl a b < 2 ^ 52 := fun a b => pl_lt a b
  fin_cases k <;>
    · simp [limb, col]
      have := hpl (x 0) (y 0); have := hpl (x 0) (y 1); have := hpl (x 0) (y 2)
      have := hpl (x 0) (y 3); have := hpl (x 0) (y 4); have := hpl (x 0) (y 5)
      have := hpl (x 1) (y 0); have := hpl (x 1) (y 1); have := hpl (x 1) (y 2)
      have := hpl (x 1) (y 3); have := hpl (x 1) (y 4); have := hpl (x 1) (y 5)
      have := hpl (x 2) (y 0); have := hpl (x 2) (y 1); have := hpl (x 2) (y 2)
      have := hpl (x 2) (y 3); have := hpl (x 2) (y 4); have := hpl (x 2) (y 5)
      have := hpl (x 3) (y 0); have := hpl (x 3) (y 1); have := hpl (x 3) (y 2)
      have := hpl (x 3) (y 3); have := hpl (x 3) (y 4); have := hpl (x 3) (y 5)
      have := hpl (x 4) (y 0); have := hpl (x 4) (y 1); have := hpl (x 4) (y 2)
      have := hpl (x 4) (y 3); have := hpl (x 4) (y 4); have := hpl (x 4) (y 5)
      have := hpl (x 5) (y 0); have := hpl (x 5) (y 1); have := hpl (x 5) (y 2)
      have := hpl (x 5) (y 3); have := hpl (x 5) (y 4); have := hpl (x 5) (y 5)
      have := hph 0 0; have := hph 0 1
      have := hph 0 2; have := hph 0 3
      have := hph 0 4; have := hph 0 5
      have := hph 1 0; have := hph 1 1
      have := hph 1 2; have := hph 1 3
      have := hph 1 4; have := hph 1 5
      have := hph 2 0; have := hph 2 1
      have := hph 2 2; have := hph 2 3
      have := hph 2 4; have := hph 2 5
      have := hph 3 0; have := hph 3 1
      have := hph 3 2; have := hph 3 3
      have := hph 3 4; have := hph 3 5
      have := hph 4 0; have := hph 4 1
      have := hph 4 2; have := hph 4 3
      have := hph 4 4; have := hph 4 5
      have := hph 5 0; have := hph 5 1
      have := hph 5 2; have := hph 5 3
      have := hph 5 4; have := hph 5 5
      omega

/-- **`u44` in, `u62` out.** -/
theorem limb_lt_u44 (x y : Fin 6 → ℕ) (hx : ∀ i, x i < 2 ^ 44) (hy : ∀ i, y i < 2 ^ 44)
    (k : Fin 6) : limb x y k < 2 ^ 62 :=
  limb_lt_of_bounds x y (2 ^ 36 * 2 ^ 9) (2 ^ 62)
    (fun i j => ph_lt_bound (u := 2 ^ 44) (v := 2 ^ 44) (hx i) (hy j) (by omega)) (by omega) k

/-- **`u45` in, `u62` out.** -/
theorem limb_lt_u45 (x y : Fin 6 → ℕ) (hx : ∀ i, x i < 2 ^ 45) (hy : ∀ i, y i < 2 ^ 45)
    (k : Fin 6) : limb x y k < 2 ^ 62 :=
  limb_lt_of_bounds x y (2 ^ 38 * 2 ^ 9) (2 ^ 62)
    (fun i j => ph_lt_bound (u := 2 ^ 45) (v := 2 ^ 45) (hx i) (hy j) (by omega)) (by omega) k

/-- **`u46` in, `u62` out.** -/
theorem limb_lt_u46 (x y : Fin 6 → ℕ) (hx : ∀ i, x i < 2 ^ 46) (hy : ∀ i, y i < 2 ^ 46)
    (k : Fin 6) : limb x y k < 2 ^ 62 :=
  limb_lt_of_bounds x y (2 ^ 40 * 2 ^ 9) (2 ^ 62)
    (fun i j => ph_lt_bound (u := 2 ^ 46) (v := 2 ^ 46) (hx i) (hy j) (by omega)) (by omega) k

/-- **`u46` in, the count exactly**: `761·2^52 + 912·2^49 = 7000·2^49`, about
`0.85·2^62`. The `u62` row rounds this up; `fd_r43x6_ge_is_eq` cannot afford
the rounding -- its `fd_r43x6_sub_fast` results are differences of `u46`
products *plus `p`*, and only this margin keeps them inside `s62`. -/
theorem limb_lt_u46_tight (x y : Fin 6 → ℕ) (hx : ∀ i, x i < 2 ^ 46) (hy : ∀ i, y i < 2 ^ 46)
    (k : Fin 6) : limb x y k < 7000 * 2 ^ 49 :=
  limb_lt_of_bounds x y (2 ^ 40 * 2 ^ 9) (7000 * 2 ^ 49)
    (fun i j => ph_lt_bound (u := 2 ^ 46) (v := 2 ^ 46) (hx i) (hy j) (by omega)) (by omega) k

/-- **`u47` in, `u63` out.** The count reproduces the source's
`2434·2^51 < 2^63`. -/
theorem limb_lt_u47 (x y : Fin 6 → ℕ) (hx : ∀ i, x i < 2 ^ 47) (hy : ∀ i, y i < 2 ^ 47)
    (k : Fin 6) : limb x y k < 2 ^ 63 :=
  limb_lt_of_bounds x y (2 ^ 42 * 2 ^ 9) (2 ^ 63)
    (fun i j => ph_lt_bound (u := 2 ^ 47) (v := 2 ^ 47) (hx i) (hy j) (by omega)) (by omega) k

/-- The bound the `BitVec.toInt` transfer needs: below `2^63`, a lane is not
read back as negative. -/
theorem limb_lt_two_pow_63 (x y : Fin 6 → ℕ) (hx : ∀ i, x i < 2 ^ 47) (hy : ∀ i, y i < 2 ^ 47)
    (k : Fin 6) : limb x y k < 2 ^ 63 :=
  limb_lt_u47 x y hx hy k

/-! ## The lanes -/

/-- The result vector predicted by the ℕ-level specification. -/
def mulVec (x y : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  limbVec (limb (limbNat x) (limbNat y))

end Firedancer.Avx512
