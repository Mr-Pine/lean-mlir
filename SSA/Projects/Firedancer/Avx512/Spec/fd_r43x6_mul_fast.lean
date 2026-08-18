import SSA.Projects.Firedancer.Avx512.Mlir.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Avx512.Denote.fd_r43x6_mul_fast
import SSA.Projects.Firedancer.Avx512.Spec.Common
import SSA.Projects.Firedancer.MLIR.Poison
import SSA.Projects.Firedancer.Ed25519
import Mathlib.Tactic.IntervalCases

/-!
# `fd_r43x6_mul_fast` multiplies its inputs in `ZMod p`

Denoting the lifted SLLVM program and decoding the six output limbs yields the
product of the decoded inputs in `GF(2^255 - 19)`.

The proof composes three layers:

* `denote_fd_r43x6_mul_fast` (`Avx512/Denote/`): the denotation is the lane
  expression `mulFastResult`;
* `pack_limb_zmod`: ring correctness of the ℕ-level limbs `limb`;
* `mulFastResult_eq`: each output lane is `BitVec.ofNat 64` of `limb`.

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
def col (x y : ℕ → ℕ) : ℕ → ℕ
  | 0 => pl (x 0) (y 0)
  | 1 => pl (x 0) (y 1) + pl (x 1) (y 0)
      + ph (x 0) (y 0)
  | 2 => pl (x 0) (y 2) + pl (x 1) (y 1) + pl (x 2) (y 0)
      + ph (x 0) (y 1) + ph (x 1) (y 0)
  | 3 => pl (x 0) (y 3) + pl (x 1) (y 2) + pl (x 2) (y 1) + pl (x 3) (y 0)
      + ph (x 0) (y 2) + ph (x 1) (y 1) + ph (x 2) (y 0)
  | 4 => pl (x 0) (y 4) + pl (x 1) (y 3) + pl (x 2) (y 2) + pl (x 3) (y 1)
      + pl (x 4) (y 0)
      + ph (x 0) (y 3) + ph (x 1) (y 2) + ph (x 2) (y 1) + ph (x 3) (y 0)
  | 5 => pl (x 0) (y 5) + pl (x 1) (y 4) + pl (x 2) (y 3) + pl (x 3) (y 2)
      + pl (x 4) (y 1) + pl (x 5) (y 0)
      + ph (x 0) (y 4) + ph (x 1) (y 3) + ph (x 2) (y 2) + ph (x 3) (y 1)
      + ph (x 4) (y 0)
  | 6 => pl (x 1) (y 5) + pl (x 2) (y 4) + pl (x 3) (y 3) + pl (x 4) (y 2)
      + pl (x 5) (y 1)
      + ph (x 0) (y 5) + ph (x 1) (y 4) + ph (x 2) (y 3) + ph (x 3) (y 2)
      + ph (x 4) (y 1) + ph (x 5) (y 0)
  | 7 => pl (x 2) (y 5) + pl (x 3) (y 4) + pl (x 4) (y 3) + pl (x 5) (y 2)
      + ph (x 1) (y 5) + ph (x 2) (y 4) + ph (x 3) (y 3) + ph (x 4) (y 2)
      + ph (x 5) (y 1)
  | 8 => pl (x 3) (y 5) + pl (x 4) (y 4) + pl (x 5) (y 3)
      + ph (x 2) (y 5) + ph (x 3) (y 4) + ph (x 4) (y 3) + ph (x 5) (y 2)
  | 9 => pl (x 4) (y 5) + pl (x 5) (y 4)
      + ph (x 3) (y 5) + ph (x 4) (y 4) + ph (x 5) (y 3)
  | 10 => pl (x 5) (y 5)
      + ph (x 4) (y 5) + ph (x 5) (y 4)
  | 11 => ph (x 5) (y 5)
  | _ => 0

/-- The output limbs of `fd_r43x6_mul_fast`: the low six columns, plus the
high six folded in with weight `152 = 2^258 mod p`. -/
def limb (x y : ℕ → ℕ) (k : ℕ) : ℕ :=
  col x y k + 152 * col x y (k + 6)

/-! ## Ring correctness -/

set_option exponentiation.threshold 600 in
/-- The twelve columns decode to the full product: each of the thirty-six
products appears exactly once, at the weight `2^(43(i+j))` of its column. -/
theorem cols_mul (x y : ℕ → ℕ) :
    (pack x) * (pack y) =
      col x y 0 + 2^43 * col x y 1 + 2^86 * col x y 2 + 2^129 * col x y 3
      + 2^172 * col x y 4 + 2^215 * col x y 5 + 2^258 * col x y 6
      + 2^301 * col x y 7 + 2^344 * col x y 8 + 2^387 * col x y 9
      + 2^430 * col x y 10 + 2^473 * col x y 11 := by
  simp only [pack, col]
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
  calc (x 0 + 2^43 * x 1 + 2^86 * x 2 + 2^129 * x 3 + 2^172 * x 4 + 2^215 * x 5)
        * (y 0 + 2^43 * y 1 + 2^86 * y 2 + 2^129 * y 3 + 2^172 * y 4 + 2^215 * y 5)
      = (x 0 * y 0) + 2^43 * (x 0 * y 1 + x 1 * y 0)
        + 2^86 * (x 0 * y 2 + x 1 * y 1 + x 2 * y 0)
        + 2^129 * (x 0 * y 3 + x 1 * y 2 + x 2 * y 1 + x 3 * y 0)
        + 2^172 * (x 0 * y 4 + x 1 * y 3 + x 2 * y 2 + x 3 * y 1 + x 4 * y 0)
        + 2^215 * (x 0 * y 5 + x 1 * y 4 + x 2 * y 3 + x 3 * y 2 + x 4 * y 1 + x 5 * y 0)
        + 2^258 * (x 1 * y 5 + x 2 * y 4 + x 3 * y 3 + x 4 * y 2 + x 5 * y 1)
        + 2^301 * (x 2 * y 5 + x 3 * y 4 + x 4 * y 3 + x 5 * y 2)
        + 2^344 * (x 3 * y 5 + x 4 * y 4 + x 5 * y 3)
        + 2^387 * (x 4 * y 5 + x 5 * y 4)
        + 2^430 * (x 5 * y 5) := by ring
    _ = _ := by
        rw [← h00, ← h01, ← h02, ← h03, ← h04, ← h05,
            ← h10, ← h11, ← h12, ← h13, ← h14, ← h15,
            ← h20, ← h21, ← h22, ← h23, ← h24, ← h25,
            ← h30, ← h31, ← h32, ← h33, ← h34, ← h35,
            ← h40, ← h41, ← h42, ← h43, ← h44, ← h45,
            ← h50, ← h51, ← h52, ← h53, ← h54, ← h55]
        ring

/-- **Ring correctness**: decoding the output limbs of `fd_r43x6_mul_fast`
yields the product of the decoded inputs modulo `p = 2^255 - 19`. -/
theorem pack_limb_modEq (x y : ℕ → ℕ) :
    pack (limb x y) ≡ (pack x) * (pack y) [MOD p] := by
  -- The high columns contribute a multiple of `p`, since `2^258 - 152 = 8·p`.
  have hsplit : pack (limb x y)
      + p * (8 * (col x y 6 + 2^43 * col x y 7 + 2^86 * col x y 8
          + 2^129 * col x y 9 + 2^172 * col x y 10 + 2^215 * col x y 11))
      = (pack x) * (pack y) := by
    rw [cols_mul]
    simp only [pack, limb, p]
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
theorem pack_limb_zmod (x y : ℕ → ℕ) :
    ((pack (limb x y) : ℕ) : ZMod p)
      = ((pack x : ℕ) : ZMod p) * ((pack y : ℕ) : ZMod p) := by
  have h := pack_limb_modEq x y
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
private theorem limb_lt_of_bounds (x y : ℕ → ℕ) (Bo L : ℕ)
    (hph : ∀ i < 6, ∀ j < 6, ph (x i) (y j) < Bo)
    (hL : 761 * 2^52 + 912 * Bo ≤ L)
    (k : ℕ) (hk : k < 6) :
    limb x y k < L := by
  have hpl : ∀ a b : ℕ, pl a b < 2^52 := fun a b => pl_lt a b
  interval_cases k <;>
  · simp only [limb, col]
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
    have := hph 0 (by omega) 0 (by omega); have := hph 0 (by omega) 1 (by omega)
    have := hph 0 (by omega) 2 (by omega); have := hph 0 (by omega) 3 (by omega)
    have := hph 0 (by omega) 4 (by omega); have := hph 0 (by omega) 5 (by omega)
    have := hph 1 (by omega) 0 (by omega); have := hph 1 (by omega) 1 (by omega)
    have := hph 1 (by omega) 2 (by omega); have := hph 1 (by omega) 3 (by omega)
    have := hph 1 (by omega) 4 (by omega); have := hph 1 (by omega) 5 (by omega)
    have := hph 2 (by omega) 0 (by omega); have := hph 2 (by omega) 1 (by omega)
    have := hph 2 (by omega) 2 (by omega); have := hph 2 (by omega) 3 (by omega)
    have := hph 2 (by omega) 4 (by omega); have := hph 2 (by omega) 5 (by omega)
    have := hph 3 (by omega) 0 (by omega); have := hph 3 (by omega) 1 (by omega)
    have := hph 3 (by omega) 2 (by omega); have := hph 3 (by omega) 3 (by omega)
    have := hph 3 (by omega) 4 (by omega); have := hph 3 (by omega) 5 (by omega)
    have := hph 4 (by omega) 0 (by omega); have := hph 4 (by omega) 1 (by omega)
    have := hph 4 (by omega) 2 (by omega); have := hph 4 (by omega) 3 (by omega)
    have := hph 4 (by omega) 4 (by omega); have := hph 4 (by omega) 5 (by omega)
    have := hph 5 (by omega) 0 (by omega); have := hph 5 (by omega) 1 (by omega)
    have := hph 5 (by omega) 2 (by omega); have := hph 5 (by omega) 3 (by omega)
    have := hph 5 (by omega) 4 (by omega); have := hph 5 (by omega) 5 (by omega)
    omega

/-- **`u44` in, `u62` out.** -/
theorem limb_lt_u44 (x y : ℕ → ℕ)
    (hx : ∀ i < 6, x i < 2^44) (hy : ∀ i < 6, y i < 2^44) (k : ℕ) (hk : k < 6) :
    limb x y k < 2^62 :=
  limb_lt_of_bounds x y (2^36 * 2^9) (2^62)
    (fun i hi j hj => ph_lt_bound (u := 2^44) (v := 2^44) (hx i hi) (hy j hj) (by omega))
    (by omega) k hk

/-- **`u45` in, `u62` out.** -/
theorem limb_lt_u45 (x y : ℕ → ℕ)
    (hx : ∀ i < 6, x i < 2^45) (hy : ∀ i < 6, y i < 2^45) (k : ℕ) (hk : k < 6) :
    limb x y k < 2^62 :=
  limb_lt_of_bounds x y (2^38 * 2^9) (2^62)
    (fun i hi j hj => ph_lt_bound (u := 2^45) (v := 2^45) (hx i hi) (hy j hj) (by omega))
    (by omega) k hk

/-- **`u46` in, `u62` out.** -/
theorem limb_lt_u46 (x y : ℕ → ℕ)
    (hx : ∀ i < 6, x i < 2^46) (hy : ∀ i < 6, y i < 2^46) (k : ℕ) (hk : k < 6) :
    limb x y k < 2^62 :=
  limb_lt_of_bounds x y (2^40 * 2^9) (2^62)
    (fun i hi j hj => ph_lt_bound (u := 2^46) (v := 2^46) (hx i hi) (hy j hj) (by omega))
    (by omega) k hk

/-- **`u47` in, `u63` out.** The count reproduces the source's
`2434·2^51 < 2^63`. -/
theorem limb_lt_u47 (x y : ℕ → ℕ)
    (hx : ∀ i < 6, x i < 2^47) (hy : ∀ i < 6, y i < 2^47) (k : ℕ) (hk : k < 6) :
    limb x y k < 2^63 :=
  limb_lt_of_bounds x y (2^42 * 2^9) (2^63)
    (fun i hi j hj => ph_lt_bound (u := 2^47) (v := 2^47) (hx i hi) (hy j hj) (by omega))
    (by omega) k hk

/-- The bound the `BitVec.toInt` transfer needs: below `2^63`, a lane is not
read back as negative. -/
theorem limb_lt_two_pow_63 (x y : ℕ → ℕ)
    (hx : ∀ i < 6, x i < 2^47) (hy : ∀ i < 6, y i < 2^47) (k : ℕ) (hk : k < 6) :
    limb x y k < 2^63 :=
  limb_lt_u47 x y hx hy k hk

/-! ## The lanes -/

/-- The result vector predicted by the ℕ-level specification. -/
def mulVec (x y : Vector (BitVec 64) 8) : Vector (BitVec 64) 8 :=
  limbVec (limb (limbNat x) (limbNat y))

set_option maxHeartbeats 8000000 in
/-- **Lane derivation**: on unreduced inputs with lanes 6 and 7 of `y` zero,
every output lane of `fd_r43x6_mul_fast` is the corresponding ℕ-level limb
reduced mod `2^64`. The reduction is the identity, by `limb_lt_two_pow_63`. -/
theorem mulFastResult_eq (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulFastResult x y = (mulVec x y).map PoisonOr.value := by
  have bx0 : x[0].toNat < 2^47 := unn_toNat x 47 (by omega) hx 0 (by omega)
  have bx1 : x[1].toNat < 2^47 := unn_toNat x 47 (by omega) hx 1 (by omega)
  have bx2 : x[2].toNat < 2^47 := unn_toNat x 47 (by omega) hx 2 (by omega)
  have bx3 : x[3].toNat < 2^47 := unn_toNat x 47 (by omega) hx 3 (by omega)
  have bx4 : x[4].toNat < 2^47 := unn_toNat x 47 (by omega) hx 4 (by omega)
  have bx5 : x[5].toNat < 2^47 := unn_toNat x 47 (by omega) hx 5 (by omega)
  have by0 : y[0].toNat < 2^47 := unn_toNat y 47 (by omega) hy 0 (by omega)
  have by1 : y[1].toNat < 2^47 := unn_toNat y 47 (by omega) hy 1 (by omega)
  have by2 : y[2].toNat < 2^47 := unn_toNat y 47 (by omega) hy 2 (by omega)
  have by3 : y[3].toNat < 2^47 := unn_toNat y 47 (by omega) hy 3 (by omega)
  have by4 : y[4].toNat < 2^47 := unn_toNat y 47 (by omega) hy 4 (by omega)
  have by5 : y[5].toNat < 2^47 := unn_toNat y 47 (by omega) hy 5 (by omega)
  have b6 : y[6].toNat = 0 := by rw [hy6]; rfl
  have b7 : y[7].toNat = 0 := by rw [hy7]; rfl
  have tx0 : x[0].toNat < 2^52 := by omega
  have tx1 : x[1].toNat < 2^52 := by omega
  have tx2 : x[2].toNat < 2^52 := by omega
  have tx3 : x[3].toNat < 2^52 := by omega
  have tx4 : x[4].toNat < 2^52 := by omega
  have tx5 : x[5].toNat < 2^52 := by omega
  have ty0 : y[0].toNat < 2^52 := by omega
  have ty1 : y[1].toNat < 2^52 := by omega
  have ty2 : y[2].toNat < 2^52 := by omega
  have ty3 : y[3].toNat < 2^52 := by omega
  have ty4 : y[4].toNat < 2^52 := by omega
  have ty5 : y[5].toNat < 2^52 := by omega
  have ty6 : y[6].toNat < 2^52 := by omega
  have ty7 : y[7].toNat < 2^52 := by omega
  apply Vector.ext
  intro i hi
  interval_cases i <;>
    · simp only [mulFastResult, mulVec, limbVec, Vector.getElem_map, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      try congr 1
      try simp only [lo_eq, hi_eq,
        tx0, tx1, tx2, tx3, tx4, tx5, ty0, ty1, ty2, ty3, ty4, ty5, ty6, ty7,
        natCast_bv, bv_zero, ← BitVec.ofNat_add, ofNat_mul24, ofNat_shl7]
      try congr 1
      try simp only [limb, col, limbNat, b6, b7, pl_zero_right, ph_zero_right]
      try ring

abbrev mulValue (x y : Vector (BitVec 64) 8) := (fd_r43x6_mul_fast.denote
          (Ctxt.Valuation.ofPair (y.map PoisonOr.value) (x.map PoisonOr.value))).head.getValues

abbrev mulIsMul (x y : Vector (BitVec 64) 8) :=
    (fun l => (R43x6.decode' l : ZMod p)) <$> mulValue x y
      = .value ((R43x6.decode' x : ZMod p) * (R43x6.decode' y : ZMod p))

private def output_bounds_u44_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U44 x → R43x6.U44 y → R43x6.U62 (mulValue x y).getValue
private def output_bounds_u45_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U45 x → R43x6.U45 y → R43x6.U62 (mulValue x y).getValue
private def output_bounds_u46_u62 (x y : Vector (BitVec 64) 8) :=
  R43x6.U46 x → R43x6.U46 y → R43x6.U62 (mulValue x y).getValue
private def output_bounds_u47_u63 (x y : Vector (BitVec 64) 8) :=
  R43x6.U47 x → R43x6.U47 y → R43x6.U63 (mulValue x y).getValue

/-- The limbs of an unreduced input, bounded as naturals. -/
private theorem limbNat_lt (x : Vector (BitVec 64) 8) (hx : R43x6.Unreduced x) :
    ∀ i < 6, limbNat x i < 2^47 := by
  intro i hi
  interval_cases i <;>
    simpa [limbNat] using unn_toNat x 47 (by omega) hx _ (by omega)

set_option maxHeartbeats 1000000 in
private theorem mulIsMulThm (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulIsMul x y := by
  have hbx : ∀ i < 6, limbNat x i < 2^47 := limbNat_lt x hx
  have hby : ∀ i < 6, limbNat y i < 2^47 := limbNat_lt y hy
  -- 1. denotation to lanes to specified limbs; the poison layer collapses
  rw [mulIsMul, mulValue, denote_fd_r43x6_mul_fast, mulFastResult_eq x y hx hy hy6 hy7]
  simp only [HVector.head, Vector.getValues_map_value, PoisonOr.map_value,
    PoisonOr.value_inj]
  -- 2. decode both sides into casts of `pack`
  have hdecode : ∀ (v : Vector (BitVec 64) 8), R43x6.Unreduced v →
      R43x6.decode' v = ((pack (limbNat v) : ℕ) : Int) := by
    intro v hv
    have hv8 : v = #v[v[0],v[1],v[2],v[3],v[4],v[5],v[6],v[7]] := by
      apply Vector.ext; intro i hi; interval_cases i <;> rfl
    have hb : ∀ i < 6, limbNat v i < 2^47 := limbNat_lt v hv
    conv_lhs => rw [hv8]
    rw [decode'_lit,
      toInt_of_lt (by simpa [limbNat] using hb 0 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 1 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 2 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 3 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 4 (by omega)),
      toInt_of_lt (by simpa [limbNat] using hb 5 (by omega))]
    push_cast [pack, limbNat]
    try ring
  rw [mulVec, decode'_limbVec _ (limb_lt_two_pow_63 _ _ hbx hby),
    hdecode x hx, hdecode y hy]
  -- 3. both sides are now casts of `pack`, so `pack_limb_zmod` applies
  push_cast
  exact pack_limb_zmod (limbNat x) (limbNat y)

/-! ## Output bounds

The four rows of the `fd_r43x6.h` table, each `limb_lt_u4x` transported
through `mulFastResult_eq`: output lane `k < 6` is the specified limb, lanes 6
and 7 are zero, and none is read back as negative. -/

/-- The program's result, with the poison layer discharged. -/
private theorem mulValue_eq (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulValue x y = .value (mulVec x y) := by
  rw [mulValue, denote_fd_r43x6_mul_fast, mulFastResult_eq x y hx hy hy6 hy7]
  simp only [HVector.head, Vector.getValues_map_value]

/-- Two-sided lane bounds from a ceiling `N` on the ℕ-level limbs. -/
private theorem output_bounds_of (x y : Vector (BitVec 64) 8) (N : ℕ) (hN : N ≤ 2^63)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0)
    (hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < N) :
    R43x6.BoundedUpper ((N : Int) - 1) (mulValue x y).getValue
      ∧ R43x6.BoundedLower 0 (mulValue x y).getValue := by
  have hv : (mulValue x y).getValue = mulVec x y := by
    rw [mulValue_eq x y hx hy hy6 hy7]; rfl
  rw [hv, mulVec]
  exact limbVec_bounds _ N hN hb

private theorem output_u44 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u44_u62 x y := by
  intro hinx hiny
  have hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < 2^62 := fun k hk =>
    limb_lt_u44 _ _
      (fun i hi => by interval_cases i <;> exact unn_toNat x 44 (by omega) hinx _ (by omega))
      (fun i hi => by interval_cases i <;> exact unn_toNat y 44 (by omega) hiny _ (by omega))
      k hk
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u45 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u45_u62 x y := by
  intro hinx hiny
  have hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < 2^62 := fun k hk =>
    limb_lt_u45 _ _
      (fun i hi => by interval_cases i <;> exact unn_toNat x 45 (by omega) hinx _ (by omega))
      (fun i hi => by interval_cases i <;> exact unn_toNat y 45 (by omega) hiny _ (by omega))
      k hk
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u46 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u46_u62 x y := by
  intro hinx hiny
  have hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < 2^62 := fun k hk =>
    limb_lt_u46 _ _
      (fun i hi => by interval_cases i <;> exact unn_toNat x 46 (by omega) hinx _ (by omega))
      (fun i hi => by interval_cases i <;> exact unn_toNat y 46 (by omega) hiny _ (by omega))
      k hk
  exact_mod_cast output_bounds_of x y (2^62) (by omega) hx hy hy6 hy7 hb

private theorem output_u47 (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) : output_bounds_u47_u63 x y := by
  intro hinx hiny
  have hb : ∀ k < 6, limb (limbNat x) (limbNat y) k < 2^63 := fun k hk =>
    limb_lt_u47 _ _
      (fun i hi => by interval_cases i <;> exact unn_toNat x 47 (by omega) hinx _ (by omega))
      (fun i hi => by interval_cases i <;> exact unn_toNat y 47 (by omega) hiny _ (by omega))
      k hk
  exact_mod_cast output_bounds_of x y (2^63) (by omega) hx hy hy6 hy7 hb

/-- **Specification of `fd_r43x6_mul_fast`**: on unreduced inputs whose `y`
high lanes are zero, the six output limbs decode to the product of the decoded
inputs in `GF(2^255 - 19)`, and the four input/output width guarantees of
`fd_r43x6.h` hold. -/
theorem spec_fd_r43x6_mul_fast (x y : Vector (BitVec 64) 8)
    (hx : R43x6.Unreduced x) (hy : R43x6.Unreduced y)
    (hy6 : y[6] = 0) (hy7 : y[7] = 0) :
    mulIsMul x y ∧ output_bounds_u44_u62 x y ∧ output_bounds_u45_u62 x y
      ∧ output_bounds_u46_u62 x y ∧ output_bounds_u47_u63 x y :=
  ⟨mulIsMulThm x y hx hy hy6 hy7, output_u44 x y hx hy hy6 hy7,
    output_u45 x y hx hy hy6 hy7, output_u46 x y hx hy hy6 hy7,
    output_u47 x y hx hy hy6 hy7⟩

end Firedancer.Avx512
