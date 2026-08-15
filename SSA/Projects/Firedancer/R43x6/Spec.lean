/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# ℕ-level specification of `fd_r43x6_mul_fast`

`fd_r43x6_mul_fast` multiplies two GF(2^255-19) elements in the radix 2^43
limb representation of Firedancer's AVX-512 ed25519 implementation
(`fd_r43x6.h`). This file defines, in plain natural-number arithmetic, the
values that the machine code computes, and proves the two mathematical facts
of interest about them:

* **bounds**: on *unreduced* inputs (all limbs `< 2^47`), each output limb is
  `< {2434,1981,1528,1075,622,169}·2^51 < 2^63`, matching the analysis in the
  comments of `fd_r43x6.h` (an *unsigned* result in the terminology used
  there);
* **ring correctness**: decoding the limbs (`Σ zₖ·2^(43k)`), the outputs
  represent the product of the inputs in ℤ/(2^255-19).

The connection between these definitions and the actual lifted SLLVM program
is made in `MulFastProof.lean`.

## The algorithm

With inputs `x = <x0,…,x5>`, `y = <y0,…,y5>` (value `Σ xᵢ 2^43i`), the
implementation forms, for every product `xᵢ·yⱼ`, the split

    pl i j = (xᵢ·yⱼ) % 2^52          -- vpmadd52luq
    ph i j = (xᵢ·yⱼ) / 2^52 * 2^9    -- vpmadd52huq, prescaled by 2^9

so that `pl i j + 2^43·(ph i j) = xᵢ·yⱼ` (note `2^52 = 2^43·2^9`). Grouping
by scale factor `2^43k` gives the twelve *column sums* `col 0`,…,`col 11`,
and the final fold uses `2^258 ≡ 152 (mod p)` (since `2^258 - 152 = 8·p`) to
produce the six output limbs

    limb k = col k + 152·col (k+6),   k = 0,…,5.
-/

namespace Firedancer.R43x6

/-- The field modulus `p = 2^255 - 19` of Curve25519. -/
def P : ℕ := 2^255 - 19

/-- Low 52 bits of a limb product, as `vpmadd52luq` computes them. -/
def pl (a b : ℕ) : ℕ := a * b % 2^52

/-- High bits of a limb product, prescaled by `2^9` (the `wwl_shl(…, 9)`
applied to every `vpmadd52huq` result), so that `pl a b + 2^43 * ph a b = a * b`. -/
def ph (a b : ℕ) : ℕ := a * b / 2^52 * 2^9

theorem pl_add_shift_ph (a b : ℕ) : pl a b + 2^43 * ph a b = a * b := by
  simp only [pl, ph]
  omega

theorem pl_lt (a b : ℕ) : pl a b < 2^52 :=
  Nat.mod_lt _ (by norm_num)

/-- The product of two unreduced limbs fits in 94 bits. -/
theorem mul_limbs_lt {a b : ℕ} (ha : a < 2^47) (hb : b < 2^47) : a * b < 2^94 := by
  calc a * b ≤ 2^47 * b := Nat.mul_le_mul_right _ (Nat.le_of_lt ha)
  _ < 2^47 * 2^47 := by omega
  _ = 2^94 := by norm_num

theorem ph_lt {a b : ℕ} (ha : a < 2^47) (hb : b < 2^47) : ph a b < 2^51 := by
  have hab : a * b < 2^94 := mul_limbs_lt ha hb
  simp only [ph]
  omega

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

/-- Decode limbs into the natural number they represent:
`Σ_{k<6} l k · 2^(43k)`. -/
def pack (l : ℕ → ℕ) : ℕ :=
  l 0 + 2^43 * l 1 + 2^86 * l 2 + 2^129 * l 3 + 2^172 * l 4 + 2^215 * l 5

/-! ## Bounds

With unreduced (`u47`) inputs, the analysis in `fd_r43x6.h` gives

    col {0,…,5}  < { 2, 5, 8,11,14,17}·2^51
    col {6,…,11} < {16,13,10, 7, 4, 1}·2^51
    limb k       < {2434,1981,1528,1075,622,169}·2^51 < 2^63

(each `pl < 2^52` counts for two `2^51`, each `ph < 2^51` for one). -/

/-- The limb-wise output bound of `fd_r43x6_mul_fast`:
`{2434,1981,1528,1075,622,169}`, in units of `2^51`. -/
def limbBound : ℕ → ℕ
  | 0 => 2434 | 1 => 1981 | 2 => 1528 | 3 => 1075 | 4 => 622 | 5 => 169
  | _ => 0

set_option maxHeartbeats 1000000 in
/-- **Output bounds**: on unreduced inputs (limbs `< 2^47`), the output limbs
of `fd_r43x6_mul_fast` are bounded by `{2434,1981,1528,1075,622,169}·2^51`.
In particular limb 5 is `< 2^63` and all others are `< 2^62.3`, so the result
is *unsigned* in the terminology of `fd_r43x6.h` (and well below `2^64`, so
the 64-bit lanes do not overflow). -/
theorem limb_lt (x y : ℕ → ℕ) (hx : ∀ i < 6, x i < 2^47) (hy : ∀ i < 6, y i < 2^47)
    (k : ℕ) (hk : k < 6) :
    limb x y k < limbBound k * 2^51 := by
  have hpl : ∀ i j, pl (x i) (y j) < 2^52 := fun i j => pl_lt _ _
  have hph : ∀ i < 6, ∀ j < 6, ph (x i) (y j) < 2^51 :=
    fun i hi j hj => ph_lt (hx i hi) (hy j hj)
  interval_cases k <;>
  · simp only [limb, col, limbBound]
    have := hpl 0 0; have := hpl 0 1; have := hpl 0 2; have := hpl 0 3
    have := hpl 0 4; have := hpl 0 5; have := hpl 1 0; have := hpl 1 1
    have := hpl 1 2; have := hpl 1 3; have := hpl 1 4; have := hpl 1 5
    have := hpl 2 0; have := hpl 2 1; have := hpl 2 2; have := hpl 2 3
    have := hpl 2 4; have := hpl 2 5; have := hpl 3 0; have := hpl 3 1
    have := hpl 3 2; have := hpl 3 3; have := hpl 3 4; have := hpl 3 5
    have := hpl 4 0; have := hpl 4 1; have := hpl 4 2; have := hpl 4 3
    have := hpl 4 4; have := hpl 4 5; have := hpl 5 0; have := hpl 5 1
    have := hpl 5 2; have := hpl 5 3; have := hpl 5 4; have := hpl 5 5
    have hph' : ∀ i j, i < 6 → j < 6 → ph (x i) (y j) < 2^51 :=
      fun i j hi hj => hph i hi j hj
    have := hph' 0 0; have := hph' 0 1; have := hph' 0 2; have := hph' 0 3
    have := hph' 0 4; have := hph' 0 5; have := hph' 1 0; have := hph' 1 1
    have := hph' 1 2; have := hph' 1 3; have := hph' 1 4; have := hph' 1 5
    have := hph' 2 0; have := hph' 2 1; have := hph' 2 2; have := hph' 2 3
    have := hph' 2 4; have := hph' 2 5; have := hph' 3 0; have := hph' 3 1
    have := hph' 3 2; have := hph' 3 3; have := hph' 3 4; have := hph' 3 5
    have := hph' 4 0; have := hph' 4 1; have := hph' 4 2; have := hph' 4 3
    have := hph' 4 4; have := hph' 4 5; have := hph' 5 0; have := hph' 5 1
    have := hph' 5 2; have := hph' 5 3; have := hph' 5 4; have := hph' 5 5
    simp only [show (0:ℕ) < 6 from by omega, show (1:ℕ) < 6 from by omega,
      show (2:ℕ) < 6 from by omega, show (3:ℕ) < 6 from by omega,
      show (4:ℕ) < 6 from by omega, show (5:ℕ) < 6 from by omega,
      forall_const] at *
    omega

/-- All output limbs fit in 63 bits (`2434·2^51 < 2^63`); in particular the
64-bit lanes cannot overflow. -/
theorem limb_lt_two_pow_63 (x y : ℕ → ℕ)
    (hx : ∀ i < 6, x i < 2^47) (hy : ∀ i < 6, y i < 2^47) (k : ℕ) (hk : k < 6) :
    limb x y k < 2^63 := by
  have h := limb_lt x y hx hy k hk
  have hb : limbBound k * 2^51 ≤ 2434 * 2^51 := by
    interval_cases k <;> · simp only [limbBound]; omega
  omega

/-! ## Ring correctness -/

set_option exponentiation.threshold 600 in
/-- The twelve columns decode to the full product: before folding, the
grade-school diagram is exact. -/
theorem cols_mul (x y : ℕ → ℕ) :
    (pack x) * (pack y) =
      col x y 0 + 2^43 * col x y 1 + 2^86 * col x y 2 + 2^129 * col x y 3
      + 2^172 * col x y 4 + 2^215 * col x y 5 + 2^258 * col x y 6
      + 2^301 * col x y 7 + 2^344 * col x y 8 + 2^387 * col x y 9
      + 2^430 * col x y 10 + 2^473 * col x y 11 := by
  simp only [pack, col]
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

set_option exponentiation.threshold 600 in
/-- The key identity behind the fold: `2^258 - 152 = 8·p`, i.e.
`2^258 ≡ 152 (mod p)`. -/
theorem two_pow_258_sub_152 : 2^258 - 152 = 8 * P := by
  norm_num [P]

/-- **Ring correctness**: decoding the output limbs of `fd_r43x6_mul_fast`
yields the product of the decoded inputs modulo `p = 2^255 - 19`. -/
theorem pack_limb_modEq (x y : ℕ → ℕ) :
    pack (limb x y) ≡ (pack x) * (pack y) [MOD P] := by
  -- Split the packed result into the low columns plus `P` times a junk term.
  have hsplit : pack (limb x y)
      + P * (8 * (col x y 6 + 2^43 * col x y 7 + 2^86 * col x y 8
          + 2^129 * col x y 9 + 2^172 * col x y 10 + 2^215 * col x y 11))
      = (pack x) * (pack y) := by
    rw [cols_mul]
    simp only [pack, limb, P]
    -- Everything is linear in the twelve columns; `omega` handles the
    -- (large) literal coefficients and the `2^255 - 19` subtraction.
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
    ((pack (limb x y) : ℕ) : ZMod P)
      = ((pack x : ℕ) : ZMod P) * ((pack y : ℕ) : ZMod P) := by
  have h := pack_limb_modEq x y
  have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
  simpa [Nat.cast_mul] using this

end Firedancer.R43x6
