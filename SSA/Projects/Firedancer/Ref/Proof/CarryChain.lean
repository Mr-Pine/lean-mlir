import SSA.Projects.Firedancer.Ref.Spec.F25519
import SSA.Projects.Firedancer.Ref.Proof.Limb

/-!
# The shared carry chain

`fiat_25519_carry_mul` and `fiat_25519_carry_square` compute different column
sums and then run the *same* carry chain over them. The chain's bounds and its
value are proved here once, in terms of the five columns; each caller supplies
its own column bounds and its own value lemma.

The column bounds happen to coincide too -- at fiat's loose input bound both
reach `693 * 2 ^ 102` in column 0 down to `45 * 2 ^ 102` in column 4 -- so
`carry_chain_le` and `carry_chain_value` apply to both verbatim.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- The carry chain both `fiat_25519_carry_mul` and `fiat_25519_carry_square`
end in, over their five column sums. -/
def carry_chain (c0 c1 c2 c3 c4 : ℕ) : Fin 5 → ℕ :=
  let x27 := c0 / 2 ^ 51
  let x28 := c0 % 2 ^ 51
  let x33 := x27 + c1
  let x34 := x33 / 2 ^ 51
  let x35 := x33 % 2 ^ 51
  let x36 := x34 + c2
  let x37 := x36 / 2 ^ 51
  let x38 := x36 % 2 ^ 51
  let x39 := x37 + c3
  let x40 := x39 / 2 ^ 51
  let x41 := x39 % 2 ^ 51
  let x42 := x40 + c4
  let x43 := x42 / 2 ^ 51
  let x44 := x42 % 2 ^ 51
  let x45 := x43 * 19
  let x46 := x28 + x45
  let x47 := x46 / 2 ^ 51
  let x48 := x46 % 2 ^ 51
  let x49 := x47 + x35
  let x50 := x49 / 2 ^ 51 % 2 ^ 8
  let x51 := x49 % 2 ^ 51
  let x52 := x50 + x38
  ![x48, x51, x52, x41, x44]

/-- Every carry of the chain. The column bounds are separate because `d4 * 19`
runs in a 64-bit register, which only column 4's bound fits. -/
lemma carry_chain_carries (c0 c1 c2 c3 c4 d0 d1 d2 d3 d4 d5 d6 : ℕ)
    (h0 : c0 ≤ 693 * 2 ^ 102) (h1 : c1 ≤ 531 * 2 ^ 102) (h2 : c2 ≤ 369 * 2 ^ 102)
    (h3 : c3 ≤ 207 * 2 ^ 102) (h4 : c4 ≤ 45 * 2 ^ 102)
    (e0 : d0 = c0 / 2 ^ 51) (e1 : d1 = (d0 + c1) / 2 ^ 51)
    (e2 : d2 = (d1 + c2) / 2 ^ 51) (e3 : d3 = (d2 + c3) / 2 ^ 51)
    (e4 : d4 = (d3 + c4) / 2 ^ 51) (e5 : d5 = (c0 % 2 ^ 51 + d4 * 19) / 2 ^ 51)
    (e6 : d6 = (d5 + (d0 + c1) % 2 ^ 51) / 2 ^ 51) :
    d0 ≤ 693 * 2 ^ 51 ∧ d1 ≤ 531 * 2 ^ 51 + 693 ∧ d2 ≤ 369 * 2 ^ 51 + 532
      ∧ d3 ≤ 207 * 2 ^ 51 + 370 ∧ d4 ≤ 45 * 2 ^ 51 + 208 ∧ d5 ≤ 856 ∧ d6 ≤ 1
      ∧ d6 % 2 ^ 8 + (d1 + c2) % 2 ^ 51 ≤ 0x8000000000000 := by
  have b0 : d0 ≤ 693 * 2 ^ 51 := by omega
  have b1 : d1 ≤ 531 * 2 ^ 51 + 693 := by omega
  have b2 : d2 ≤ 369 * 2 ^ 51 + 532 := by omega
  have b3 : d3 ≤ 207 * 2 ^ 51 + 370 := by omega
  have b4 : d4 ≤ 45 * 2 ^ 51 + 208 := by omega
  have b5 : d5 ≤ 856 := by omega
  have b6 : d6 ≤ 1 := by omega
  have t6 : d6 % 2 ^ 8 = d6 := Nat.mod_eq_of_lt (by omega)
  have b7 : d6 % 2 ^ 8 + (d1 + c2) % 2 ^ 51 ≤ 0x8000000000000 := by rw [t6]; omega
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩

/-- fiat's tight output bound. -/
lemma carry_chain_le (c0 c1 c2 c3 c4 : ℕ)
    (h0 : c0 ≤ 693 * 2 ^ 102) (h1 : c1 ≤ 531 * 2 ^ 102) (h2 : c2 ≤ 369 * 2 ^ 102)
    (h3 : c3 ≤ 207 * 2 ^ 102) (h4 : c4 ≤ 45 * 2 ^ 102) :
    ∀ i, carry_chain c0 c1 c2 c3 c4 i ≤ 0x8000000000000 := by
  obtain ⟨-, -, -, -, -, -, -, b7⟩ := carry_chain_carries c0 c1 c2 c3 c4 _ _ _ _ _ _ _
    h0 h1 h2 h3 h4 rfl rfl rfl rfl rfl rfl rfl
  -- not `fin_cases … <;> simp`: that folds the goal's `2 ^ 51`s into literals
  -- while `b7` keeps the powers, leaving omega two unrelated atoms.
  refine forall_fin5 ?_ ?_ ?_ ?_ ?_ <;> omega

/-- The chain's limbs are all `0` only when its columns are. -/
lemma carry_chain_eq_zero (c0 c1 c2 c3 c4 : ℕ)
    (h0 : c0 ≤ 693 * 2 ^ 102) (h1 : c1 ≤ 531 * 2 ^ 102) (h2 : c2 ≤ 369 * 2 ^ 102)
    (h3 : c3 ≤ 207 * 2 ^ 102) (h4 : c4 ≤ 45 * 2 ^ 102)
    (h : ∀ i, carry_chain c0 c1 c2 c3 c4 i = 0) :
    c0 = 0 ∧ c1 = 0 ∧ c2 = 0 ∧ c3 = 0 ∧ c4 = 0 := by
  obtain ⟨-, -, -, -, -, b5, b6, -⟩ := carry_chain_carries c0 c1 c2 c3 c4 _ _ _ _ _ _ _
    h0 h1 h2 h3 h4 rfl rfl rfl rfl rfl rfl rfl
  have z0 := h 0; have z1 := h 1; have z2 := h 2; have z3 := h 3; have z4 := h 4
  simp only [carry_chain, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at z0 z1 z2 z3 z4
  omega

lemma two_pow_255 : (2 : ZMod _root_.p) ^ 255 = 19 := by
  have hp : (2 : ℕ) ^ 255 = _root_.p + 19 := by norm_num [_root_.p]
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self, zero_add]
    using congrArg (fun n : ℕ => (n : ZMod _root_.p)) hp

/-- The chain trades `2^255` in the top limb for `19` in the bottom one. -/
lemma carry_chain_value (c0 c1 c2 c3 c4 : ℕ)
    (h0 : c0 ≤ 693 * 2 ^ 102) (h1 : c1 ≤ 531 * 2 ^ 102) (h2 : c2 ≤ 369 * 2 ^ 102)
    (h3 : c3 ≤ 207 * 2 ^ 102) (h4 : c4 ≤ 45 * 2 ^ 102) :
    decodeFieldElem (carry_chain c0 c1 c2 c3 c4)
      = (c0 : ZMod _root_.p) + (c1 : ZMod _root_.p) * 2 ^ 51 + (c2 : ZMod _root_.p) * 2 ^ 102
        + (c3 : ZMod _root_.p) * 2 ^ 153 + (c4 : ZMod _root_.p) * 2 ^ 204 := by
  obtain ⟨-, -, -, -, -, -, b6, -⟩ := carry_chain_carries c0 c1 c2 c3 c4 _ _ _ _ _ _ _
    h0 h1 h2 h3 h4 rfl rfl rfl rfl rfl rfl rfl
  set d0 := c0 / 2 ^ 51 with e0
  set d1 := (d0 + c1) / 2 ^ 51 with e1
  set d2 := (d1 + c2) / 2 ^ 51 with e2
  set d3 := (d2 + c3) / 2 ^ 51 with e3
  set d4 := (d3 + c4) / 2 ^ 51 with e4
  set d5 := (c0 % 2 ^ 51 + d4 * 19) / 2 ^ 51 with e5
  set d6 := (d5 + (d0 + c1) % 2 ^ 51) / 2 ^ 51 with e6
  have hchain : carry_chain c0 c1 c2 c3 c4
      = ![(c0 % 2 ^ 51 + d4 * 19) % 2 ^ 51, (d5 + (d0 + c1) % 2 ^ 51) % 2 ^ 51,
          d6 % 2 ^ 8 + (d1 + c2) % 2 ^ 51, (d2 + c3) % 2 ^ 51, (d3 + c4) % 2 ^ 51] := by
    simp only [carry_chain, e0, e1, e2, e3, e4, e5, e6]
  have key : c0 + c1 * 2 ^ 51 + c2 * 2 ^ 102 + c3 * 2 ^ 153 + c4 * 2 ^ 204 + 19 * d4
      = (c0 % 2 ^ 51 + d4 * 19) % 2 ^ 51
        + (d5 + (d0 + c1) % 2 ^ 51) % 2 ^ 51 * 2 ^ 51
        + (d6 % 2 ^ 8 + (d1 + c2) % 2 ^ 51) * 2 ^ 102
        + (d2 + c3) % 2 ^ 51 * 2 ^ 153
        + (d3 + c4) % 2 ^ 51 * 2 ^ 204
        + d4 * 2 ^ 255 := by
    rw [Nat.mod_eq_of_lt (show d6 < 2 ^ 8 by omega)]
    omega
  have hcast := congrArg (fun n : ℕ => (n : ZMod _root_.p)) key
  push_cast at hcast
  have v0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 5) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  rw [hchain]
  simp only [decodeFieldElem, Fin.toNat_eq_val, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, v0, v1, v2, v3, v4]
  push_cast
  linear_combination -hcast - (d4 : ZMod _root_.p) * two_pow_255

lemma limb_mul_le {x y : ℕ} (hx : x ≤ 0x18000000000000) (hy : y ≤ 0x18000000000000) :
    x * y ≤ 9 * 2 ^ 102 :=
  calc x * y ≤ 0x18000000000000 * 0x18000000000000 := Nat.mul_le_mul hx hy
    _ = 9 * 2 ^ 102 := by norm_num

lemma limb_mul19_le {x y : ℕ} (hx : x ≤ 0x18000000000000) (hy : y ≤ 0x18000000000000) :
    x * (y * 19) ≤ 171 * 2 ^ 102 :=
  calc x * (y * 19) = x * y * 19 := by ring
    _ ≤ 9 * 2 ^ 102 * 19 := Nat.mul_le_mul_right _ (limb_mul_le hx hy)
    _ = 171 * 2 ^ 102 := by ring


/-! ## The carried product

The columns of `a * b` fed through the chain. `fiat_25519_carry_square` computes
`carry_product_repr a a`, so this sits here rather than in either operation's
proof. -/

/-- `fiat_25519_carry_mul`'s `x<k>` over ℕ; the `uint1` truncation at `x50`
is `% 2`. -/
def carry_product_repr (a b : Fin 5 → ℕ) : Fin 5 → ℕ :=
  let x1 := a 4 * (b 4 * 19)
  let x2 := a 4 * (b 3 * 19)
  let x3 := a 4 * (b 2 * 19)
  let x4 := a 4 * (b 1 * 19)
  let x5 := a 3 * (b 4 * 19)
  let x6 := a 3 * (b 3 * 19)
  let x7 := a 3 * (b 2 * 19)
  let x8 := a 2 * (b 4 * 19)
  let x9 := a 2 * (b 3 * 19)
  let x10 := a 1 * (b 4 * 19)
  let x11 := a 4 * b 0
  let x12 := a 3 * b 1
  let x13 := a 3 * b 0
  let x14 := a 2 * b 2
  let x15 := a 2 * b 1
  let x16 := a 2 * b 0
  let x17 := a 1 * b 3
  let x18 := a 1 * b 2
  let x19 := a 1 * b 1
  let x20 := a 1 * b 0
  let x21 := a 0 * b 4
  let x22 := a 0 * b 3
  let x23 := a 0 * b 2
  let x24 := a 0 * b 1
  let x25 := a 0 * b 0
  let x26 := x25 + (x10 + (x9 + (x7 + x4)))
  let x27 := x26 / 2 ^ 51
  let x28 := x26 % 2 ^ 51
  let x29 := x21 + (x17 + (x14 + (x12 + x11)))
  let x30 := x22 + (x18 + (x15 + (x13 + x1)))
  let x31 := x23 + (x19 + (x16 + (x5 + x2)))
  let x32 := x24 + (x20 + (x8 + (x6 + x3)))
  let x33 := x27 + x32
  let x34 := x33 / 2 ^ 51
  let x35 := x33 % 2 ^ 51
  let x36 := x34 + x31
  let x37 := x36 / 2 ^ 51
  let x38 := x36 % 2 ^ 51
  let x39 := x37 + x30
  let x40 := x39 / 2 ^ 51
  let x41 := x39 % 2 ^ 51
  let x42 := x40 + x29
  let x43 := x42 / 2 ^ 51
  let x44 := x42 % 2 ^ 51
  let x45 := x43 * 19
  let x46 := x28 + x45
  let x47 := x46 / 2 ^ 51
  let x48 := x46 % 2 ^ 51
  let x49 := x47 + x35
  let x50 := x49 / 2 ^ 51 % 2 ^ 8
  let x51 := x49 % 2 ^ 51
  let x52 := x50 + x38
  ![x48, x51, x52, x41, x44]

/-- Which grouping of the products counts as column `k`. -/
lemma carry_product_repr_eq (a b : Fin 5 → ℕ) :
    carry_product_repr a b = carry_chain
      (a 0 * b 0 + (a 1 * (b 4 * 19) + (a 2 * (b 3 * 19) + (a 3 * (b 2 * 19) + a 4 * (b 1 * 19)))))
      (a 0 * b 1 + (a 1 * b 0 + (a 2 * (b 4 * 19) + (a 3 * (b 3 * 19) + a 4 * (b 2 * 19)))))
      (a 0 * b 2 + (a 1 * b 1 + (a 2 * b 0 + (a 3 * (b 4 * 19) + a 4 * (b 3 * 19)))))
      (a 0 * b 3 + (a 1 * b 2 + (a 2 * b 1 + (a 3 * b 0 + a 4 * (b 4 * 19)))))
      (a 0 * b 4 + (a 1 * b 3 + (a 2 * b 2 + (a 3 * b 1 + a 4 * b 0)))) := rfl

/-- Every `a i * b j` with `i + j ≥ 5` sits in column `i + j - 5` scaled by
`19`, which is `2 ^ 255` in the field. -/
lemma product_columns_value (a b : Fin 5 → ℕ) :
    ((a 0 * b 0 + (a 1 * (b 4 * 19) + (a 2 * (b 3 * 19) + (a 3 * (b 2 * 19)
        + a 4 * (b 1 * 19)))) : ℕ) : ZMod _root_.p)
      + ((a 0 * b 1 + (a 1 * b 0 + (a 2 * (b 4 * 19) + (a 3 * (b 3 * 19)
        + a 4 * (b 2 * 19)))) : ℕ) : ZMod _root_.p) * 2 ^ 51
      + ((a 0 * b 2 + (a 1 * b 1 + (a 2 * b 0 + (a 3 * (b 4 * 19)
        + a 4 * (b 3 * 19)))) : ℕ) : ZMod _root_.p) * 2 ^ 102
      + ((a 0 * b 3 + (a 1 * b 2 + (a 2 * b 1 + (a 3 * b 0
        + a 4 * (b 4 * 19)))) : ℕ) : ZMod _root_.p) * 2 ^ 153
      + ((a 0 * b 4 + (a 1 * b 3 + (a 2 * b 2 + (a 3 * b 1 + a 4 * b 0))) : ℕ) : ZMod _root_.p)
        * 2 ^ 204
      = decodeFieldElem a * decodeFieldElem b := by
  have v0 : ((0 : Fin 5) : ℕ) = 0 := rfl
  have v1 : ((1 : Fin 5) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 5) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 5) : ℕ) = 3 := rfl
  have v4 : ((4 : Fin 5) : ℕ) = 4 := rfl
  simp only [decodeFieldElem, Fin.toNat_eq_val, Fin.isValue, v0, v1, v2, v3, v4]
  push_cast
  linear_combination
    (-((a 1 : ZMod _root_.p) * b 4 + (a 2 : ZMod _root_.p) * b 3 + (a 3 : ZMod _root_.p) * b 2
        + (a 4 : ZMod _root_.p) * b 1)
      - ((a 2 : ZMod _root_.p) * b 4 + (a 3 : ZMod _root_.p) * b 3
        + (a 4 : ZMod _root_.p) * b 2) * 2 ^ 51
      - ((a 3 : ZMod _root_.p) * b 4 + (a 4 : ZMod _root_.p) * b 3) * 2 ^ 102
      - (a 4 : ZMod _root_.p) * (b 4 : ZMod _root_.p) * 2 ^ 153) * two_pow_255

/-- Worst case per column: four `19`-scaled products in column 0, none in 4. -/
lemma product_columns_le (a b : Fin 5 → ℕ)
    (ha : ∀ i, a i ≤ 0x18000000000000) (hb : ∀ i, b i ≤ 0x18000000000000) :
    a 0 * b 0 + (a 1 * (b 4 * 19) + (a 2 * (b 3 * 19) + (a 3 * (b 2 * 19) + a 4 * (b 1 * 19))))
        ≤ 693 * 2 ^ 102
      ∧ a 0 * b 1 + (a 1 * b 0 + (a 2 * (b 4 * 19) + (a 3 * (b 3 * 19) + a 4 * (b 2 * 19))))
        ≤ 531 * 2 ^ 102
      ∧ a 0 * b 2 + (a 1 * b 1 + (a 2 * b 0 + (a 3 * (b 4 * 19) + a 4 * (b 3 * 19))))
        ≤ 369 * 2 ^ 102
      ∧ a 0 * b 3 + (a 1 * b 2 + (a 2 * b 1 + (a 3 * b 0 + a 4 * (b 4 * 19)))) ≤ 207 * 2 ^ 102
      ∧ a 0 * b 4 + (a 1 * b 3 + (a 2 * b 2 + (a 3 * b 1 + a 4 * b 0))) ≤ 45 * 2 ^ 102 := by
  have m : ∀ i j, a i * b j ≤ 9 * 2 ^ 102 := fun i j => limb_mul_le (ha i) (hb j)
  have m19 : ∀ i j, a i * (b j * 19) ≤ 171 * 2 ^ 102 := fun i j => limb_mul19_le (ha i) (hb j)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have k1 := m 0 0; have k2 := m19 1 4; have k3 := m19 2 3; have k4 := m19 3 2
    have k5 := m19 4 1; omega
  · have k1 := m 0 1; have k2 := m 1 0; have k3 := m19 2 4; have k4 := m19 3 3
    have k5 := m19 4 2; omega
  · have k1 := m 0 2; have k2 := m 1 1; have k3 := m 2 0; have k4 := m19 3 4
    have k5 := m19 4 3; omega
  · have k1 := m 0 3; have k2 := m 1 2; have k3 := m 2 1; have k4 := m 3 0
    have k5 := m19 4 4; omega
  · have k1 := m 0 4; have k2 := m 1 3; have k3 := m 2 2; have k4 := m 3 1
    have k5 := m 4 0; omega

/-- fiat's tight bound on the carried limbs. -/
lemma carry_product_bounds (a b : Fin 5 → ℕ)
    (ha : ∀ i, a i ≤ 0x18000000000000) (hb : ∀ i, b i ≤ 0x18000000000000) :
    ∀ i, carry_product_repr a b i ≤ 0x8000000000000 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := product_columns_le a b ha hb
  rw [carry_product_repr_eq]
  exact carry_chain_le _ _ _ _ _ h0 h1 h2 h3 h4

/-- `carry_product_repr` represents the product. -/
lemma carry_product_eq_value (a b : Fin 5 → ℕ)
    (ha : ∀ i, a i ≤ 0x18000000000000) (hb : ∀ i, b i ≤ 0x18000000000000) :
    decodeFieldElem (carry_product_repr a b) = decodeFieldElem a * decodeFieldElem b := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := product_columns_le a b ha hb
  rw [carry_product_repr_eq, carry_chain_value _ _ _ _ _ h0 h1 h2 h3 h4]
  exact product_columns_value a b


/-- All-zero product limbs come only from an all-zero operand. -/
lemma carry_product_repr_eq_zero (a b : Fin 5 → ℕ)
    (ha : ∀ i, a i ≤ 0x18000000000000) (hb : ∀ i, b i ≤ 0x18000000000000)
    (h : ∀ i, carry_product_repr a b i = 0) :
    (∀ i, a i = 0) ∨ (∀ i, b i = 0) := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := product_columns_le a b ha hb
  rw [carry_product_repr_eq] at h
  obtain ⟨c0, c1, c2, c3, c4⟩ := carry_chain_eq_zero _ _ _ _ _ h0 h1 h2 h3 h4 h
  simp only [Nat.add_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at c0 c1 c2 c3 c4
  by_cases hb0 : ∀ i, b i = 0
  · exact Or.inr hb0
  · left
    push_neg at hb0
    obtain ⟨j, hj⟩ := hb0
    intro i
    fin_cases i <;> fin_cases j <;> simp_all

end Firedancer.Ref
