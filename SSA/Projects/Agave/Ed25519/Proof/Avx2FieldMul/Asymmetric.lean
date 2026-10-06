import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.Arithmetic
import Mathlib.Tactic.FinCases

/-! Asymmetric coefficient limits for point-operation callers.

The AVX2 source permits a larger left operand than right operand because it
pre-scales right coefficients by 19 in u32. These exact integer limits allow
5.25 radix units on the left and 3.125 on the right. Their product is chosen
so even the largest convolution column remains below 2^63. This includes
several additions/subtractions of the shared reduced coefficient invariant.
It is not a restatement of every real-number bound documented by Rust.
-/
namespace Agave.Ed25519.Avx2FieldMul

/-- 5.25 times the alternating radix (26 bits for even coefficients). -/
def leftLimit (i : Fin 10) : Nat :=
  if i.val % 2 = 0 then 21 * 2 ^ 24 else 21 * 2 ^ 23

/-- 3.125 times the alternating radix; scaling by 19 still fits in u32. -/
def rightLimit (i : Fin 10) : Nat :=
  if i.val % 2 = 0 then 25 * 2 ^ 23 else 25 * 2 ^ 22

def LeftBound (x : Limbs) : Prop := ∀ i, x i < leftLimit i
def RightBound (y : Limbs) : Prop := ∀ i, y i < rightLimit i

/-- The source's sharp column multipliers, in order z0 through z9. -/
def columnMultiplier (k : Fin 10) : Nat := ![249,154,195,118,141,82,87,46,33,10] k

theorem exact_capacity (k : Fin 10) :
    (∑ i : Fin 10, coefficient i (rhsIndex k i) * leftLimit i *
      rightLimit (rhsIndex k i)) = columnMultiplier k * 525 * 2 ^ 46 := by
  fin_cases k <;>
    norm_num [coefficient, rhsIndex, leftLimit, rightLimit, columnMultiplier,
      Fin.sum_univ_succ]

theorem asymmetric_column_bound {x y : Limbs} (hx : LeftBound x)
    (hy : RightBound y) (k : Fin 10) :
    column x y k ≤ columnMultiplier k * 525 * 2 ^ 46 := by
  rw [← exact_capacity]
  apply Finset.sum_le_sum
  intro i _
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.le_of_lt (hx i)))
    (Nat.le_of_lt (hy (rhsIndex k i)))

theorem capacity_lt_i64 (k : Fin 10) :
    columnMultiplier k * 525 * 2 ^ 46 < 2 ^ 63 := by
  fin_cases k <;> norm_num [columnMultiplier]

theorem asymmetric_column_lt_i64 {x y : Limbs} (hx : LeftBound x)
    (hy : RightBound y) (k : Fin 10) : column x y k < 2 ^ 63 :=
  (asymmetric_column_bound hx hy k).trans_lt (capacity_lt_i64 k)

/-- Each node in Rust's sum10 tree sums a subset of ten nonnegative products.
This proves all unsigned and signed 64-bit sum bounds. -/
theorem asymmetric_partial_column_lt_i64 {x y : Limbs}
    (hx : LeftBound x) (hy : RightBound y) (k : Fin 10) (s : Finset (Fin 10)) :
    (∑ i ∈ s, term x y i (rhsIndex k i)) < 2 ^ 63 := by
  have hs : (∑ i ∈ s, term x y i (rhsIndex k i)) ≤ column x y k :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  exact hs.trans_lt (asymmetric_column_lt_i64 hx hy k)

theorem asymmetric_scaled_rhs_lt_u32 {y : Limbs} (hy : RightBound y)
    (j : Fin 10) : 19 * y j < 2 ^ 32 := by
  have hj := hy j
  unfold rightLimit at hj
  split_ifs at hj <;> norm_num at hj ⊢ <;> omega

theorem asymmetric_doubled_lt_u32 {x : Limbs} (hx : LeftBound x)
    (i : Fin 10) : 2 * x i < 2 ^ 32 := by
  have hi := hx i
  unfold leftLimit at hi
  split_ifs at hi <;> norm_num at hi ⊢ <;> omega

private theorem rhsIndex_of_sum (i j : Fin 10) :
    rhsIndex ⟨(i.val + j.val) % 10, Nat.mod_lt _ (by decide)⟩ i = j := by
  apply Fin.ext
  simp only [rhsIndex]
  omega

/-- Every widened individual product is below the signed 64-bit limit. -/
theorem asymmetric_term_lt_i64 {x y : Limbs}
    (hx : LeftBound x) (hy : RightBound y) (i j : Fin 10) :
    term x y i j < 2 ^ 63 := by
  have h := asymmetric_partial_column_lt_i64 hx hy
    ⟨(i.val + j.val) % 10, Nat.mod_lt _ (by decide)⟩ {i}
  simpa only [Finset.sum_singleton, rhsIndex_of_sum] using h

/-- Pre-scaled u32 operands multiply to exactly the corresponding unbounded
term; this identifies the split factors used by `m(twice(x), 19*y)`. -/
theorem split_scaled_term (x y : Limbs) (i j : Fin 10) :
    ((if i.val % 2 = 1 ∧ j.val % 2 = 1 then 2 else 1) * x i) *
      ((if 10 ≤ i.val + j.val then 19 else 1) * y j) = term x y i j := by
  unfold term coefficient
  ring

/-- Narrow multiplication bounds remain accepted by the larger contract. -/
theorem bounded_left {x : Limbs} (hx : Bounded x) : LeftBound x := by
  intro i
  have hi := hx i
  unfold leftLimit
  split_ifs at hi ⊢ <;> norm_num at hi ⊢ <;> omega

theorem bounded_right {x : Limbs} (hx : Bounded x) : RightBound x := by
  intro i
  have hi := hx i
  unfold rightLimit
  split_ifs at hi ⊢ <;> norm_num at hi ⊢ <;> omega

/-- Five shared loose coefficients summed with integer arithmetic fit the
left limit. This is a caller lemma, not a claim about wrapping subtraction. -/
theorem five_loose_left {x : Limbs}
    (hx : ∀ i, x i < 5 * (2 ^ (if i.val % 2 = 0 then 26 else 25) + 2 ^ 18)) :
    LeftBound x := by
  intro i
  have hi := hx i
  unfold leftLimit
  split_ifs at hi ⊢ <;> norm_num at hi ⊢ <;> omega

/-- Three shared loose coefficients fit the u32 pre-scaling right limit. -/
theorem three_loose_right {x : Limbs}
    (hx : ∀ i, x i < 3 * (2 ^ (if i.val % 2 = 0 then 26 else 25) + 2 ^ 18)) :
    RightBound x := by
  intro i
  have hi := hx i
  unfold rightLimit
  split_ifs at hi ⊢ <;> norm_num at hi ⊢ <;> omega

/-- The exact conservative upper bound produced by point doubling's left
operand, retaining its three additive slack contributions. -/
theorem point_caps_left {x : Limbs}
    (hx : ∀ i, x i < 5 * 2 ^ (if i.val % 2 = 0 then 26 else 25) + 3 * 2 ^ 18) :
    LeftBound x := by
  intro i
  have hi := hx i
  unfold leftLimit
  split_ifs at hi ⊢ <;> norm_num at hi ⊢ <;> omega

/-- The exact conservative right-operand bound from point doubling.
This also covers addition's smaller `3*radix + 2*slack` bound. -/
theorem point_caps_right {x : Limbs}
    (hx : ∀ i, x i < 3 * 2 ^ (if i.val % 2 = 0 then 26 else 25) + 3 * 2 ^ 18) :
    RightBound x := by
  intro i
  have hi := hx i
  unfold rightLimit
  split_ifs at hi ⊢ <;> norm_num at hi ⊢ <;> omega

end Agave.Ed25519.Avx2FieldMul
