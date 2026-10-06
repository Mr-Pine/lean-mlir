import SSA.Projects.Agave.Ed25519.Spec.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Integer convolution underlying the pinned AVX2 multiplication routine.
The definitions in this file are mathematical specifications. An execution
bridge is required before applying these theorems to compiler-generated RIR. -/

namespace Agave.Ed25519.Avx2FieldMul

abbrev Limbs := Fin 10 → Nat

abbrev exponent := Field.exponent
abbrev decode := Field.decode10
abbrev modulus := Field.p

/-- The odd/odd factor accounts for the mixed radix; 19 folds 2^255. -/
def coefficient (i j : Fin 10) : Nat :=
  (if i.val % 2 = 1 ∧ j.val % 2 = 1 then 2 else 1) *
  (if 10 ≤ i.val + j.val then 19 else 1)

def rhsIndex (k i : Fin 10) : Fin 10 :=
  ⟨(k.val + 10 - i.val) % 10, Nat.mod_lt _ (by decide)⟩

def term (x y : Limbs) (i j : Fin 10) : Nat :=
  coefficient i j * x i * y j

def column (x y : Limbs) (k : Fin 10) : Nat :=
  ∑ i, term x y i (rhsIndex k i)

/-- Every actual Rust convolution uses exactly one product for each x limb. -/
theorem column_expansion (x y : Limbs) (k : Fin 10) :
    column x y k = ∑ i, coefficient i (rhsIndex k i) * x i * y (rhsIndex k i) := rfl

/-- The integer quotient discarded when reducing the convolution modulo p. -/
def quotient (x y : Limbs) : Nat :=
  ∑ i : Fin 10, ∑ j : Fin 10,
    if 10 ≤ i.val + j.val then
      x i * y j * (if i.val % 2 = 1 ∧ j.val % 2 = 1 then 2 else 1) *
        2 ^ (51 * ((i.val + j.val - 10) / 2) + 26 * ((i.val + j.val - 10) % 2))
    else 0

private theorem decode_expansion (x : Limbs) : decode x =
    x 0 * 1 + x 1 * 67108864 + x 2 * 2251799813685248 + x 3 * 151115727451828646838272 + x 4 * 5070602400912917605986812821504 + x 5 * 340282366920938463463374607431768211456 + x 6 * 11417981541647679048466287755595961091061972992 + x 7 * 766247770432944429179173513575154591809369561091801088 + x 8 * 25711008708143844408671393477458601640355247900524685364822016 + x 9 * 1725436586697640946858688965569256363112777243042596638790631055949824 := by
  norm_num [decode, Field.decode10, Field.exponent, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_0 (x y : Limbs) : column x y 0 =
    1 * x 0 * y 0 + 38 * x 1 * y 9 + 19 * x 2 * y 8 + 38 * x 3 * y 7 + 19 * x 4 * y 6 + 38 * x 5 * y 5 + 19 * x 6 * y 4 + 38 * x 7 * y 3 + 19 * x 8 * y 2 + 38 * x 9 * y 1 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_1 (x y : Limbs) : column x y 1 =
    1 * x 0 * y 1 + 1 * x 1 * y 0 + 19 * x 2 * y 9 + 19 * x 3 * y 8 + 19 * x 4 * y 7 + 19 * x 5 * y 6 + 19 * x 6 * y 5 + 19 * x 7 * y 4 + 19 * x 8 * y 3 + 19 * x 9 * y 2 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_2 (x y : Limbs) : column x y 2 =
    1 * x 0 * y 2 + 2 * x 1 * y 1 + 1 * x 2 * y 0 + 38 * x 3 * y 9 + 19 * x 4 * y 8 + 38 * x 5 * y 7 + 19 * x 6 * y 6 + 38 * x 7 * y 5 + 19 * x 8 * y 4 + 38 * x 9 * y 3 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_3 (x y : Limbs) : column x y 3 =
    1 * x 0 * y 3 + 1 * x 1 * y 2 + 1 * x 2 * y 1 + 1 * x 3 * y 0 + 19 * x 4 * y 9 + 19 * x 5 * y 8 + 19 * x 6 * y 7 + 19 * x 7 * y 6 + 19 * x 8 * y 5 + 19 * x 9 * y 4 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_4 (x y : Limbs) : column x y 4 =
    1 * x 0 * y 4 + 2 * x 1 * y 3 + 1 * x 2 * y 2 + 2 * x 3 * y 1 + 1 * x 4 * y 0 + 38 * x 5 * y 9 + 19 * x 6 * y 8 + 38 * x 7 * y 7 + 19 * x 8 * y 6 + 38 * x 9 * y 5 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_5 (x y : Limbs) : column x y 5 =
    1 * x 0 * y 5 + 1 * x 1 * y 4 + 1 * x 2 * y 3 + 1 * x 3 * y 2 + 1 * x 4 * y 1 + 1 * x 5 * y 0 + 19 * x 6 * y 9 + 19 * x 7 * y 8 + 19 * x 8 * y 7 + 19 * x 9 * y 6 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_6 (x y : Limbs) : column x y 6 =
    1 * x 0 * y 6 + 2 * x 1 * y 5 + 1 * x 2 * y 4 + 2 * x 3 * y 3 + 1 * x 4 * y 2 + 2 * x 5 * y 1 + 1 * x 6 * y 0 + 38 * x 7 * y 9 + 19 * x 8 * y 8 + 38 * x 9 * y 7 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_7 (x y : Limbs) : column x y 7 =
    1 * x 0 * y 7 + 1 * x 1 * y 6 + 1 * x 2 * y 5 + 1 * x 3 * y 4 + 1 * x 4 * y 3 + 1 * x 5 * y 2 + 1 * x 6 * y 1 + 1 * x 7 * y 0 + 19 * x 8 * y 9 + 19 * x 9 * y 8 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_8 (x y : Limbs) : column x y 8 =
    1 * x 0 * y 8 + 2 * x 1 * y 7 + 1 * x 2 * y 6 + 2 * x 3 * y 5 + 1 * x 4 * y 4 + 2 * x 5 * y 3 + 1 * x 6 * y 2 + 2 * x 7 * y 1 + 1 * x 8 * y 0 + 38 * x 9 * y 9 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

theorem column_9 (x y : Limbs) : column x y 9 =
    1 * x 0 * y 9 + 1 * x 1 * y 8 + 1 * x 2 * y 7 + 1 * x 3 * y 6 + 1 * x 4 * y 5 + 1 * x 5 * y 4 + 1 * x 6 * y 3 + 1 * x 7 * y 2 + 1 * x 8 * y 1 + 1 * x 9 * y 0 := by
  norm_num [column, term, coefficient, rhsIndex, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

private theorem quotient_expansion (x y : Limbs) : quotient x y =
    x 1 * y 9 * 2 + x 2 * y 8 * 1 + x 2 * y 9 * 67108864 + x 3 * y 7 * 2 + x 3 * y 8 * 67108864 + x 3 * y 9 * 4503599627370496 + x 4 * y 6 * 1 + x 4 * y 7 * 67108864 + x 4 * y 8 * 2251799813685248 + x 4 * y 9 * 151115727451828646838272 + x 5 * y 5 * 2 + x 5 * y 6 * 67108864 + x 5 * y 7 * 4503599627370496 + x 5 * y 8 * 151115727451828646838272 + x 5 * y 9 * 10141204801825835211973625643008 + x 6 * y 4 * 1 + x 6 * y 5 * 67108864 + x 6 * y 6 * 2251799813685248 + x 6 * y 7 * 151115727451828646838272 + x 6 * y 8 * 5070602400912917605986812821504 + x 6 * y 9 * 340282366920938463463374607431768211456 + x 7 * y 3 * 2 + x 7 * y 4 * 67108864 + x 7 * y 5 * 4503599627370496 + x 7 * y 6 * 151115727451828646838272 + x 7 * y 7 * 10141204801825835211973625643008 + x 7 * y 8 * 340282366920938463463374607431768211456 + x 7 * y 9 * 22835963083295358096932575511191922182123945984 + x 8 * y 2 * 1 + x 8 * y 3 * 67108864 + x 8 * y 4 * 2251799813685248 + x 8 * y 5 * 151115727451828646838272 + x 8 * y 6 * 5070602400912917605986812821504 + x 8 * y 7 * 340282366920938463463374607431768211456 + x 8 * y 8 * 11417981541647679048466287755595961091061972992 + x 8 * y 9 * 766247770432944429179173513575154591809369561091801088 + x 9 * y 1 * 2 + x 9 * y 2 * 67108864 + x 9 * y 3 * 4503599627370496 + x 9 * y 4 * 151115727451828646838272 + x 9 * y 5 * 10141204801825835211973625643008 + x 9 * y 6 * 340282366920938463463374607431768211456 + x 9 * y 7 * 22835963083295358096932575511191922182123945984 + x 9 * y 8 * 766247770432944429179173513575154591809369561091801088 + x 9 * y 9 * 51422017416287688817342786954917203280710495801049370729644032 := by
  norm_num [quotient, Fin.sum_univ_succ, Nat.add_assoc, Nat.mul_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- Unconditional polynomial identity: no limb bound is needed for the
integer convolution. Bounds enter only when connecting machine arithmetic. -/
theorem convolution_identity (x y : Limbs) :
    decode x * decode y = decode (column x y) + modulus * quotient x y := by
  rw [decode_expansion x, decode_expansion y, decode_expansion (column x y),
    column_0, column_1, column_2, column_3, column_4, column_5, column_6, column_7, column_8, column_9, quotient_expansion]
  norm_num only [modulus, Field.p]
  ring

theorem convolution_mod (x y : Limbs) :
    decode (column x y) % modulus = (decode x * decode y) % modulus := by
  rw [convolution_identity]
  simp

/-- A simple caller bound (one bit of slack in either radix). -/
abbrev Bounded := Field.MulBound

theorem bounded_uniform {x : Limbs} (h : Bounded x) (i : Fin 10) : x i < 2 ^ 27 := by
  have hi := h i
  split_ifs at hi <;> norm_num at hi ⊢ <;> omega

theorem coefficient_le (i j : Fin 10) : coefficient i j ≤ 38 := by
  unfold coefficient
  split_ifs <;> norm_num

theorem term_bound {x y : Limbs} (hx : Bounded x) (hy : Bounded y)
    (i j : Fin 10) : term x y i j ≤ 38 * (2 ^ 27 - 1) ^ 2 := by
  have hxi : x i ≤ 2 ^ 27 - 1 := by have := bounded_uniform hx i; omega
  have hyj : y j ≤ 2 ^ 27 - 1 := by have := bounded_uniform hy j; omega
  calc
    term x y i j ≤ 38 * (2 ^ 27 - 1) * (2 ^ 27 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul (coefficient_le i j) hxi) hyj
    _ = _ := by ring

theorem column_bound {x y : Limbs} (hx : Bounded x) (hy : Bounded y)
    (k : Fin 10) : column x y k < 2 ^ 63 := by
  have h : column x y k ≤ ∑ _i : Fin 10, 38 * (2 ^ 27 - 1) ^ 2 :=
    Finset.sum_le_sum (fun i _ => term_bound hx hy i (rhsIndex k i))
  norm_num at h ⊢
  omega

/-- Multiplication by 19 takes place before widening. Its u32 result is exact. -/
theorem scaled_rhs_lt_u32 {y : Limbs} (hy : Bounded y) (j : Fin 10) :
    19 * y j < 2 ^ 32 := by
  have := bounded_uniform hy j
  norm_num at this ⊢
  omega

/-- Only odd x limbs are doubled before widening. -/
theorem doubled_odd_lt_u32 {x : Limbs} (hx : Bounded x)
    (i : Fin 10) (hi : i.val % 2 = 1) : 2 * x i < 2 ^ 32 := by
  have hb := hx i
  simp [hi] at hb
  norm_num at hb ⊢
  omega

/-- Every subtree in the nonnegative sum10 addition tree is bounded by the
whole convolution column. Hence every addition fits in u64. -/
theorem partial_column_lt_u64 {x y : Limbs} (hx : Bounded x) (hy : Bounded y)
    (k : Fin 10) (s : Finset (Fin 10)) :
    (∑ i ∈ s, term x y i (rhsIndex k i)) < 2 ^ 64 := by
  have hsub : (∑ i ∈ s, term x y i (rhsIndex k i)) ≤ column x y k := by
    exact Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have h := column_bound hx hy k
  norm_num at h ⊢
  omega

end Agave.Ed25519.Avx2FieldMul
