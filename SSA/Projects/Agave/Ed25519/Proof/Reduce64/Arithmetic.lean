import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs
import SSA.Projects.Agave.Ed25519.Spec.Field

/-! Integer correctness of the two parallel carry chains in
`FieldElement2625x4::reduce64`. These theorems do not by themselves connect
this integer calculation to the compiler-generated RIR program. -/
namespace Agave.Ed25519.Reduce64
open Agave.Ed25519.Field

abbrev Columns := Fin 10 → Nat

def t1 (z : Columns) := z 1 + z 0 / 2^26
def t2 (z : Columns) := z 2 + t1 z / 2^25
def t3 (z : Columns) := z 3 + t2 z / 2^26
def t5 (z : Columns) := z 5 + z 4 / 2^26
def t6 (z : Columns) := z 6 + t5 z / 2^25
def t7 (z : Columns) := z 7 + t6 z / 2^26
def t4 (z : Columns) := z 4 % 2^26 + t3 z / 2^25
def u5 (z : Columns) := t5 z % 2^25 + t4 z / 2^26
def t8 (z : Columns) := z 8 + t7 z / 2^25
def t9 (z : Columns) := z 9 + t8 z / 2^26
def carry (z : Columns) := t9 z / 2^25
def u0 (z : Columns) := z 0 % 2^26 + (carry z % 2^26) * 19
def u1 (z : Columns) := t1 z % 2^25 + (carry z / 2^26) * 19 + u0 z / 2^26

def reduce (z : Columns) : Columns :=
  ![u0 z % 2^26, u1 z, t2 z % 2^26, t3 z % 2^25,
    t4 z % 2^26, u5 z, t6 z % 2^26, t7 z % 2^25,
    t8 z % 2^26, t9 z % 2^25]

/-- Exact accounting before applying the field modulus. -/
theorem conservation (z : Columns) :
    decode10 z + carry z * 19 = decode10 (reduce z) + carry z * 2^255 := by
  simp only [decode10, exponent, Fin.sum_univ_succ, reduce, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  norm_num
  have h0 := Nat.mod_add_div (z 0) (2^26)
  have h1 := Nat.mod_add_div (t1 z) (2^25)
  have h2 := Nat.mod_add_div (t2 z) (2^26)
  have h3 := Nat.mod_add_div (t3 z) (2^25)
  have h4 := Nat.mod_add_div (z 4) (2^26)
  have h5 := Nat.mod_add_div (t5 z) (2^25)
  have h6 := Nat.mod_add_div (t6 z) (2^26)
  have h7 := Nat.mod_add_div (t7 z) (2^25)
  have h8 := Nat.mod_add_div (t8 z) (2^26)
  have h9 := Nat.mod_add_div (t9 z) (2^25)
  have h4' := Nat.mod_add_div (t4 z) (2^26)
  have hc := Nat.mod_add_div (carry z) (2^26)
  have hu := Nat.mod_add_div (u0 z) (2^26)
  simp only [u1, u5]
  have ht1 : t1 z = z 1 + z 0 / 2^26 := rfl
  have ht2 : t2 z = z 2 + t1 z / 2^25 := rfl
  have ht3 : t3 z = z 3 + t2 z / 2^26 := rfl
  have ht4 : t4 z = z 4 % 2^26 + t3 z / 2^25 := rfl
  have ht5 : t5 z = z 5 + z 4 / 2^26 := rfl
  have ht6 : t6 z = z 6 + t5 z / 2^25 := rfl
  have ht7 : t7 z = z 7 + t6 z / 2^26 := rfl
  have ht8 : t8 z = z 8 + t7 z / 2^25 := rfl
  have ht9 : t9 z = z 9 + t8 z / 2^26 := rfl
  have htc : carry z = t9 z / 2^25 := rfl
  have htu : u0 z = z 0 % 2^26 + (carry z % 2^26)*19 := rfl
  norm_num at *
  omega


/-- Reduction preserves the residue for arbitrary natural-number columns.
Bounds are needed only when implementing this calculation using machine words. -/
theorem residue (z : Columns) : SameField (decode10 z) (decode10 (reduce z)) := by
  have h := conservation z
  rw [two_pow_255] at h
  have he : decode10 z = decode10 (reduce z) + carry z * p := by nlinarith [h]
  unfold SameField
  rw [he]
  simp

/-- A uniform bound sufficient for every unflagged 64-bit addition. -/
def ColumnsBound (z : Columns) : Prop := ∀ i, z i < 2^63

theorem intermediate_bounds (z : Columns) (h : ColumnsBound z) :
    t1 z < 2^63 + 2^39 ∧ t2 z < 2^63 + 2^39 ∧
    t3 z < 2^63 + 2^39 ∧ t5 z < 2^63 + 2^39 ∧
    t6 z < 2^63 + 2^39 ∧ t7 z < 2^63 + 2^39 ∧
    t8 z < 2^63 + 2^39 ∧ t9 z < 2^63 + 2^39 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6; have h7 := h 7
  have h8 := h 8; have h9 := h 9
  simp only [t1, t2, t3, t5, t6, t7, t8, t9]
  norm_num at *
  omega

/-- The two exceptional odd coefficients still fit the shared loose invariant. -/
theorem output_bounds (z : Columns) (h : ColumnsBound z) :
    ∀ i, reduce z i < 2^(if i.val % 2 = 0 then 26 else 25) + 2^18 := by
  obtain ⟨h1,h2,h3,h5,h6,h7,h8,h9⟩ := intermediate_bounds z h
  intro i
  fin_cases i <;> simp only [reduce, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals norm_num
  all_goals try simp only [u1, u0, u5, carry, t4]
  all_goals norm_num at *
  all_goals omega

/-- Every unflagged addition is exact in an unsigned 64-bit word. -/
theorem no_unsigned_wrap (z : Columns) (h : ColumnsBound z) :
    t1 z < 2^64 ∧ t2 z < 2^64 ∧ t3 z < 2^64 ∧ t5 z < 2^64 ∧
    t6 z < 2^64 ∧ t7 z < 2^64 ∧ t8 z < 2^64 ∧ t9 z < 2^64 := by
  obtain ⟨h1,h2,h3,h5,h6,h7,h8,h9⟩ := intermediate_bounds z h
  norm_num at *
  omega

/-- All flagged adds/multiplies are below the signed 64-bit threshold.
The small bounds additionally justify the final narrowing to 32-bit lanes. -/
theorem small_intermediate_bounds (z : Columns) (h : ColumnsBound z) :
    t4 z < 2^40 ∧ u5 z < 2^26 ∧
    (carry z % 2^26) * 19 < 2^31 ∧
    (carry z / 2^26) * 19 < 2^18 ∧
    u0 z < 2^31 ∧ u1 z < 2^26 := by
  obtain ⟨h1,h2,h3,h5,h6,h7,h8,h9⟩ := intermediate_bounds z h
  simp only [t4, u5, carry, u0, u1]
  norm_num at *
  omega

/-- No result coefficient is lost by the SIMD packing's 64-to-32-bit extraction. -/
theorem output_u32 (z : Columns) (h : ColumnsBound z) (i : Fin 10) :
    reduce z i < 2^32 := by
  have hi := output_bounds z h i
  split_ifs at hi <;> norm_num at hi ⊢ <;> omega

end Agave.Ed25519.Reduce64

