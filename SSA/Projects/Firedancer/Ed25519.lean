import Mathlib.Data.Int.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Tactic.NormNum
import Mathlib.Data.ZMod.Basic

/-- The ed25519 field characteristic, `2^255 - 19`. -/
def p := 2^255 - 19

/-- `p` as an integer literal. The `ℕ` subtraction is exact, so the cast can be
pushed through; the carry-chain proofs work over `ℤ` and need it in this form. -/
theorem p_int : (p : ℤ) = 2 ^ 255 - 19 := by simp [p]

theorem p_pos : 0 < (p : ℤ) := by rw [p_int]; norm_num

instance : NeZero p := ⟨by simp [p]⟩

/-- An exact multiple of `p` disappears in `ZMod p`. The serial carry macros
both come with an integer identity of the shape `a = b - k * p` -- `k` is limb
5's overflow for the carry propagate and the conditional subtract's `q` for
`mod_nearly_reduced` -- and this is the step from there to the congruence. -/
theorem intCast_eq_of_sub_mul {a b k : ℤ} (h : a = b - k * (p : ℤ)) :
    ((a : ℤ) : ZMod p) = ((b : ℤ) : ZMod p) := by
  rw [ZMod.intCast_eq_intCast_iff', h]
  simp [Int.sub_emod, Int.mul_emod_left]
