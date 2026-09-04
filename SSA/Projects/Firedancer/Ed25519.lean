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

/-- `√-1` in `ZMod p`, the constant ed25519 calls `sqrt(-1)` and Firedancer
stores in the global `@fd_f25519_sqrtm1`. It exists because `p ≡ 5 mod 8`, and
this is the representative with an even canonical form. -/
def sqrtm1 : ZMod p :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752

/-- ... and it really is one, so the literal above is checked rather than
asserted. -/
theorem sqrtm1_sq : sqrtm1 ^ 2 = -1 := by decide +kernel

/-- An exact multiple of `p` disappears in `ZMod p`. The serial carry macros
both come with an integer identity of the shape `a = b - k * p` -- `k` is limb
5's overflow for the carry propagate and the conditional subtract's `q` for
`mod_nearly_reduced` -- and this is the step from there to the congruence. -/
theorem intCast_eq_of_sub_mul {a b k : ℤ} (h : a = b - k * (p : ℤ)) :
    ((a : ℤ) : ZMod p) = ((b : ℤ) : ZMod p) := by
  rw [ZMod.intCast_eq_intCast_iff', h]
  simp [Int.sub_emod, Int.mul_emod_left]
