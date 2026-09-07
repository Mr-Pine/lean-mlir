import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_subborrowx_u51
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- One 51-bit subtract-with-borrow step, over the limbs it computes rather than
the 64-bit difference computing them: `*o₁` is a reduced limb and `*o₂` says
whether the subtraction wrapped, so that
`low + c + b = a + 2 ^ 51 * borrow`.

The implications are the contract, for the same reason as in
`fiat_25519_addcarryx_u51_spec` -- outside it the difference and the borrow byte
do not determine the result. They are stated over `c + b` rather than as fiat's
`c ≤ 1`, `b < 2 ^ 51` because that is what the two cases actually need: `1 ≤`
keeps the unwrapped difference inside a limb, and `≤ 2 ^ 51` keeps the wrapped
one within one borrow. It also admits `a = 2 ^ 51`, which `LimbBounds` allows. -/
abbrev fiat_25519_subborrowx_u51_spec (o₁ o₂ : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) : Prop :=
  let invocation := runFunction (fiat_25519_subborrowx_u51.denote
    (Ctxt.Valuation.ofHVector [.value b, .value a, .value c, .value o₂, .value o₁]ₕ))
  let result := StateT.run invocation s

  a.toNat < 2 ^ 51 + (c.toNat + b.toNat) → 1 ≤ c.toNat + b.toNat →
  c.toNat + b.toNat ≤ 2 ^ 51 →
  ∃ (low : BitVec 64) (borrow : BitVec 8),
    low.toNat < 2 ^ 51
    ∧ low.toNat + c.toNat + b.toNat = a.toNat + 2 ^ 51 * borrow.toNat
    ∧ ∃ s' : GlobalState, result = .value ([]ₕ, s')
      ∧ ({ s with mem := (s.mem.splice o₁ low).splice o₂ borrow } : GlobalState) ≈ s'

/-! The spec states the result as `lo + (c + b) = a + n * bo`, the form limb
arithmetic composes in, mirroring `fiat_25519_addcarryx_u51_spec`. These read
one digit back out. `n * bo` is nonlinear, so both go through the two cases the
borrow can take rather than straight to `omega`. -/

/-- The borrow is set exactly when the subtraction went below zero. -/
theorem borrow_eq_of_split {lo d a n bo : ℕ} (hlo : lo < n) (hbo : bo ≤ 1)
    (h : lo + d = a + n * bo) : bo = if a < d then 1 else 0 := by
  obtain rfl | rfl : bo = 0 ∨ bo = 1 := by omega
  · rw [Nat.mul_zero] at h; split <;> omega
  · rw [Nat.mul_one] at h; split <;> omega

/-- ... and the limb is the difference, brought back up by `n` when it did. -/
theorem limb_eq_of_split {lo d a n bo : ℕ} (h : lo + d = a + n * bo) :
    lo = a + n * bo - d := by omega

end Firedancer.Ref
