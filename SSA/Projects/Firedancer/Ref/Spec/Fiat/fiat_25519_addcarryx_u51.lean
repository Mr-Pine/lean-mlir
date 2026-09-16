import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Fiat.fiat_25519_addcarryx_u51
import SSA.Projects.Firedancer.Ref.Spec.F25519

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- One 51-bit add-with-carry step, over the limbs it computes rather than the
64-bit `and`/`shift` computing them: the pair written out is the base-`2 ^ 51`
splitting of `c + a + b`, with `*o₁` the reduced limb.

The three implications are fiat's contract. They guard the statement rather than
weakening its conclusion because the carry is truncated to 8 bits and the sum to
64: outside the contract the two words do not determine the sum, so there is no
limb-level claim left to make. -/
abbrev fiat_25519_addcarryx_u51_spec (o₁ o₂ : Pointer) (c : BitVec 8) (a b : BitVec 64)
    (s : GlobalState) : Prop :=
  let invocation :=
    runFunction
      (fiat_25519_addcarryx_u51.denote
        (Ctxt.Valuation.ofHVector [.value b, .value a, .value c, .value o₂, .value o₁]ₕ))
  let result := StateT.run invocation s
  c.toNat ≤ 1 →
    a.toNat < 2 ^ 51 →
    b.toNat < 2 ^ 51 →
    ∃ (low : BitVec 64) (carry : BitVec 8),
      low.toNat < 2 ^ 51 ∧
        low.toNat + 2 ^ 51 * carry.toNat = c.toNat + a.toNat + b.toNat ∧
        ∃ s' : GlobalState,
          result = .value ([]ₕ, s') ∧
            ({ s with mem := (s.mem.splice o₁ low).splice o₂ carry } : GlobalState) ≈ s'

/-! The spec states the result as `lo + n * hi = S`, the form limb arithmetic
composes in. These read one digit back out. -/

/-- The reduced limb is the sum's low digit. -/
theorem eq_mod_of_split {lo hi n S : ℕ} (hlo : lo < n) (h : lo + n * hi = S) : lo = S % n := by
  subst h; rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlo]

/-- The carry is its high digit. -/
theorem eq_div_of_split {lo hi n S : ℕ} (hlo : lo < n) (h : lo + n * hi = S) : hi = S / n := by
  subst h
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt hlo), Nat.div_eq_of_lt hlo, Nat.zero_add]

end Firedancer.Ref
