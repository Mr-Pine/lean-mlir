/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.Firedancer.Ref.Spec.F25519

@[expose] public section

namespace Firedancer.Ref

open LeanMLIR SLLVM

/-- The 40-byte field elements at `p` and `q` do not overlap. -/
abbrev FieldApart (p q : Pointer) : Prop :=
  p.id ≠ q.id ∨ p.offsetInBits + 320 ≤ q.offsetInBits ∨ q.offsetInBits + 320 ≤ p.offsetInBits

end Firedancer.Ref
