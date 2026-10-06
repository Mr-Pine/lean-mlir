import SSA.Projects.Agave.Ed25519.Bridge.Acceptance
import SSA.Projects.Agave.Ed25519.Bridge.SmallOrder

/-!
Unconditional acceptance-specification bridge at the same challenge scalar.
The small-order correspondence is proved in `SmallOrder`, not assumed.

These are curve/encoding theorems. Their connection to executable backends
requires separate implementation-conformance proofs. The shared challenge
parameter explicitly leaves SHA-512 and scalar reduction outside this module.
-/

namespace Agave.Ed25519.Bridge

theorem smallOrderAgreement (a r : BitVec 256) : SmallOrderAgreement a r :=
  fun P _ => eight_nsmul_eq_zero_iff_mem_lowOrder P

/-- Precisely characterize strict Agave versus Firedancer acceptance. -/
theorem agave_iff_firedancer_and_canonical
    (a r : BitVec 256) (s challenge : Nat) :
    AgaveStrictAccept a r s challenge ↔
      FiredancerAccept a r s challenge ∧ CanonicalY r :=
  strict_iff_firedancer_and_canonical (smallOrderAgreement a r)

/-- Every strictly accepted input satisfies Firedancer's acceptance spec. -/
theorem agave_implies_firedancer
    {a r : BitVec 256} {s challenge : Nat}
    (h : AgaveStrictAccept a r s challenge) : FiredancerAccept a r s challenge :=
  strict_implies_firedancer (smallOrderAgreement a r) h

/-- Equality on the canonical-R domain; public-key bytes may be noncanonical. -/
theorem agave_iff_firedancer_of_canonical
    {a r : BitVec 256} {s challenge : Nat} (hcanonical : CanonicalY r) :
    AgaveStrictAccept a r s challenge ↔ FiredancerAccept a r s challenge :=
  strict_iff_firedancer_of_canonical (smallOrderAgreement a r) hcanonical

/-- Every acceptance disagreement is precisely a Firedancer-accepted input
with a noncanonical R coordinate. -/
theorem firedancer_only_iff_noncanonical
    (a r : BitVec 256) (s challenge : Nat) :
    (FiredancerAccept a r s challenge ∧ ¬ AgaveStrictAccept a r s challenge) ↔
      FiredancerAccept a r s challenge ∧ ¬ CanonicalY r := by
  rw [agave_iff_firedancer_and_canonical]
  tauto

end Agave.Ed25519.Bridge
