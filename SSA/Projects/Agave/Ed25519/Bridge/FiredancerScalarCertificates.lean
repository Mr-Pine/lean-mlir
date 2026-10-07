import SSA.Projects.Agave.Ed25519.Bridge.FiredancerScalarArithmetic

/-!
Closed arithmetic proofs for representative boundary digests. Every theorem
reduces the exact LLVM source expression in Lean's kernel and establishes the
canonical residue, including definedness of all flagged source operations.
These finite instances do not establish universal reducer correctness.
-/

namespace Agave.Ed25519.Bridge

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The all-zero digest returns the canonical zero scalar. -/
theorem firedancerScalarCanonical_zero : FiredancerScalarCanonicalAt 0 := by
  decide +kernel

/-- A canonical scalar immediately below L is preserved. -/
theorem firedancerScalarCanonical_order_sub_one :
    FiredancerScalarCanonicalAt (BitVec.ofNat 512 (subgroupOrder - 1)) := by
  decide +kernel

/-- The order itself reduces to zero. -/
theorem firedancerScalarCanonical_order :
    FiredancerScalarCanonicalAt (BitVec.ofNat 512 subgroupOrder) := by
  decide +kernel

/-- Crossing the order boundary produces the canonical one scalar. -/
theorem firedancerScalarCanonical_order_add_one :
    FiredancerScalarCanonicalAt (BitVec.ofNat 512 (subgroupOrder + 1)) := by
  decide +kernel

/-- The high-bit boundary exercises the full 64-byte input. -/
theorem firedancerScalarCanonical_high_bit :
    FiredancerScalarCanonicalAt (BitVec.ofNat 512 (2 ^ 511)) := by
  decide +kernel

/-- The maximal digest exercises all input words and high signed carry paths. -/
theorem firedancerScalarCanonical_max :
    FiredancerScalarCanonicalAt (BitVec.ofNat 512 (2 ^ 512 - 1)) := by
  decide +kernel

end Agave.Ed25519.Bridge
