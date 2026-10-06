import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSpec

/-!
# Firedancer return codes and the acceptance bridge

This module extracts exactly the return-code checks supplied by both existing
Firedancer verifier specifications. It needs neither the AVX-512 execution
proof nor its arithmetic dependencies. The checks are premises, not a proof of
execution conformance; `FiredancerReturnChecks` must be obtained from the
existing verifier specification for the actual run under consideration.

No return-code enumeration, successful-run assumption, canonical input,
challenge bound, hash model, or equality of client error codes is needed.
-/

namespace Agave.Ed25519.Bridge

open Firedancer.Common

/-- The acceptance-relevant part of both existing Firedancer verifier specs.
The state/footprint clauses and the final failure-code disjunction are not
needed to extract success. `s` and `challenge` are the integers actually read
by the signature check and double-scalar multiplication respectively. -/
structure FiredancerReturnChecks (a r : BitVec 256) (s challenge : Nat)
    (ret : BitVec 32) : Prop where
  scalar : groupOrder ≤ s → ret = FD_ED25519_ERR_SIG
  publicKey : s < groupOrder → (¬ ∃ A, Firedancer.Common.Encodes a A) →
    ret = FD_ED25519_ERR_PUBKEY
  signatureR : s < groupOrder → (∃ A, Firedancer.Common.Encodes a A) →
    (¬ ∃ R, Firedancer.Common.Encodes r R) → ret = FD_ED25519_ERR_SIG
  decoded : s < groupOrder → ∀ A R : CurvePoint,
    Firedancer.Common.Encodes a A → Firedancer.Common.Encodes r R →
      ((A.x, A.y) ∈ _root_.Ed25519.lowOrder → ret = FD_ED25519_ERR_PUBKEY) ∧
      ((A.x, A.y) ∉ _root_.Ed25519.lowOrder →
        (R.x, R.y) ∈ _root_.Ed25519.lowOrder → ret = FD_ED25519_ERR_SIG) ∧
      ((A.x, A.y) ∉ _root_.Ed25519.lowOrder →
        (R.x, R.y) ∉ _root_.Ed25519.lowOrder →
        (ret = FD_ED25519_SUCCESS ↔ challenge • -A + s • base = R))

/-- The existing specifications' return-path checks characterize successful
acceptance, including malformed encodings and noncanonical signature scalars. -/
theorem firedancer_success_iff_accept
    {a r : BitVec 256} {s challenge : Nat} {ret : BitVec 32}
    (hchecks : FiredancerReturnChecks a r s challenge ret) :
    ret = FD_ED25519_SUCCESS ↔ FiredancerAccept a r s challenge := by
  classical
  have hsig : FD_ED25519_SUCCESS ≠ FD_ED25519_ERR_SIG := by decide
  have hpk : FD_ED25519_SUCCESS ≠ FD_ED25519_ERR_PUBKEY := by decide
  constructor
  · intro hsuccess
    have hs : s < groupOrder := by
      by_contra h
      exact hsig (hsuccess.symm.trans (hchecks.scalar (Nat.le_of_not_gt h)))
    have ha : ∃ A, Firedancer.Common.Encodes a A := by
      by_contra h
      exact hpk (hsuccess.symm.trans (hchecks.publicKey hs h))
    have hr : ∃ R, Firedancer.Common.Encodes r R := by
      by_contra h
      exact hsig (hsuccess.symm.trans (hchecks.signatureR hs ha h))
    obtain ⟨A, hA⟩ := ha
    obtain ⟨R, hR⟩ := hr
    obtain ⟨hlowA, hlowR, hequation⟩ := hchecks.decoded hs A R hA hR
    have hnA : (A.x, A.y) ∉ _root_.Ed25519.lowOrder :=
      fun h => hpk (hsuccess.symm.trans (hlowA h))
    have hnR : (R.x, R.y) ∉ _root_.Ed25519.lowOrder :=
      fun h => hsig (hsuccess.symm.trans (hlowR hnA h))
    exact ⟨hs, A, R, hA, hR, hnA, hnR, (hequation hnA hnR).mp hsuccess⟩
  · rintro ⟨hs, A, R, hA, hR, hnA, hnR, heq⟩
    exact ((hchecks.decoded hs A R hA hR).2.2 hnA hnR).mpr heq

/-- A strict acceptance policy agrees with the actual Firedancer return code
once that run supplies the existing specification's checks. Canonical R is
an additional policy check; no canonical-public-key premise is present. -/
theorem agave_iff_firedancer_success_and_canonical
    {a r : BitVec 256} {s challenge : Nat} {ret : BitVec 32}
    (hchecks : FiredancerReturnChecks a r s challenge ret) :
    AgaveStrictAccept a r s challenge ↔
      ret = FD_ED25519_SUCCESS ∧ CanonicalY r := by
  rw [firedancer_success_iff_accept hchecks]
  exact agave_iff_firedancer_and_canonical a r s challenge

/-- Exact equivalence on the canonical-R domain, with all other malformed
inputs still in scope. -/
theorem agave_iff_firedancer_success_of_canonical
    {a r : BitVec 256} {s challenge : Nat} {ret : BitVec 32}
    (hchecks : FiredancerReturnChecks a r s challenge ret) (hcanonical : CanonicalY r) :
    AgaveStrictAccept a r s challenge ↔ ret = FD_ED25519_SUCCESS := by
  rw [agave_iff_firedancer_success_and_canonical hchecks, and_iff_left hcanonical]

end Agave.Ed25519.Bridge
