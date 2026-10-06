import SSA.Projects.Agave.Ed25519.Bridge.FiredancerProgram
import SSA.Projects.Agave.Ed25519.Bridge.FullInput

/-!
# Full-input policy versus the actual parameterized FD execution

The actual SLLVM execution, partial SHA/scalar interface, and Agave byte-input
policy are connected here without importing the Agave execution importer or
the legacy FD proof closure. Execution and cryptographic refinements remain
separate explicit local hypotheses.
-/

namespace Agave.Ed25519.Bridge

open LeanMLIR Firedancer.Common

/-- The policy/execution bridge for all public-key, signature and message bytes.
Only equality of the scalar consumed in this invocation is required from the
hash/reduction boundary. Canonical R is derived on the accepting Agave side. -/
theorem agaveFull_iff_firedancerObserve_success_and_canonical
    (programs : FiredancerShaPrograms) (msg : Pointer) (sz : BitVec 64)
    (sig pk sha : Pointer) (state : GlobalState)
    (a r s : BitVec 256) (message : HashBytes) (fdChallenge : Nat)
    (hexecution : FiredancerExecutionRefines programs msg sz sig pk sha state a r s fdChallenge)
    (calls : FiredancerHashCalls) (reduce : FiredancerReduce) (hash : HashBytes → BitVec 512)
    (hfdChallenge : firedancerChallenge calls reduce (state.mem.live? sha.id) sha.offset
      r a message = some fdChallenge)
    (hchallenge : ChallengeRefines calls reduce hash (state.mem.live? sha.id) sha.offset
      r a message) :
    AgaveFullAccept hash a r s message ↔
      firedancerObserve programs msg sz sig pk sha state = some FD_ED25519_SUCCESS ∧
        CanonicalY r := by
  have hsame : messageChallenge hash r a message = fdChallenge :=
    Option.some.inj (hchallenge.symm.trans hfdChallenge)
  unfold AgaveFullAccept
  rw [hsame]
  exact agave_iff_firedancerObserve_success_and_canonical
    programs msg sz sig pk sha state a r s fdChallenge hexecution

end Agave.Ed25519.Bridge
