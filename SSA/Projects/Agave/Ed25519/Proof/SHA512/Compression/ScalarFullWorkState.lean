import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullBase

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Spec

/-- The independent specification's working state, indexed by completed rounds. -/
def workState (initial : Spec.State) (w : Nat → Word) : Nat → Spec.State
  | 0 => initial
  | n + 1 => Spec.round (workState initial w n) (w n) (constants.toList.getD n 0)

theorem workState_eq_roundsFrom (initial : Spec.State) (words : List Word) (n : Nat) :
    workState initial (fun r => words.getD r 0) n = roundsFrom initial words 0 n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [workState, roundsFrom, Nat.zero_add, ih]

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
