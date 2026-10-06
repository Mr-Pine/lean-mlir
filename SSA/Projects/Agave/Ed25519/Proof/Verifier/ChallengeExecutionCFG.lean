import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionProgram
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionTermination
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

/-! Kernel-checked control-flow facts about the actual extracted challenge.
The finite rank proves termination of the CFG even for arbitrary primitive
effects. It deliberately does not claim absence of memory or primitive poison.
-/

namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR

def blockRank : Fin 8 → Nat
  | ⟨0, _⟩ => 7
  | ⟨1, _⟩ => 6
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 3
  | ⟨6, _⟩ => 2
  | _ => 1

theorem blockRank_positive (k : Fin 8) : 0 < blockRank k := by
  fin_cases k <;> decide

/-- The numerical order of blocks is not a topological order: block 4 jumps
back to block 3. This independently checked ranking still strictly decreases. -/
theorem program_ranked (p : Primitives) (g : Globals) (k : Fin 8) :
    exitRanked blockRank (blockRank k) ((program p g).blocks k).exit := by
  fin_cases k
  · change 2 < 7 ∧ 6 < 7
    decide
  · change 4 < 6 ∧ 5 < 6
    decide
  · change 1 < 2
    decide
  · change 2 < 4 ∧ 3 < 4
    decide
  · change 4 < 5
    decide
  · change 2 < 3
    decide
  · change 1 < 2
    decide
  · change True
    trivial

/-- Seven basic-block executions suffice on every input, including arbitrary
message lengths and arbitrary external callee effects. A poison result is
still poison; this statement only excludes running out of CFG fuel. -/
theorem program_no_fuel_exhaustion (p : Primitives) (g : Globals)
    (args : Vals [.ptr, .ptr, .ptr, .ptr, .bv 64]) (state after : GlobalState) :
    (program p g).eval 7 args state ≠ .value (none, after) := by
  exact evalFrom_fuel_sufficient (program p g) blockRank blockRank_positive
    (program_ranked p g) 7 _ _ state after (Nat.le_refl 7)

end Agave.Ed25519.Verifier.Execution.Challenge
