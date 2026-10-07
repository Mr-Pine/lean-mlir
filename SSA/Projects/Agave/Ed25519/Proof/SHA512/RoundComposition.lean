import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec

/-! Pure composition of the two source-shaped scalar round expressions.
The general segment theorems allow short RIR cut points to be reused at any
round index. They do not assert an execution equation for imported code.
-/

namespace Agave.Ed25519.SHA512.Spec

open Agave.Ed25519.Bridge.Challenge

def softRoundsFrom (s : State) (words : List Word) (start : Nat) : Nat → State
  | 0 => s
  | n + 1 => softRound (softRoundsFrom s words start n)
      (words.getD (start + n) 0) (constants.toList.getD (start + n) 0)

def avxRoundsFrom (s : State) (words : List Word) (start : Nat) : Nat → State
  | 0 => s
  | n + 1 => avxRound (avxRoundsFrom s words start n)
      (constants.toList.getD (start + n) 0 + words.getD (start + n) 0)

theorem softRoundsFrom_eq (s : State) (words : List Word) (start n : Nat) :
    softRoundsFrom s words start n = roundsFrom s words start n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [softRoundsFrom, roundsFrom, ih, softRound_eq_round]

theorem avxRoundsFrom_eq (s : State) (words : List Word) (start n : Nat) :
    avxRoundsFrom s words start n = roundsFrom s words start n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [avxRoundsFrom, roundsFrom, ih, avxRound_eq_round]

/-- Reusable two-round cut point, matching one AVX schedule-pair iteration. -/
theorem avxPair_eq (s : State) (words : List Word) (start : Nat) :
    avxRound
      (avxRound s (constants.toList.getD start 0 + words.getD start 0))
      (constants.toList.getD (start + 1) 0 + words.getD (start + 1) 0) =
    roundsFrom s words start 2 := by
  simp [roundsFrom, avxRound_eq_round]

def softCompression (s : State) (block : Bytes) : State :=
  feedForward s (softRoundsFrom s (schedule block) 0 80)

def avxCompression (s : State) (block : Bytes) : State :=
  feedForward s (avxRoundsFrom s (schedule block) 0 80)

/-- Complete eighty-round equality is independent of globals, memory,
readiness and hardware feature detection. The still-separate MLIR proof
must identify each backend's execution result with these expressions. -/
theorem softCompression_eq (s : State) (block : Bytes) :
    softCompression s block = compressBlock s block := by
  simp only [softCompression, compressBlock, softRoundsFrom_eq]

theorem avxCompression_eq (s : State) (block : Bytes) :
    avxCompression s block = compressBlock s block := by
  simp only [avxCompression, compressBlock, avxRoundsFrom_eq]

theorem backend_choice_eq (useAvx : Bool) (s : State) (block : Bytes) :
    (if useAvx then avxCompression s block else softCompression s block) =
      compressBlock s block := by
  cases useAvx <;> simp [softCompression_eq, avxCompression_eq]

end Agave.Ed25519.SHA512.Spec
