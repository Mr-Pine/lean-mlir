import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Field
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareWord

/-! Word schedule, bounds, and field value for repeated squaring. The exact
pointer-program execution is proved separately in Pow2k. -/
namespace Agave.Ed25519.Encoding.Decompress.Execution.Pow2k
open SerialFieldMul

def iterateSquare : Nat → Words → Words
  | 0, a => a
  | n + 1, a => iterateSquare n (SerialPoint.squareMachine a)

/-- The square loop keeps every limb within the caller's tight bound. -/
theorem iterateSquare_tight (n : Nat) (a : Words)
    (ha : SerialPoint.Tight (unsigned a)) :
    SerialPoint.Tight (unsigned (iterateSquare n a)) := by
  induction n generalizing a with
  | zero => exact ha
  | succ n ih =>
    exact ih _ (SerialPoint.squareMachine_tight a (SerialPoint.tight_bounded _ ha))

/-- Field value of the concrete repeated square schedule. -/
theorem iterateSquare_value (n : Nat) (a : Words)
    (ha : SerialPoint.Tight (unsigned a)) :
    wordValue (iterateSquare n a) = wordValue a ^ (2 ^ n) := by
  induction n generalizing a with
  | zero => simp [iterateSquare]
  | succ n ih =>
    rw [iterateSquare, ih _ (SerialPoint.squareMachine_tight a (SerialPoint.tight_bounded _ ha))]
    have hs : wordValue (SerialPoint.squareMachine a) = wordValue a ^ 2 :=
      SerialPoint.squareMachine_value a (SerialPoint.tight_bounded _ ha)
    rw [hs, ← pow_mul, pow_succ]
    congr 1
    omega

end Agave.Ed25519.Encoding.Decompress.Execution.Pow2k
