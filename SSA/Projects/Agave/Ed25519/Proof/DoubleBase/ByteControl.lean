import SSA.Projects.RIR.Semantics.Operations.Scalar
import Mathlib

/-! Exact byte arithmetic used by both compiler CFGs. These finite-domain
theorems are checked by kernel reduction, without native_decide or new axioms.
They cover all 256 digit bytes, including zero and both signed boundaries.
The NAF theorem discharges the single excluded byte (-128) for table indexing.
-/
namespace Agave.Ed25519.DoubleBase

open LeanMLIR.RIR

/-- Both CFGs use `llvm.scmp.i8.i8` and switch on -1,0,1. -/
theorem signed_compare_byte : ∀ v : BitVec 8,
    (Operation.cmp true (.value v) (.value 0) : PoisonOr (BitVec 8)) =
      .value (BitVec.ofInt 8 (Int.sign v.toInt)) := by
  decide +kernel

/-- The default/unreachable successor of each signed-digit switch is unreachable
for every nonpoison input byte, not just well-formed NAF digits. -/
theorem signed_compare_byte_range : ∀ v : BitVec 8,
    (Operation.cmp true (.value v) (.value 0) : PoisonOr (BitVec 8)) = .value (-1) ∨
    (Operation.cmp true (.value v) (.value 0) : PoisonOr (BitVec 8)) = .value 0 ∨
    (Operation.cmp true (.value v) (.value 0) : PoisonOr (BitVec 8)) = .value 1 := by
  decide +kernel

/-- Source branches use wrapping i8 negation for negative digits, then sext to
i64 and logical shift by one. This is intentionally not defined as mathematical
absolute value: the -128 case would disagree. -/
def compiledLookup (v : BitVec 8) : Nat :=
  let magnitude := if v.slt 0 then -v else v
  (magnitude.signExtend 64 >>> 1).toNat

theorem compiledLookup_correct : ∀ v : BitVec 8, v ≠ 128#8 →
    compiledLookup v = v.toInt.natAbs / 2 := by
  decide +kernel

/-- Explicitly preserve the exceptional behavior instead of silently treating
byte negation as unbounded mathematical negation. -/
theorem compiledLookup_neg128 : compiledLookup 128#8 = 9223372036854775744 := by
  rfl

/-- The small table's emitted unsigned i8 comparison exactly guards index<8. -/
theorem compiledLookup_width5 : ∀ v : BitVec 8,
    -16 < v.toInt → v.toInt < 16 →
    (if v.slt 0 then -v else v).ult 16 = true ∧ compiledLookup v < 8 := by
  decide +kernel

/-- The precomputed basepoint table has 64 entries for width-eight digits. -/
theorem compiledLookup_width8 : ∀ v : BitVec 8,
    -128 < v.toInt → v.toInt < 128 → compiledLookup v < 64 := by
  decide +kernel

end Agave.Ed25519.DoubleBase
