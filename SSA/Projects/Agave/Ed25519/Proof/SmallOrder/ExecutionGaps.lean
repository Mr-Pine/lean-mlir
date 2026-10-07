import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.Linked
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityArithmetic

/-! The remaining small-order execution boundary. These are propositions, not
axioms or proved contracts. In particular exact import and code linkage alone
cannot discharge either verifier leaf. They are kept separate from the local
arithmetic theorems so the unresolved execution work cannot be mistaken for a
newly closed primitive boundary. -/
namespace Agave.Ed25519.SmallOrder.Execution
open LeanMLIR.RIR Verifier.Execution

/-- Still to prove: allocation/copies, two XYZ-only loop iterations, final
XY ZT products, output readback and caller frame of the actual k=3 body.
The lower projective-double body also needs its execution refinement. -/
def CofactorExecutionGap (layout : Dalek.Layout Point Scalar Result) : Prop :=
  Dalek.CofactorContract cofactorProgram.call layout

/-- Still to prove: four multiplication calls, all four byte-store serializers,
both byte-comparison calls, and restoring private stack allocations. The final
AND/black-box suffix is covered separately by `EqualityTail`. -/
def EqualityExecutionGap (layout : Dalek.Layout Point Scalar Result)
    (shared : Verifier.Shared Point Scalar) : Prop :=
  Dalek.SmallOrderEqContract equalityProgram.call layout shared

/-- The arithmetic interpretation of `layout.cofactor` is independent of the
execution gap: it must encode the limb schedule established by `eightTimes`.
No relation to group-theoretic [8]P is assumed or proved by this declaration. -/
def CofactorLayoutGap (layout : Dalek.Layout Point Scalar Result)
    (limbs : Point → SerialPoint.LimbPoint)
    (encode : SerialPoint.LimbPoint → Dalek.PointBytes) : Prop :=
  ∀ point, SerialPoint.PointTight (limbs point) ∧
    layout.point point = encode (limbs point) ∧
    layout.cofactor point = encode (eightTimes (limbs point))

/-- The source small-order predicate must agree with the concrete cofactor
identity equation. This group/representation fact is not hidden in a byte
comparison axiom. -/
def SmallOrderArithmeticGap (shared : Verifier.Shared Point Scalar)
    (cofactor : Point → PointArithmetic.Extended K) : Prop :=
  ∀ point, shared.smallOrder point = true ↔
    crossEqual (cofactor point) ⟨0, 1, 1, 0⟩

end Agave.Ed25519.SmallOrder.Execution
