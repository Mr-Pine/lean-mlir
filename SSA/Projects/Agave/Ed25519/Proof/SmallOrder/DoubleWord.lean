import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareWord
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.WordRefinement

/-! Word-level completed doubling. The emitted unflagged additions and biased
subtractions implement this schedule; tight input coordinates establish every
natural-subtraction and field-multiplication bound used in its interpretation.
Linking the arithmetic instruction slice to this schedule remains separate. -/
namespace Agave.Ed25519.SmallOrder
open SerialPoint SerialFieldMul PointArithmetic

/-- Four square calls and the exact completed-coordinate arithmetic schedule. -/
def doubleWord (P : WordPoint) : WordPoint :=
  let xx := squareMachine P.X
  let yy := squareMachine P.Y
  let zz := squareMachine P.Z
  let sum := addWord yy xx
  let diff := subWord yy xx
  ⟨subWord (squareMachine (addWord P.X P.Y)) sum, sum, diff,
    subWord (addWord zz zz) diff⟩

theorem doubleWord_unsigned (P : WordPoint) (h : PointTight (unsignedPoint P)) :
    unsignedPoint (doubleWord P) = doubleCompleted (unsignedPoint P) := by
  have hb := pointTight_bounded _ h
  change Tight (unsigned P.X) ∧ Tight (unsigned P.Y) ∧
    Tight (unsigned P.Z) ∧ Tight (unsigned P.T) at h
  change Bounded (unsigned P.X) ∧ Bounded (unsigned P.Y) ∧
    Bounded (unsigned P.Z) ∧ Bounded (unsigned P.T) at hb
  have hxy := addWord_unsigned P.X P.Y hb.1 hb.2.1
  have hxyB : Bounded (unsigned (addWord P.X P.Y)) := by
    rw [hxy]
    exact add_bounded _ _ h.1 h.2.1
  have hxx := squareMachine_unsigned P.X hb.1
  have hyy := squareMachine_unsigned P.Y hb.2.1
  have hzz := squareMachine_unsigned P.Z hb.2.2.1
  have hxxT := squareMachine_tight P.X hb.1
  have hyyT := squareMachine_tight P.Y hb.2.1
  have hzzT := squareMachine_tight P.Z hb.2.2.1
  have hsum := addWord_unsigned (squareMachine P.Y) (squareMachine P.X)
    (tight_bounded _ hyyT) (tight_bounded _ hxxT)
  have hsumB : Bounded (unsigned (addWord (squareMachine P.Y) (squareMachine P.X))) := by
    rw [hsum]
    exact add_bounded _ _ hyyT hxxT
  have hdiff := subWord_unsigned (squareMachine P.Y) (squareMachine P.X)
    (tight_bounded _ hyyT) (tight_bounded _ hxxT)
  have hdiffB : Bounded (unsigned (subWord (squareMachine P.Y) (squareMachine P.X))) := by
    rw [hdiff]
    exact tight_bounded _ (sub_safe _ _ (tight_bounded _ hyyT) (tight_bounded _ hxxT)).2.2
  have hzz2 := addWord_unsigned (squareMachine P.Z) (squareMachine P.Z)
    (tight_bounded _ hzzT) (tight_bounded _ hzzT)
  have hzz2B : Bounded (unsigned (addWord (squareMachine P.Z) (squareMachine P.Z))) := by
    rw [hzz2]
    exact add_bounded _ _ hzzT hzzT
  have hx := subWord_unsigned (squareMachine (addWord P.X P.Y))
    (addWord (squareMachine P.Y) (squareMachine P.X))
    (tight_bounded _ (squareMachine_tight _ hxyB)) hsumB
  have ht := subWord_unsigned (addWord (squareMachine P.Z) (squareMachine P.Z))
    (subWord (squareMachine P.Y) (squareMachine P.X)) hzz2B hdiffB
  ext <;> simp only [unsignedPoint, doubleWord, doubleCompleted,
    hx, ht, hsum, hdiff, hzz2, hxx, hyy, hzz,
    squareMachine_unsigned _ hxyB, hxy]

theorem doubleWord_bounded (P : WordPoint) (h : PointTight (unsignedPoint P)) :
    PointBounded (unsignedPoint (doubleWord P)) := by
  rw [doubleWord_unsigned P h]
  exact doubleCompleted_bounded _ h

theorem doubleWord_value (P : WordPoint) (h : PointTight (unsignedPoint P)) :
    pointValue (unsignedPoint (asExtendedWord (doubleWord P))) =
      serialDouble (pointValue (unsignedPoint P)) := by
  rw [asExtendedWord_unsigned _ (doubleWord_bounded P h), doubleWord_unsigned P h]
  exact double_value _ h

end Agave.Ed25519.SmallOrder
