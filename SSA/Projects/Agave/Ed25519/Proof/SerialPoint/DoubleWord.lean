import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.WordRefinement
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.SquareWord

namespace Agave.Ed25519.SerialPoint
open SerialFieldMul PointArithmetic

/-- Field-word schedule for the completed output of the serial doubling body. -/
def doubleWord (p : WordPoint) : WordPoint :=
  let xx := squareMachine p.X
  let yy := squareMachine p.Y
  let zz := squareMachine p.Z
  let sum := addWord yy xx
  let diff := subWord yy xx
  ⟨subWord (squareMachine (addWord p.X p.Y)) sum, sum, diff,
    subWord (addWord zz zz) diff⟩

/-- Exact word schedule agrees with the natural-limb double, with every bound
for its square and subtraction calls derived from the input point invariant. -/
theorem doubleWord_unsigned (p : WordPoint) (hp : PointTight (unsignedPoint p)) :
    unsignedPoint (doubleWord p) = doubleCompleted (unsignedPoint p) := by
  change Tight (unsigned p.X) ∧ Tight (unsigned p.Y) ∧
    Tight (unsigned p.Z) ∧ Tight (unsigned p.T) at hp
  have hx := tight_bounded _ hp.1
  have hy := tight_bounded _ hp.2.1
  have hz := tight_bounded _ hp.2.2.1
  have hxx := squareMachine_unsigned p.X hx
  have hyy := squareMachine_unsigned p.Y hy
  have hzz := squareMachine_unsigned p.Z hz
  have hxxT := squareMachine_tight p.X hx
  have hyyT := squareMachine_tight p.Y hy
  have hzzT := squareMachine_tight p.Z hz
  have hxxB := tight_bounded _ hxxT
  have hyyB := tight_bounded _ hyyT
  have hzzB := tight_bounded _ hzzT
  have hsum := addWord_unsigned _ _ hyyB hxxB
  have hsumB : Bounded (unsigned (addWord (squareMachine p.Y) (squareMachine p.X))) := by
    rw [hsum]
    exact add_bounded _ _ hyyT hxxT
  have hdiff := subWord_unsigned _ _ hyyB hxxB
  have hdiffB : Bounded (unsigned (subWord (squareMachine p.Y) (squareMachine p.X))) := by
    rw [hdiff]
    exact tight_bounded _ (sub_safe _ _ hyyB hxxB).2.2
  have hxy := addWord_unsigned p.X p.Y hx hy
  have hxyB : Bounded (unsigned (addWord p.X p.Y)) := by
    rw [hxy]
    exact add_bounded _ _ hp.1 hp.2.1
  have hxy2 := squareMachine_unsigned (addWord p.X p.Y) hxyB
  have hxy2B := tight_bounded _ (squareMachine_tight (addWord p.X p.Y) hxyB)
  have hzz2 := addWord_unsigned _ _ hzzB hzzB
  have hzz2B : Bounded (unsigned (addWord (squareMachine p.Z) (squareMachine p.Z))) := by
    rw [hzz2]
    exact add_bounded _ _ hzzT hzzT
  have houtX := subWord_unsigned _ _ hxy2B hsumB
  have houtT := subWord_unsigned _ _ hzz2B hdiffB
  apply Extended.ext <;>
    simp only [unsignedPoint, doubleWord, doubleCompleted,
      houtX, houtT, hsum, hdiff, hxy2, hxy, hzz2, hxx, hyy, hzz]

theorem doubleWord_bounded (p : WordPoint) (hp : PointTight (unsignedPoint p)) :
    PointBounded (unsignedPoint (doubleWord p)) := by
  rw [doubleWord_unsigned p hp]
  exact doubleCompleted_bounded _ hp

theorem doubleWord_value (p : WordPoint) (hp : PointTight (unsignedPoint p)) :
    pointValue (unsignedPoint (asExtendedWord (doubleWord p))) =
      serialDouble (pointValue (unsignedPoint p)) := by
  rw [asExtendedWord_unsigned _ (doubleWord_bounded p hp), doubleWord_unsigned p hp]
  exact double_value _ hp

/-- Final projective→extended conversion uses three multiplications and one square. -/
def projectiveAsExtendedWord (p : WordPoint) : WordPoint :=
  ⟨machine p.X p.Z, machine p.Y p.Z, squareMachine p.Z, machine p.X p.Y⟩

theorem projectiveAsExtendedWord_value (p : WordPoint)
    (hp : PointBounded (unsignedPoint p)) :
    pointValue (unsignedPoint (projectiveAsExtendedWord p)) =
      projectiveAsExtended (pointValue (unsignedPoint p)) := by
  change Bounded (unsigned p.X) ∧ Bounded (unsigned p.Y) ∧
    Bounded (unsigned p.Z) ∧ Bounded (unsigned p.T) at hp
  have hx := machine_unsigned_mul p.X p.Z hp.1 hp.2.2.1
  have hy := machine_unsigned_mul p.Y p.Z hp.2.1 hp.2.2.1
  have hz := squareMachine_unsigned p.Z hp.2.2.1
  have ht := machine_unsigned_mul p.X p.Y hp.1 hp.2.1
  apply Extended.ext <;>
    simp only [pointValue, unsignedPoint, projectiveAsExtendedWord,
      projectiveAsExtended, hx, hy, hz, ht, mul, sq, mul_value, square_value]

theorem projectiveAsExtendedWord_tight (p : WordPoint)
    (hp : PointBounded (unsignedPoint p)) :
    PointTight (unsignedPoint (projectiveAsExtendedWord p)) :=
  ⟨machine_unsigned_tight _ _ hp.1 hp.2.2.1,
    machine_unsigned_tight _ _ hp.2.1 hp.2.2.1,
    squareMachine_tight _ hp.2.2.1,
    machine_unsigned_tight _ _ hp.1 hp.2.1⟩

/-- Projective inputs physically contain only X,Y,Z; no fourth coordinate
or fourth allocation slice is needed for doubling. -/
def ProjectiveTight (p : LimbPoint) : Prop := Tight p.X ∧ Tight p.Y ∧ Tight p.Z

theorem doubleWord_projective_unsigned (p : WordPoint)
    (hp : ProjectiveTight (unsignedPoint p)) :
    unsignedPoint (doubleWord p) = doubleCompleted (unsignedPoint p) := by
  let q : WordPoint := ⟨p.X, p.Y, p.Z, fun _ => 0⟩
  have hq : PointTight (unsignedPoint q) := by
    refine ⟨hp.1, hp.2.1, hp.2.2, ?_⟩
    intro i
    change (0 : Nat) < 2^52
    decide
  simpa only [q, doubleWord, doubleCompleted, unsignedPoint] using doubleWord_unsigned q hq

theorem doubleCompleted_projective_bounded (p : LimbPoint) (hp : ProjectiveTight p) :
    PointBounded (doubleCompleted p) := by
  let q : LimbPoint := ⟨p.X, p.Y, p.Z, fun _ => 0⟩
  have hq : PointTight q := ⟨hp.1, hp.2.1, hp.2.2, fun _ => by
    change (0 : Nat) < 2^52
    decide⟩
  exact doubleCompleted_bounded q hq

end Agave.Ed25519.SerialPoint
