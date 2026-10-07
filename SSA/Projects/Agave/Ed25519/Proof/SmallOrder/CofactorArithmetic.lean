import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Refinement

/-! Arithmetic of the three doublings used at k = 3. The first two loop
iterations only materialize XYZ; T is dead until the final conversion. This
module proves that omission harmless, but does not assert RIR execution. -/
namespace Agave.Ed25519.SmallOrder
open SerialPoint PointArithmetic

/-- Logical extended representative of one loop iteration. -/
def twice (P : LimbPoint) : LimbPoint := asExtended (doubleCompleted P)

def eightTimes (P : LimbPoint) : LimbPoint := twice (twice (twice P))

theorem twice_tight (P : LimbPoint) (h : PointTight P) : PointTight (twice P) :=
  double_tight P h

theorem eightTimes_tight (P : LimbPoint) (h : PointTight P) :
    PointTight (eightTimes P) :=
  twice_tight _ (twice_tight _ (twice_tight P h))

theorem eightTimes_value (P : LimbPoint) (h : PointTight P) :
    pointValue (eightTimes P) =
      serialDouble (serialDouble (serialDouble (pointValue P))) := by
  unfold eightTimes
  rw [show pointValue (twice (twice (twice P))) =
      serialDouble (pointValue (twice (twice P))) from
    double_value _ (twice_tight _ (twice_tight P h))]
  rw [show pointValue (twice (twice P)) = serialDouble (pointValue (twice P)) from
    double_value _ (twice_tight P h)]
  rw [show pointValue (twice P) = serialDouble (pointValue P) from double_value P h]

/-- The projective double never observes the omitted T coordinate. -/
theorem doubleCompleted_ignores_T (P : LimbPoint) (t : SerialFieldMul.Limbs) :
    doubleCompleted {P with T := t} = doubleCompleted P := rfl

/-- The first three products match the emitted `as_projective` conversion. -/
theorem twice_xyz (P : LimbPoint) :
    (twice P).X = mul (doubleCompleted P).X (doubleCompleted P).T ∧
    (twice P).Y = mul (doubleCompleted P).Y (doubleCompleted P).Z ∧
    (twice P).Z = mul (doubleCompleted P).Z (doubleCompleted P).T :=
  ⟨rfl, rfl, rfl⟩

end Agave.Ed25519.SmallOrder
