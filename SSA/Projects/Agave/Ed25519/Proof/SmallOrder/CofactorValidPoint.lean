import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.CofactorArithmetic
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.DoubleWord
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ValidPoint
import SSA.Projects.Agave.Ed25519.Proof.Tables.Dynamic

/-! The exact noncanonical word schedule for cofactor multiplication, with
its arithmetic bounds and group interpretation. No execution assumption or
chosen canonical representative is used to construct the valid output. -/
namespace Agave.Ed25519.SmallOrder
open SerialPoint PointArithmetic Verifier.Execution

/-- Convert between the verifier ABI record and the arithmetic word record. -/
def keyWordPoint (P : Key.PointWords) : WordPoint := ⟨P.X, P.Y, P.Z, P.T⟩
def wordKeyPoint (P : WordPoint) : Key.PointWords := ⟨P.X, P.Y, P.Z, P.T⟩

@[simp] theorem keyWordPoint_wordKeyPoint (P : WordPoint) :
    keyWordPoint (wordKeyPoint P) = P := by cases P; rfl

/-- The concrete four-multiplication conversion after one completed double. -/
def twiceWord (P : WordPoint) : WordPoint := asExtendedWord (SerialPoint.doubleWord P)
def eightTimesWord (P : WordPoint) : WordPoint := twiceWord (twiceWord (twiceWord P))

theorem twiceWord_tight (P : WordPoint) (h : PointTight (unsignedPoint P)) :
    PointTight (unsignedPoint (twiceWord P)) :=
  asExtendedWord_tight _ (SerialPoint.doubleWord_bounded P h)

theorem twiceWord_unsigned (P : WordPoint) (h : PointTight (unsignedPoint P)) :
    unsignedPoint (twiceWord P) = twice (unsignedPoint P) := by
  unfold twiceWord twice
  rw [asExtendedWord_unsigned _ (SerialPoint.doubleWord_bounded P h),
    SerialPoint.doubleWord_unsigned P h]

theorem eightTimesWord_tight (P : WordPoint) (h : PointTight (unsignedPoint P)) :
    PointTight (unsignedPoint (eightTimesWord P)) :=
  twiceWord_tight _ (twiceWord_tight _ (twiceWord_tight P h))

theorem eightTimesWord_unsigned (P : WordPoint) (h : PointTight (unsignedPoint P)) :
    unsignedPoint (eightTimesWord P) = eightTimes (unsignedPoint P) := by
  unfold eightTimesWord eightTimes
  rw [twiceWord_unsigned _ (twiceWord_tight _ (twiceWord_tight P h)),
    twiceWord_unsigned _ (twiceWord_tight P h), twiceWord_unsigned P h]

/-- The verifier's homogeneous coordinate predicate is equivalent to the
existing group-library representative, including its nonzero denominator. -/
theorem key_represents_iff (P : Key.PointWords) (A : Bridge.CurvePoint) :
    P.Represents A ↔ Tables.Represents (pointValue (unsignedPoint (keyWordPoint P))) A := by
  let Q := Tables.toFD (pointValue (unsignedPoint (keyWordPoint P)))
  change (Q.Z ≠ 0 ∧ Q.X = A.x * Q.Z ∧ Q.Y = A.y * Q.Z ∧
    Q.T = A.x * A.y * Q.Z) ↔ ∃ h : Q.WellFormed, Q.toAffine h = A
  constructor
  · rintro ⟨hz, hx, hy, ht⟩
    have hqx : Q.x = A.x := by
      change Q.X * Q.Z⁻¹ = A.x
      rw [hx, mul_assoc, mul_inv_cancel₀ hz, mul_one]
    have hqy : Q.y = A.y := by
      change Q.Y * Q.Z⁻¹ = A.y
      rw [hy, mul_assoc, mul_inv_cancel₀ hz, mul_one]
    have hw : Q.WellFormed := {
      isUnit_Z := hz.isUnit
      onCurve := by rw [hqx, hqy]; exact A.on
      t_spec := by rw [hx, hy, ht]; ring }
    exact ⟨hw, Edwards.Point.ext hqx hqy⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h.isUnit_Z.ne_zero, _root_.Ed25519.Point.X_eq h,
      _root_.Ed25519.Point.Y_eq h, _root_.Ed25519.Point.T_eq h⟩

theorem twiceWord_represents (P : Key.PointWords) (A : Bridge.CurvePoint)
    (ht : PointTight (unsignedPoint (keyWordPoint P))) (hr : P.Represents A) :
    (wordKeyPoint (twiceWord (keyWordPoint P))).Represents (A + A) := by
  apply (key_represents_iff _ _).mpr
  rw [keyWordPoint_wordKeyPoint]
  change Tables.Represents (pointValue (unsignedPoint (asExtendedWord
    (SerialPoint.doubleWord (keyWordPoint P))))) _
  rw [SerialPoint.doubleWord_value _ ht]
  exact Tables.represents_serialDouble ((key_represents_iff P A).mp hr)

theorem eightTimesWord_represents (P : Key.PointWords) (A : Bridge.CurvePoint)
    (ht : PointTight (unsignedPoint (keyWordPoint P))) (hr : P.Represents A) :
    (wordKeyPoint (eightTimesWord (keyWordPoint P))).Represents (8 • A) := by
  have h1 := twiceWord_represents P A ht hr
  have h2 := twiceWord_represents (wordKeyPoint (twiceWord (keyWordPoint P))) (A + A)
    (by simpa using twiceWord_tight _ ht) h1
  have h3 := twiceWord_represents
    (wordKeyPoint (twiceWord (twiceWord (keyWordPoint P)))) ((A + A) + (A + A))
    (by simpa using twiceWord_tight _ (twiceWord_tight _ ht)) (by simpa using h2)
  have h8 : ((A + A) + (A + A)) + ((A + A) + (A + A)) = 8 • A := by abel
  simpa only [keyWordPoint_wordKeyPoint, h8, eightTimesWord] using h3

namespace ValidPoint

theorem wordPoint_tight (P : Verifier.Execution.ValidPoint) :
    PointTight (unsignedPoint (keyWordPoint P.words)) :=
  ⟨P.tightX, P.tightY, P.tightZ, P.tightT⟩

/-- Concrete cofactor representative: the exact word arithmetic determines
all output bytes, while its curve field is the group multiple by eight. -/
def timesEight (P : Verifier.Execution.ValidPoint) : Verifier.Execution.ValidPoint where
  words := wordKeyPoint (eightTimesWord (keyWordPoint P.words))
  curve := 8 • P.curve
  tightX := (eightTimesWord_tight _ (wordPoint_tight P)).1
  tightY := (eightTimesWord_tight _ (wordPoint_tight P)).2.1
  tightZ := (eightTimesWord_tight _ (wordPoint_tight P)).2.2.1
  tightT := (eightTimesWord_tight _ (wordPoint_tight P)).2.2.2
  represents := eightTimesWord_represents P.words P.curve (wordPoint_tight P) P.represents

@[simp] theorem timesEight_curve (P : Verifier.Execution.ValidPoint) :
    (timesEight P).curve = 8 • P.curve := rfl

@[simp] theorem timesEight_words (P : Verifier.Execution.ValidPoint) :
    (timesEight P).words = wordKeyPoint (eightTimesWord (keyWordPoint P.words)) := rfl

end ValidPoint
end Agave.Ed25519.SmallOrder
