import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointWord

namespace Agave.Ed25519.SerialPoint
open SerialFieldMul PointArithmetic

abbrev WordPoint := Extended FieldWords

def unsignedPoint (p : WordPoint) : LimbPoint :=
  ⟨unsigned p.X, unsigned p.Y, unsigned p.Z, unsigned p.T⟩

/-- Cache coordinates use mathematical Y-X,Y+X,Z,2dT order here. -/
def cachedAddWord (p c : WordPoint) : WordPoint :=
  let pp := machine (addWord p.Y p.X) c.Y
  let mm := machine (subWord p.Y p.X) c.X
  let zz := machine p.Z c.Z
  let tt := machine p.T c.T
  ⟨subWord pp mm, addWord pp mm, addWord (addWord zz zz) tt,
    subWord (addWord zz zz) tt⟩

theorem machine_unsigned_mul (a b : FieldWords)
    (ha : Bounded (unsigned a)) (hb : Bounded (unsigned b)) :
    unsigned (machine a b) = mul (unsigned a) (unsigned b) :=
  machine_unsigned a b ha hb

theorem machine_unsigned_tight (a b : FieldWords)
    (ha : Bounded (unsigned a)) (hb : Bounded (unsigned b)) :
    Tight (unsigned (machine a b)) := by
  rw [machine_unsigned_mul a b ha hb]
  exact mul_tight _ _ ha hb

/-- Every word operation in cached addition implements the natural schedule;
all intermediate bounds follow from the point and cache invariants. -/
theorem cachedAddWord_unsigned (p c : WordPoint)
    (hp : PointTight (unsignedPoint p)) (hc : PointBounded (unsignedPoint c)) :
    unsignedPoint (cachedAddWord p c) = cachedAddCompleted (unsignedPoint p) (unsignedPoint c) := by
  have hpb := pointTight_bounded _ hp
  change Bounded (unsigned p.X) ∧ Bounded (unsigned p.Y) ∧
    Bounded (unsigned p.Z) ∧ Bounded (unsigned p.T) at hpb
  change Tight (unsigned p.X) ∧ Tight (unsigned p.Y) ∧
    Tight (unsigned p.Z) ∧ Tight (unsigned p.T) at hp
  change Bounded (unsigned c.X) ∧ Bounded (unsigned c.Y) ∧
    Bounded (unsigned c.Z) ∧ Bounded (unsigned c.T) at hc
  have hsum := addWord_unsigned p.Y p.X hpb.2.1 hpb.1
  have hdiff := subWord_unsigned p.Y p.X hpb.2.1 hpb.1
  have hsumB : Bounded (unsigned (addWord p.Y p.X)) := by
    rw [hsum]
    exact add_bounded _ _ hp.2.1 hp.1
  have hdiffB : Bounded (unsigned (subWord p.Y p.X)) := by
    rw [hdiff]
    exact tight_bounded _ (sub_safe _ _ hpb.2.1 hpb.1).2.2
  have hpp := machine_unsigned_mul (addWord p.Y p.X) c.Y hsumB hc.2.1
  have hmm := machine_unsigned_mul (subWord p.Y p.X) c.X hdiffB hc.1
  have hzz := machine_unsigned_mul p.Z c.Z hpb.2.2.1 hc.2.2.1
  have htt := machine_unsigned_mul p.T c.T hpb.2.2.2 hc.2.2.2
  have hppB := tight_bounded _ (machine_unsigned_tight _ _ hsumB hc.2.1)
  have hmmB := tight_bounded _ (machine_unsigned_tight _ _ hdiffB hc.1)
  have hzzT := machine_unsigned_tight p.Z c.Z hpb.2.2.1 hc.2.2.1
  have hzzB := tight_bounded _ hzzT
  have httB := tight_bounded _ (machine_unsigned_tight p.T c.T hpb.2.2.2 hc.2.2.2)
  have hzz2 := addWord_unsigned (machine p.Z c.Z) (machine p.Z c.Z) hzzB hzzB
  have hzz2B : Bounded (unsigned (addWord (machine p.Z c.Z) (machine p.Z c.Z))) := by
    rw [hzz2]
    exact add_bounded _ _ hzzT hzzT
  have hx := subWord_unsigned _ _ hppB hmmB
  have hy := addWord_unsigned _ _ hppB hmmB
  have hz := addWord_unsigned _ _ hzz2B httB
  have ht := subWord_unsigned _ _ hzz2B httB
  ext <;> simp only [unsignedPoint, cachedAddWord, cachedAddCompleted,
    addCompleted, hx, hy, hz, ht, hzz2, hpp, hmm, hzz, htt, hsum, hdiff]

/-- Conversion of the completed word result to extended coordinates has the
proved cached-add polynomial value. -/
theorem cachedAddWord_value (p c : WordPoint)
    (hp : PointTight (unsignedPoint p)) (hc : PointBounded (unsignedPoint c)) :
    pointValue (asExtended (unsignedPoint (cachedAddWord p c))) =
      serialAddCached (pointValue (unsignedPoint p)) (pointValue (unsignedPoint c)) := by
  rw [cachedAddWord_unsigned p c hp hc]
  exact cachedAdd_value _ _ hp hc

/-- The four exact field-word multiplications used by completed→extended. -/
def asExtendedWord (p : WordPoint) : WordPoint :=
  ⟨machine p.X p.T, machine p.Y p.Z, machine p.Z p.T, machine p.X p.Y⟩

theorem asExtendedWord_unsigned (p : WordPoint)
    (hp : PointBounded (unsignedPoint p)) :
    unsignedPoint (asExtendedWord p) = asExtended (unsignedPoint p) := by
  change Bounded (unsigned p.X) ∧ Bounded (unsigned p.Y) ∧
    Bounded (unsigned p.Z) ∧ Bounded (unsigned p.T) at hp
  apply Extended.ext
  · exact machine_unsigned_mul _ _ hp.1 hp.2.2.2
  · exact machine_unsigned_mul _ _ hp.2.1 hp.2.2.1
  · exact machine_unsigned_mul _ _ hp.2.2.1 hp.2.2.2
  · exact machine_unsigned_mul _ _ hp.1 hp.2.1

theorem asExtendedWord_tight (p : WordPoint)
    (hp : PointBounded (unsignedPoint p)) :
    PointTight (unsignedPoint (asExtendedWord p)) := by
  rw [asExtendedWord_unsigned p hp]
  exact asExtended_tight _ hp

theorem cachedAddCompleted_bounded (p c : LimbPoint)
    (hp : PointTight p) (hc : PointBounded c) :
    PointBounded (cachedAddCompleted p c) := by
  have hpb := pointTight_bounded p hp
  have hsub := tight_bounded _ (sub_safe _ _ hpb.2.1 hpb.1).2.2
  exact addCompleted_bounded _ _ _ _
    (mul_tight _ _ (add_bounded _ _ hp.2.1 hp.1) hc.2.1)
    (mul_tight _ _ hsub hc.1)
    (mul_tight _ _ hpb.2.2.1 hc.2.2.1)
    (mul_tight _ _ hpb.2.2.2 hc.2.2.2)

end Agave.Ed25519.SerialPoint
