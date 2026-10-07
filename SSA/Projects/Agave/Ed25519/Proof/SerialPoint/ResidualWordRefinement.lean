import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.PointLayout

namespace Agave.Ed25519.SerialPoint
open SerialFieldMul PointArithmetic

/-- Exact coordinate permutations, used for subtraction without field negation. -/
def swapXY {α : Type} (p : Extended α) : Extended α := ⟨p.Y, p.X, p.Z, p.T⟩
def swapZT {α : Type} (p : Extended α) : Extended α := ⟨p.X, p.Y, p.T, p.Z⟩

def cachedSubWord (p c : WordPoint) : WordPoint :=
  swapZT (cachedAddWord p (swapXY c))

theorem cachedSubWord_unsigned (p c : WordPoint)
    (hp : PointTight (unsignedPoint p)) (hc : PointBounded (unsignedPoint c)) :
    unsignedPoint (cachedSubWord p c) = cachedSubCompleted (unsignedPoint p) (unsignedPoint c) := by
  have hs : PointBounded (unsignedPoint (swapXY c)) := ⟨hc.2.1, hc.1, hc.2.2⟩
  change swapZT (unsignedPoint (cachedAddWord p (swapXY c))) = _
  rw [cachedAddWord_unsigned p (swapXY c) hp hs]
  rfl

theorem cachedSubCompleted_bounded (p c : LimbPoint)
    (hp : PointTight p) (hc : PointBounded c) :
    PointBounded (cachedSubCompleted p c) := by
  have h := cachedAddCompleted_bounded p (swapXY c) hp ⟨hc.2.1, hc.1, hc.2.2⟩
  exact ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

/-- Affine addition omits the projective cache-Z multiplication. -/
def affineAddWord (p c : WordPoint) : WordPoint :=
  let pp := machine (addWord p.Y p.X) c.Y
  let mm := machine (subWord p.Y p.X) c.X
  let tt := machine p.T c.T
  ⟨subWord pp mm, addWord pp mm, addWord (addWord p.Z p.Z) tt,
    subWord (addWord p.Z p.Z) tt⟩

theorem affineAddWord_unsigned (p c : WordPoint)
    (hp : PointTight (unsignedPoint p)) (hc : PointBounded (unsignedPoint c)) :
    unsignedPoint (affineAddWord p c) = affineAddCompleted (unsignedPoint p) (unsigned c.X) (unsigned c.Y) (unsigned c.T) := by
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
  have htt := machine_unsigned_mul p.T c.T hpb.2.2.2 hc.2.2.2
  have hppB := tight_bounded _ (machine_unsigned_tight _ _ hsumB hc.2.1)
  have hmmB := tight_bounded _ (machine_unsigned_tight _ _ hdiffB hc.1)
  have hzzT := hp.2.2.1
  have hzzB := tight_bounded _ hzzT
  have httB := tight_bounded _ (machine_unsigned_tight p.T c.T hpb.2.2.2 hc.2.2.2)
  have hzz2 := addWord_unsigned p.Z p.Z hzzB hzzB
  have hzz2B : Bounded (unsigned (addWord p.Z p.Z)) := by
    rw [hzz2]
    exact add_bounded _ _ hzzT hzzT
  have hx := subWord_unsigned _ _ hppB hmmB
  have hy := addWord_unsigned _ _ hppB hmmB
  have hz := addWord_unsigned _ _ hzz2B httB
  have ht := subWord_unsigned _ _ hzz2B httB
  ext <;> simp only [unsignedPoint, affineAddWord, affineAddCompleted,
    addCompleted, hx, hy, hz, ht, hzz2, hpp, hmm, htt, hsum, hdiff]


def affineSubWord (p c : WordPoint) : WordPoint :=
  swapZT (affineAddWord p (swapXY c))

theorem affineSubWord_unsigned (p c : WordPoint)
    (hp : PointTight (unsignedPoint p)) (hc : PointBounded (unsignedPoint c)) :
    unsignedPoint (affineSubWord p c) =
      affineSubCompleted (unsignedPoint p) (unsigned c.X) (unsigned c.Y) (unsigned c.T) := by
  have hs : PointBounded (unsignedPoint (swapXY c)) := ⟨hc.2.1, hc.1, hc.2.2⟩
  change swapZT (unsignedPoint (affineAddWord p (swapXY c))) = _
  rw [affineAddWord_unsigned p (swapXY c) hp hs]
  rfl

theorem affineAddCompleted_bounded (p c : LimbPoint)
    (hp : PointTight p) (hc : PointBounded c) :
    PointBounded (affineAddCompleted p c.X c.Y c.T) := by
  have hb := pointTight_bounded p hp
  have hd := tight_bounded _ (sub_safe _ _ hb.2.1 hb.1).2.2
  exact addCompleted_bounded _ _ _ _
    (mul_tight _ _ (add_bounded _ _ hp.2.1 hp.1) hc.2.1)
    (mul_tight _ _ hd hc.1) hp.2.2.1
    (mul_tight _ _ hb.2.2.2 hc.2.2.2)

theorem affineSubCompleted_bounded (p c : LimbPoint)
    (hp : PointTight p) (hc : PointBounded c) :
    PointBounded (affineSubCompleted p c.X c.Y c.T) := by
  have h := affineAddCompleted_bounded p (swapXY c) hp ⟨hc.2.1, hc.1, hc.2.2⟩
  exact ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

namespace Execution
/-- Physical affine Niels records contain Y+X, Y-X, and 2dXY only. -/
def affineCacheFromWords (c : PointWords) : WordPoint :=
  let p := pointFromWords c
  ⟨p.Y, p.X, fun _ => 0, p.Z⟩
end Execution
end Agave.Ed25519.SerialPoint
