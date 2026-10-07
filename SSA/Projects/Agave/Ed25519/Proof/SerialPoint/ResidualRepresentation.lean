import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.ResidualWordRefinement
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Group

namespace Agave.Ed25519.SerialPoint
open PointArithmetic SerialFieldMul Tables
open DoubleBase (GroupPoint represents_negate)

/-- The implicit affine Z belongs to the cache interpretation, not its memory record. -/
def affineCacheValue (c : LimbPoint) : FieldPoint :=
  ⟨value c.X, value c.Y, 1, value c.T⟩

/-- Completed subtraction remains a genuine, nonzero-Z representative after
conversion. Nonvanishing follows from the curve group law, not an output premise. -/
theorem cachedSubCompleted_represents (p c : LimbPoint)
    (hp : PointTight p) (hc : PointBounded c)
    {Q : FieldPoint} {V W : GroupPoint}
    (hP : Represents (pointValue p) V) (hQ : Represents Q W)
    (hC : pointValue c = serialCache _root_.Ed25519.d Q) :
    Represents (pointValue (asExtended (cachedSubCompleted p c))) (V - W) := by
  rw [cachedSub_value p c hp hc, hC]
  erw [← serialCache_negatePoint]
  convert represents_serialAdd hP (represents_negate hQ) using 1
  simp only [serialAdd, sub_eq_add_neg]
  rfl

theorem affineAddCompleted_represents (p c : LimbPoint)
    (hp : PointTight p) (hc : PointBounded c)
    {Q : FieldPoint} {V W : GroupPoint}
    (hP : Represents (pointValue p) V) (hQ : Represents Q W)
    (hC : affineCacheValue c = serialCache _root_.Ed25519.d Q) :
    Represents (pointValue (asExtended (affineAddCompleted p c.X c.Y c.T))) (V + W) := by
  rw [affineAdd_value p c.X c.Y c.T hp hc.1 hc.2.2.2, serialAffineAddCached_eq]
  change Represents (serialAddCached (pointValue p) (affineCacheValue c)) (V + W)
  rw [hC]
  exact represents_serialAdd hP hQ

theorem affineSubCompleted_represents (p c : LimbPoint)
    (hp : PointTight p) (hc : PointBounded c)
    {Q : FieldPoint} {V W : GroupPoint}
    (hP : Represents (pointValue p) V) (hQ : Represents Q W)
    (hC : affineCacheValue c = serialCache _root_.Ed25519.d Q) :
    Represents (pointValue (asExtended (affineSubCompleted p c.X c.Y c.T))) (V - W) := by
  rw [affineSub_value p c.X c.Y c.T hp hc.2.1 hc.2.2.2, serialAffineAddCached_eq]
  change Represents (serialAddCached (pointValue p) (negateCache (affineCacheValue c))) (V - W)
  rw [hC]
  erw [← serialCache_negatePoint]
  convert represents_serialAdd hP (represents_negate hQ) using 1 <;>
    simp only [serialAdd, sub_eq_add_neg]

end Agave.Ed25519.SerialPoint
