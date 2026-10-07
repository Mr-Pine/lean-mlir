import SSA.Projects.Agave.Ed25519.Bridge.FiredancerBaseTableData
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerInvocationReady

/-! Kernel certificates for all 128 concrete source records. The finite
arithmetic checks certify the pinned initializer; group induction identifies
its affine representatives with the verifier's mathematical odd-multiple table. -/
namespace Agave.Ed25519.Bridge.FiredancerBaseInitializer
open PointArithmetic
open _root_.Ed25519
open Tables

set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

deriving instance DecidableEq for _root_.Ed25519.PrecomputedPoint

/-- Every stored limb meets the existing Firedancer loose-limb contract. -/
theorem limb_bounds : ∀ (k : Fin 128) (c : Fin 4) (i : Fin 5),
    limb k c i ≤ 0x18000000000000 := by
  decide +kernel

/-- All four physical coordinates decode to the precomputed affine witness. -/
theorem cache_correct (k : Fin 128) : cache k = (toFD (point k)).toPrecomputed := by
  fin_cases k <;> decide +kernel

theorem point_zero : point 0 = fromFD basePoint := by
  decide +kernel

theorem point_z_one (k : Fin 128) : (point k).Z = 1 := by
  fin_cases k <;> rfl

def advance (k : Fin 127) : Extended (ZMod _root_.p) :=
  serialAdd d (serialDouble (point 0)) (point k.castSucc)

/-- Each next record is the normalized result of adding twice the basepoint. -/
theorem advance_certificate (k : Fin 127) :
    (advance k).Z ≠ 0 ∧ point k.succ = scale ((advance k).Z)⁻¹ (advance k) := by
  fin_cases k <;> decide +kernel

theorem advance_related (k : Fin 127) : Related (advance k) (point k.succ) :=
  ⟨_, inv_ne_zero (advance_certificate k).1, (advance_certificate k).2⟩

theorem point_represents (k : Fin 128) : Represents (point k) (firedancerBaseAffine k.val) := by
  induction k using Fin.induction with
  | zero =>
    rw [point_zero]
    refine ⟨wellFormed_basePoint, ?_⟩
    simp [firedancerBaseAffine]
  | succ k ih =>
    have hbase : Represents (point 0) (basePoint.toAffine wellFormed_basePoint) := by
      rw [point_zero]
      exact ⟨wellFormed_basePoint, rfl⟩
    have hstep := represents_serialAdd (represents_serialDouble hbase) ih
    have he : basePoint.toAffine wellFormed_basePoint + basePoint.toAffine wellFormed_basePoint +
        firedancerBaseAffine k.val = firedancerBaseAffine (k.val+1) := by
      unfold firedancerBaseAffine
      rw [← two_nsmul, ← add_nsmul]
      congr 1
      omega
    exact represents_related (he ▸ hstep) (advance_related k)

private theorem normalized_point (P : _root_.Ed25519.Point) (hP : P.WellFormed)
    (hZ : P.Z = 1) :
    P = decodedPoint (P.toAffine hP).x (P.toAffine hP).y := by
  cases P with
  | mk X Y Z T =>
    change Z = 1 at hZ
    subst Z
    have hT : X * Y = T := by simpa using hP.t_spec
    simp only [Point.toAffine, Point.x, Point.y, inv_one, mul_one, decodedPoint, hT]

/-- The complete initializer equals the table used by the existing source proof. -/
theorem cache_eq_mathematical (k : Fin 128) : cache k = firedancerBaseTable k.val := by
  obtain ⟨hP, hAffine⟩ := point_represents k
  have hZ : (toFD (point k)).Z = 1 := point_z_one k
  have hp := normalized_point (toFD (point k)) hP hZ
  rw [hAffine] at hp
  rw [cache_correct, hp]
  rfl

end Agave.Ed25519.Bridge.FiredancerBaseInitializer
