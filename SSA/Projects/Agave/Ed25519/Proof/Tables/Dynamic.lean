import SSA.Projects.Agave.Ed25519.Spec.PointArithmetic
import SSA.Projects.Firedancer.Common.Spec.Group

/-!
The odd-multiple constructor in `window.rs:231` and
`backend/vector/avx2/edwards.rs:321` starts with A and repeatedly adds 2A.
These definitions retain the extended point immediately before conversion to
the respective cached representation. The cache conversions are the functions
`serialCache` and `avx2Cache` of PointArithmetic.

This is an algebraic constructor theorem. The RIR memory-loop refinement must
connect its eight stored cache records to these entries.
-/
namespace Agave.Ed25519.Tables
open PointArithmetic

section Generic
variable {K : Type*} [Field K]

/-- Relation between physical serial Niels and AVX2 cached coordinates. -/
def CachedRelated (S V : Extended K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ V = cacheScale c S

theorem cached_related (d : K) (hd : (121666 : K) * d = -121665)
    (hc : (121666 : K) ≠ 0) {P Q : Extended K} (h : Related P Q) :
    CachedRelated (serialCache d P) (avx2Cache Q) := by
  obtain ⟨c, hcn, rfl⟩ := h
  refine ⟨121666 * c, mul_ne_zero hc hcn, ?_⟩
  rw [avx2Cache_eq_cacheScale d hd]
  ext <;> simp only [cacheScale, serialCache, scale] <;> ring

def serialOdd (d : K) (A : Extended K) : Nat → Extended K
  | 0 => A
  | k + 1 => serialAdd d (serialDouble A) (serialOdd d A k)

def avx2Odd (A : Extended K) : Nat → Extended K
  | 0 => A
  | k + 1 => avx2Add (avx2Double A) (avx2Odd A k)

/-- Every constructed entry is related; no table-correctness assumption is used. -/
theorem odd_related (d : K) (hd : (121666 : K) * d = -121665)
    (hc : (121666 : K) ≠ 0) {A A' : Extended K} (hA : Related A A') (k : Nat) :
    Related (serialOdd d A k) (avx2Odd A' k) := by
  induction k with
  | zero => exact hA
  | succ k ih => exact add_related d hd hc (double_related hA) ih

def serialWidth5 (d : K) (A : Extended K) (k : Fin 8) := serialOdd d A k.val
def avx2Width5 (A : Extended K) (k : Fin 8) := avx2Odd A k.val

theorem width5_related (d : K) (hd : (121666 : K) * d = -121665)
    (hc : (121666 : K) ≠ 0) {A A' : Extended K} (hA : Related A A') (k : Fin 8) :
    Related (serialWidth5 d A k) (avx2Width5 A' k) :=
  odd_related d hd hc hA k.val

/-- The stored cache records, not only their extended antecedents, are related. -/
theorem width5_cached_related (d : K) (hd : (121666 : K) * d = -121665)
    (hc : (121666 : K) ≠ 0) {A A' : Extended K} (hA : Related A A') (k : Fin 8) :
    CachedRelated (serialCache d (serialWidth5 d A k))
      (avx2Cache (avx2Width5 A' k)) :=
  cached_related d hd hc (width5_related d hd hc hA k)

/-- Specializing the schedule theorem removes its dynamic-table premise. -/
theorem dynamic_schedule_related (d : K) (hd : (121666 : K) * d = -121665)
    (hc : (121666 : K) ≠ 0) {A A' P P' : Extended K}
    (hA : Related A A') (hP : Related P P') (ops : List (Operation (Fin 8))) :
    Related (ops.foldl (serialStep d (serialWidth5 d A)) P)
      (ops.foldl (avx2Step (avx2Width5 A')) P') :=
  schedule_related d hd hc _ _ (width5_related d hd hc hA) ops hP
end Generic

open _root_.Ed25519
abbrev F := ZMod p

def toFD (P : Extended F) : _root_.Ed25519.Point := ⟨P.X, P.Y, P.Z, P.T⟩
def fromFD (P : _root_.Ed25519.Point) : Extended F := ⟨P.X, P.Y, P.Z, P.T⟩

@[simp] theorem toFD_fromFD (P : _root_.Ed25519.Point) : toFD (fromFD P) = P := by
  cases P; rfl
@[simp] theorem fromFD_toFD (P : Extended F) : fromFD (toFD P) = P := by
  cases P; rfl

def Represents (P : Extended F) (V : Edwards.Point curve) : Prop :=
  ∃ h : (toFD P).WellFormed, (toFD P).toAffine h = V

theorem represents_related {P Q : Extended F} {V : Edwards.Point curve}
    (hP : Represents P V) (hPQ : Related P Q) : Represents Q V := by
  obtain ⟨hP, rfl⟩ := hP
  obtain ⟨c, hc, rfl⟩ := hPQ
  have hxy : affine (scale c P) = affine P := affine_scale c hc P
  have hx := congrArg Prod.fst hxy
  have hy := congrArg Prod.snd hxy
  simp only [affine, div_eq_mul_inv] at hx hy
  have hQ : (toFD (scale c P)).WellFormed := {
    isUnit_Z := (mul_ne_zero hc hP.isUnit_Z.ne_zero).isUnit
    onCurve := by
      change OnCurve ((scale c P).X * (scale c P).Z⁻¹)
        ((scale c P).Y * (scale c P).Z⁻¹)
      rw [hx, hy]
      exact hP.onCurve
    t_spec := by
      change (c * P.X) * (c * P.Y) = (c * P.T) * (c * P.Z)
      have ht : P.X * P.Y = P.T * P.Z := hP.t_spec
      linear_combination c ^ 2 * ht }
  refine ⟨hQ, ?_⟩
  apply Edwards.Point.ext <;> assumption

theorem serialAdd_toFD (P Q : Extended F) :
    toFD (serialAdd d P Q) = (toFD P).addPrecomputed (toFD Q).toPrecomputed := by
  cases P; cases Q
  simp only [toFD, serialAdd, serialAddCached, serialCache, completedToExtended,
    Point.addPrecomputed, Point.toPrecomputed]
  congr 1 <;> ring

theorem avx2Double_toFD (P : Extended F) :
    toFD (avx2Double P) = (toFD P).dbl := by
  cases P
  simp only [toFD, avx2Double, Point.dbl]
  congr 1 <;> ring

theorem represents_serialAdd {P Q : Extended F} {V W : Edwards.Point curve}
    (hP : Represents P V) (hQ : Represents Q W) :
    Represents (serialAdd d P Q) (V + W) := by
  obtain ⟨hP, rfl⟩ := hP
  obtain ⟨hQ, rfl⟩ := hQ
  unfold Represents
  rw [serialAdd_toFD]
  exact ⟨Point.wellFormed_addPrecomputed hP hQ, Point.toAffine_addPrecomputed hP hQ⟩

theorem represents_serialDouble {P : Extended F} {V : Edwards.Point curve}
    (hP : Represents P V) : Represents (serialDouble P) (V + V) := by
  have hD : Represents (avx2Double P) (V + V) := by
    obtain ⟨hP, rfl⟩ := hP
    unfold Represents
    rw [avx2Double_toFD]
    exact ⟨Point.wellFormed_dbl hP, Point.toAffine_dbl hP⟩
  apply represents_related hD
  refine ⟨-1, neg_ne_zero.mpr one_ne_zero, ?_⟩
  rw [avx2Double_eq_scale_serialDouble, scale_scale]
  simp

/-- Each serial constructor entry represents precisely the advertised odd multiple. -/
theorem serialOdd_represents {A : Extended F} {V : Edwards.Point curve}
    (hA : Represents A V) (k : Nat) : Represents (serialOdd d A k) ((2*k+1) • V) := by
  induction k with
  | zero => simpa [serialOdd] using hA
  | succ k ih =>
    have h := represents_serialAdd (represents_serialDouble hA) ih
    have he : V + V + (2*k+1) • V = (2*(k+1)+1) • V := by
      rw [← two_nsmul, ← add_nsmul]
      congr 1
      omega
    simpa only [serialOdd, he] using h

/-- The SIMD constructor has the same mathematical entries, despite different scales. -/
theorem avx2Odd_represents {A : Extended F} {V : Edwards.Point curve}
    (hA : Represents A V) (k : Nat) : Represents (avx2Odd A k) ((2*k+1) • V) := by
  exact represents_related (serialOdd_represents hA k)
    (odd_related d d_spec (by decide) (related_refl A) k)

end Agave.Ed25519.Tables
