import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Algebraic refinement of Agave's serial and AVX2 point formulas

These definitions follow `solana-ed25519` 0.2.4:
* `backend/serial/curve_models.rs`: `ProjectivePoint::double`,
  `CompletedPoint::as_extended`, and addition of a `ProjectiveNielsPoint`;
* `backend/vector/avx2/edwards.rs`: `ExtendedPoint::double`, cached conversion,
  and addition of a `CachedPoint`.

The conclusions compare the four coordinates, before taking affine quotients.
No curve-membership or input-range hypotheses are needed for these polynomial
identities. This is the algebraic layer: relating extracted RIR instructions to
these formulas additionally requires the field-operation refinement theorems
and their limb-bound invariants.
-/

namespace Agave.Ed25519.PointArithmetic

/-- Extended projective coordinates, in physical AVX2 lane order X,Y,Z,T. -/
@[ext] structure Extended (K : Type*) where
  X : K
  Y : K
  Z : K
  T : K
  deriving DecidableEq

section Ring
variable {K : Type*} [CommRing K]

/-- A common scale of all four extended coordinates. -/
def scale (c : K) (P : Extended K) : Extended K :=
  ⟨c * P.X, c * P.Y, c * P.Z, c * P.T⟩

@[simp] theorem scale_one (P : Extended K) : scale 1 P = P := by
  ext <;> simp [scale]

@[simp] theorem scale_scale (a b : K) (P : Extended K) :
    scale a (scale b P) = scale (a * b) P := by
  ext <;> simp [scale, mul_assoc]

/-- The four multiplications in `CompletedPoint::as_extended`. -/
def completedToExtended (X Y Z T : K) : Extended K :=
  ⟨X * T, Y * Z, Z * T, X * Y⟩

/-- Dropping T to projective coordinates and applying `ProjectivePoint::as_extended`.
The loop keeps XYZ and performs this conversion once at its final return. -/
def projectiveAsExtended (P : Extended K) : Extended K :=
  ⟨P.X * P.Z, P.Y * P.Z, P.Z ^ 2, P.X * P.Y⟩

theorem completed_consistent (X Y Z T : K) :
    (completedToExtended X Y Z T).X * (completedToExtended X Y Z T).Y =
      (completedToExtended X Y Z T).Z * (completedToExtended X Y Z T).T := by
  simp only [completedToExtended]
  ring

theorem projectiveAsExtended_eq_scale (P : Extended K) (h : P.X * P.Y = P.Z * P.T) :
    projectiveAsExtended P = scale P.Z P := by
  ext <;> simp only [projectiveAsExtended, scale]
  · ring
  · ring
  · ring
  · exact h

/-- Serial `ProjectivePoint::double` followed by `as_extended`. -/
def serialDouble (P : Extended K) : Extended K :=
  let XX := P.X ^ 2
  let YY := P.Y ^ 2
  let ZZ2 := 2 * P.Z ^ 2
  let X_plus_Y_sq := (P.X + P.Y) ^ 2
  let YY_plus_XX := YY + XX
  let YY_minus_XX := YY - XX
  completedToExtended (X_plus_Y_sq - YY_plus_XX) YY_plus_XX
    YY_minus_XX (ZZ2 - YY_minus_XX)

/-- AVX2 doubling, after field-level refinement of shuffle, blend and multiply. -/
def avx2Double (P : Extended K) : Extended K :=
  let S1 := P.X ^ 2
  let S2 := P.Y ^ 2
  let S3 := P.Z ^ 2
  let S4 := (P.X + P.Y) ^ 2
  let S5 := S1 + S2
  let S6 := S1 - S2
  let S8 := S1 - S2 + 2 * S3
  let S9 := S1 + S2 - S4
  ⟨S8 * S9, S5 * S6, S8 * S6, S5 * S9⟩

/-- Exact coordinate equality up to scale -1, for every input tuple. -/
theorem avx2Double_eq_scale_serialDouble (P : Extended K) :
    avx2Double P = scale (-1) (serialDouble P) := by
  ext <;> simp only [avx2Double, serialDouble, completedToExtended, scale] <;> ring

/-- Scaling an input scales a doubled output by its fourth power. -/
theorem serialDouble_scale (c : K) (P : Extended K) :
    serialDouble (scale c P) = scale (c ^ 4) (serialDouble P) := by
  ext <;> simp only [serialDouble, completedToExtended, scale] <;> ring

/-- Serial Niels cached coordinates `(Y-X,Y+X,Z,2*d*T)`. -/
def serialCache (d : K) (Q : Extended K) : Extended K :=
  ⟨Q.Y - Q.X, Q.Y + Q.X, Q.Z, 2 * d * Q.T⟩

/-- Serial addition of projective Niels coordinates, then `as_extended`. -/
def serialAddCached (P C : Extended K) : Extended K :=
  let PP := (P.Y + P.X) * C.Y
  let MM := (P.Y - P.X) * C.X
  let TT2d := P.T * C.T
  let ZZ2 := 2 * (P.Z * C.Z)
  completedToExtended (PP - MM) (PP + MM) (ZZ2 + TT2d) (ZZ2 - TT2d)

/-- Serial `AffineNielsPoint` addition, as used for the precomputed base table.
Its three cached coordinates are Y-X, Y+X, and 2*d*X*Y, with implicit Z=1. -/
def serialAffineAddCached (P : Extended K) (ymx ypx xy2d : K) : Extended K :=
  let PP := (P.Y + P.X) * ypx
  let MM := (P.Y - P.X) * ymx
  let Txy2d := P.T * xy2d
  let Z2 := 2 * P.Z
  completedToExtended (PP - MM) (PP + MM) (Z2 + Txy2d) (Z2 - Txy2d)

/-- The affine base-table path is exactly the projective path with cache Z=1. -/
theorem serialAffineAddCached_eq (P : Extended K) (ymx ypx xy2d : K) :
    serialAffineAddCached P ymx ypx xy2d =
      serialAddCached P ⟨ymx, ypx, 1, xy2d⟩ := by
  simp only [serialAffineAddCached, serialAddCached, mul_one]

def serialAdd (d : K) (P Q : Extended K) : Extended K :=
  serialAddCached P (serialCache d Q)

/-- Addition is homogeneous of degree two in each input tuple. -/
theorem serialAdd_scale (d a b : K) (P Q : Extended K) :
    serialAdd d (scale a P) (scale b Q) =
      scale ((a * b) ^ 2) (serialAdd d P Q) := by
  ext <;> simp only [serialAdd, serialAddCached, serialCache, completedToExtended,
    scale] <;> ring

/-- AVX2 cached conversion, including the negation of lane D. -/
def avx2Cache (Q : Extended K) : Extended K :=
  ⟨121666 * (Q.Y - Q.X), 121666 * (Q.Y + Q.X),
    (2 * 121666) * Q.Z, -(2 * 121665) * Q.T⟩

/-- AVX2 cached addition after the ABDC, ADDA and CBCB shuffles. -/
def avx2AddCached (P C : Extended K) : Extended K :=
  let S8 := (P.Y - P.X) * C.X
  let S9 := (P.Y + P.X) * C.Y
  let S10 := P.Z * C.Z
  let S11 := P.T * C.T
  let S12 := S9 - S8
  let S13 := S9 + S8
  let S14 := S10 - S11
  let S15 := S10 + S11
  ⟨S12 * S14, S15 * S13, S15 * S14, S12 * S13⟩

def avx2Add (P Q : Extended K) : Extended K :=
  avx2AddCached P (avx2Cache Q)

/-- Serial and SIMD caches differ also by the factor two on the Z lane. -/
def cacheScale (c : K) (C : Extended K) : Extended K :=
  ⟨c * C.X, c * C.Y, (2 * c) * C.Z, c * C.T⟩

/-- This is precisely the Edwards parameter relation `d = -121665/121666`. -/
theorem avx2Cache_eq_cacheScale (d : K) (hd : (121666 : K) * d = -121665)
    (Q : Extended K) : avx2Cache Q = cacheScale 121666 (serialCache d Q) := by
  ext <;> simp only [avx2Cache, cacheScale, serialCache]
  linear_combination -2 * Q.T * hd

/-- The cache scale induces its square on all output coordinates. -/
theorem avx2AddCached_cacheScale (c : K) (P C : Extended K) :
    avx2AddCached P (cacheScale c C) = scale (c ^ 2) (serialAddCached P C) := by
  ext <;> simp only [avx2AddCached, serialAddCached, completedToExtended,
    cacheScale, scale] <;> ring

/-- Exact AVX2/serial addition refinement for every two coordinate tuples. -/
theorem avx2Add_eq_scale_serialAdd (d : K) (hd : (121666 : K) * d = -121665)
    (P Q : Extended K) : avx2Add P Q = scale (121666 ^ 2) (serialAdd d P Q) := by
  unfold avx2Add serialAdd
  rw [avx2Cache_eq_cacheScale d hd, avx2AddCached_cacheScale]

/-- Negating a cached point swaps the first two lanes and negates the last. -/
def negateCache (C : Extended K) : Extended K := ⟨C.Y, C.X, C.Z, -C.T⟩

def negatePoint (P : Extended K) : Extended K := ⟨-P.X, P.Y, P.Z, -P.T⟩

theorem avx2Cache_negatePoint (P : Extended K) :
    avx2Cache (negatePoint P) = negateCache (avx2Cache P) := by
  ext <;> simp only [avx2Cache, negatePoint, negateCache] <;> ring

theorem serialCache_negatePoint (d : K) (P : Extended K) :
    serialCache d (negatePoint P) = negateCache (serialCache d P) := by
  ext <;> simp only [serialCache, negatePoint, negateCache] <;> ring

/-- Hence the same refinement applies to the subtraction path. -/
theorem avx2Sub_eq_scale_serialSub (d : K) (hd : (121666 : K) * d = -121665)
    (P Q : Extended K) :
    avx2AddCached P (negateCache (avx2Cache Q)) =
      scale (121666 ^ 2) (serialAddCached P (negateCache (serialCache d Q))) := by
  rw [← avx2Cache_negatePoint, ← serialCache_negatePoint]
  exact avx2Add_eq_scale_serialAdd d hd P (negatePoint Q)

theorem negatePoint_scale (c : K) (P : Extended K) :
    negatePoint (scale c P) = scale c (negatePoint P) := by
  ext <;> simp only [negatePoint, scale] <;> ring

end Ring

section Field
variable {K : Type*} [Field K]

/-- Observable affine coordinates; valid representations additionally have Z ≠ 0. -/
def affine (P : Extended K) : K × K := (P.X / P.Z, P.Y / P.Z)

/-- The serial loop's final projective-to-extended conversion preserves both
observable coordinates; even the totalized Z=0 case agrees. -/
theorem affine_projectiveAsExtended (P : Extended K) :
    affine (projectiveAsExtended P) = affine P := by
  by_cases hZ : P.Z = 0
  · simp [affine, projectiveAsExtended, hZ]
  · simp only [affine, projectiveAsExtended, pow_two,
      mul_div_mul_right _ _ hZ]

/-- Common nonzero projective scale cancels, even without a nonzero-Z premise. -/
theorem affine_scale (c : K) (hc : c ≠ 0) (P : Extended K) :
    affine (scale c P) = affine P := by
  simp only [affine, scale, mul_div_mul_left _ _ hc]

/-- Scaling preserves the domain of genuine projective representations. -/
theorem scale_Z_ne_zero_iff (c : K) (hc : c ≠ 0) (P : Extended K) :
    (scale c P).Z ≠ 0 ↔ P.Z ≠ 0 := by
  simp [scale, hc]

/-- Extended-coordinate consistency XY=ZT is preserved and reflected. -/
theorem scale_consistent_iff (c : K) (hc : c ≠ 0) (P : Extended K) :
    (scale c P).X * (scale c P).Y = (scale c P).Z * (scale c P).T ↔
      P.X * P.Y = P.Z * P.T := by
  have hcc : c * c ≠ 0 := mul_ne_zero hc hc
  simp only [scale]
  constructor <;> intro h
  · apply mul_left_cancel₀ hcc
    linear_combination h
  · linear_combination c ^ 2 * h

/-- This relation records the exact common scale used by the loop invariant. -/
def Related (P Q : Extended K) : Prop := ∃ c : K, c ≠ 0 ∧ Q = scale c P

theorem related_refl (P : Extended K) : Related P P :=
  ⟨1, one_ne_zero, (scale_one P).symm⟩

theorem related_trans {P Q R : Extended K} (hPQ : Related P Q) (hQR : Related Q R) :
    Related P R := by
  obtain ⟨a, ha, rfl⟩ := hPQ
  obtain ⟨b, hb, rfl⟩ := hQR
  exact ⟨b * a, mul_ne_zero hb ha, scale_scale b a P⟩

theorem related_affine_eq {P Q : Extended K} (h : Related P Q) : affine Q = affine P := by
  obtain ⟨c, hc, rfl⟩ := h
  exact affine_scale c hc P

/-- The relation remains true after one serial/AVX2 doubling, even when the
input representations already differ by a nontrivial accumulated scale. -/
theorem double_related {P Q : Extended K} (h : Related P Q) :
    Related (serialDouble P) (avx2Double Q) := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨-1 * c ^ 4, mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 4 hc), ?_⟩
  rw [avx2Double_eq_scale_serialDouble, serialDouble_scale, scale_scale]

/-- Addition also propagates independently accumulated representation scales. -/
theorem add_related (d : K) (hd : (121666 : K) * d = -121665)
    (hc : (121666 : K) ≠ 0) {P P' Q Q' : Extended K}
    (hP : Related P P') (hQ : Related Q Q') :
    Related (serialAdd d P Q) (avx2Add P' Q') := by
  obtain ⟨a, ha, rfl⟩ := hP
  obtain ⟨b, hb, rfl⟩ := hQ
  refine ⟨121666 ^ 2 * (a * b) ^ 2,
    mul_ne_zero (pow_ne_zero 2 hc) (pow_ne_zero 2 (mul_ne_zero ha hb)), ?_⟩
  rw [avx2Add_eq_scale_serialAdd d hd, serialAdd_scale, scale_scale]

theorem negate_related {P Q : Extended K} (h : Related P Q) :
    Related (negatePoint P) (negatePoint Q) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, hc, negatePoint_scale c P⟩

/-- An operation schedule independent of scalar recoding: scalar multiplication
must separately be shown to produce the same schedule and related table entries. -/
inductive Operation (Index : Type*) where
  | double
  | add (index : Index)
  | sub (index : Index)

def serialStep {Index : Type*} (d : K) (table : Index → Extended K)
    (P : Extended K) : Operation Index → Extended K
  | .double => serialDouble P
  | .add i => serialAdd d P (table i)
  | .sub i => serialAdd d P (negatePoint (table i))

def avx2Step {Index : Type*} (table : Index → Extended K)
    (P : Extended K) : Operation Index → Extended K
  | .double => avx2Double P
  | .add i => avx2Add P (table i)
  | .sub i => avx2Add P (negatePoint (table i))

/-- One arbitrary shared signed-digit operation preserves representation relation. -/
theorem step_related {Index : Type*} (d : K)
    (hd : (121666 : K) * d = -121665) (hc : (121666 : K) ≠ 0)
    (serialTable avx2Table : Index → Extended K)
    (hTable : ∀ i, Related (serialTable i) (avx2Table i))
    {P Q : Extended K} (h : Related P Q) (op : Operation Index) :
    Related (serialStep d serialTable P op) (avx2Step avx2Table Q op) := by
  cases op with
  | double => exact double_related h
  | add i => exact add_related d hd hc h (hTable i)
  | sub i => exact add_related d hd hc h (negate_related (hTable i))

/-- A complete shared signed-digit schedule preserves the invariant, with no
bound on its length or hypotheses about the input points being on the curve. -/
theorem schedule_related {Index : Type*} (d : K)
    (hd : (121666 : K) * d = -121665) (hc : (121666 : K) ≠ 0)
    (serialTable avx2Table : Index → Extended K)
    (hTable : ∀ i, Related (serialTable i) (avx2Table i))
    (ops : List (Operation Index)) {P Q : Extended K} (h : Related P Q) :
    Related (ops.foldl (serialStep d serialTable) P)
      (ops.foldl (avx2Step avx2Table) Q) := by
  induction ops generalizing P Q with
  | nil => exact h
  | cons op ops ih =>
    exact ih (step_related d hd hc serialTable avx2Table hTable h op)

/-- A compression observation can be any function of affine X and Y. In Ed25519
it is canonical Y bytes together with the sign bit of canonical X. -/
def compressWith {Bytes : Type*} (encode : K × K → Bytes) (P : Extended K) : Bytes :=
  encode (affine P)

theorem compressWith_scale {Bytes : Type*} (encode : K × K → Bytes)
    (c : K) (hc : c ≠ 0) (P : Extended K) :
    compressWith encode (scale c P) = compressWith encode P := by
  simp only [compressWith, affine_scale c hc]

theorem double_affine_eq (P : Extended K) :
    affine (avx2Double P) = affine (serialDouble P) := by
  rw [avx2Double_eq_scale_serialDouble, affine_scale (-1) (neg_ne_zero.mpr one_ne_zero)]

theorem add_affine_eq (d : K) (hd : (121666 : K) * d = -121665)
    (hc : (121666 : K) ≠ 0) (P Q : Extended K) :
    affine (avx2Add P Q) = affine (serialAdd d P Q) := by
  rw [avx2Add_eq_scale_serialAdd d hd, affine_scale _ (pow_ne_zero 2 hc)]

theorem double_compress_eq {Bytes : Type*} (encode : K × K → Bytes) (P : Extended K) :
    compressWith encode (avx2Double P) = compressWith encode (serialDouble P) := by
  simp only [compressWith, double_affine_eq]

theorem add_compress_eq {Bytes : Type*} (encode : K × K → Bytes)
    (d : K) (hd : (121666 : K) * d = -121665) (hc : (121666 : K) ≠ 0)
    (P Q : Extended K) :
    compressWith encode (avx2Add P Q) = compressWith encode (serialAdd d P Q) := by
  simp only [compressWith, add_affine_eq d hd hc]

/-- Any shared schedule on related tables has identical final compression,
including the serial loop's final projective-to-extended conversion. -/
theorem schedule_compress_eq {Index Bytes : Type*} (encode : K × K → Bytes)
    (d : K) (hd : (121666 : K) * d = -121665) (hc : (121666 : K) ≠ 0)
    (serialTable avx2Table : Index → Extended K)
    (hTable : ∀ i, Related (serialTable i) (avx2Table i))
    (ops : List (Operation Index)) {P Q : Extended K} (h : Related P Q) :
    compressWith encode (ops.foldl (avx2Step avx2Table) Q) =
      compressWith encode (projectiveAsExtended (ops.foldl (serialStep d serialTable) P)) := by
  simp only [compressWith, affine_projectiveAsExtended]
  exact congrArg encode
    (related_affine_eq (schedule_related d hd hc serialTable avx2Table hTable ops h))

/-- Defining the curve parameter by division discharges its only algebraic premise. -/
theorem parameter_relation (hc : (121666 : K) ≠ 0) :
    (121666 : K) * (-121665 / 121666) = -121665 := by
  field_simp [hc]

end Field
end Agave.Ed25519.PointArithmetic
