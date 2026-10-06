import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.Arithmetic
import SSA.Projects.Agave.Ed25519.Spec.PointArithmetic

/-! Limb-level composition of the serial formulas. The RIR execution lemmas
must connect the extracted regions to these schedules; the arithmetic
statements here neither assume nor assert that remaining connection. -/
namespace Agave.Ed25519.SerialPoint
open SerialFieldMul PointArithmetic
section

abbrev LimbPoint := Extended Limbs
abbrev FieldPoint := Extended (ZMod modulus)

def pointValue (P : LimbPoint) : FieldPoint :=
  ⟨value P.X, value P.Y, value P.Z, value P.T⟩

def PointBounded (P : LimbPoint) : Prop :=
  Bounded P.X ∧ Bounded P.Y ∧ Bounded P.Z ∧ Bounded P.T

def PointTight (P : LimbPoint) : Prop :=
  Tight P.X ∧ Tight P.Y ∧ Tight P.Z ∧ Tight P.T

def mul (a b : Limbs) : Limbs := reduce (columns a b)
def sq (a : Limbs) : Limbs := reduce (squareColumns a)

theorem mul_tight (a b : Limbs) (ha : Bounded a) (hb : Bounded b) : Tight (mul a b) := by
  have h := mul_output_bounds a b ha hb
  intro i
  by_cases hi : i = 1
  · subst i
    have hh := h.2.1
    norm_num [radix] at hh ⊢
    exact lt_trans hh (by decide)
  · have hh := h.1 i hi
    norm_num [radix] at hh ⊢
    exact lt_trans hh (by decide)

theorem sq_tight (a : Limbs) (ha : Bounded a) : Tight (sq a) := by
  simpa [sq, mul, squareColumns_eq] using mul_tight a a ha ha

theorem pointTight_bounded (P : LimbPoint) (h : PointTight P) : PointBounded P :=
  ⟨tight_bounded _ h.1, tight_bounded _ h.2.1,
    tight_bounded _ h.2.2.1, tight_bounded _ h.2.2.2⟩

/-- `CompletedPoint::as_extended` uses four ordinary field multiplications. -/
def asExtended (C : LimbPoint) : LimbPoint :=
  ⟨mul C.X C.T, mul C.Y C.Z, mul C.Z C.T, mul C.X C.Y⟩

@[simp] theorem asExtended_value (C : LimbPoint) :
    pointValue (asExtended C) = completedToExtended
      (value C.X) (value C.Y) (value C.Z) (value C.T) := by
  ext <;> simp [pointValue, asExtended, completedToExtended, mul, mul_value]

theorem asExtended_tight (C : LimbPoint) (h : PointBounded C) :
    PointTight (asExtended C) :=
  ⟨mul_tight _ _ h.1 h.2.2.2, mul_tight _ _ h.2.1 h.2.2.1,
    mul_tight _ _ h.2.2.1 h.2.2.2, mul_tight _ _ h.1 h.2.1⟩

def doubleCompleted (P : LimbPoint) : LimbPoint :=
  let xx := sq P.X
  let yy := sq P.Y
  let zz := sq P.Z
  let sum := add yy xx
  let diff := sub yy xx
  ⟨sub (sq (add P.X P.Y)) sum, sum, diff, sub (add zz zz) diff⟩

/-- The natural-number schedule implements the serial doubling polynomial,
with all needed subtraction premises derived from the point invariant. -/
theorem double_value (P : LimbPoint) (h : PointTight P) :
    pointValue (asExtended (doubleCompleted P)) = serialDouble (pointValue P) := by
  have hx := tight_bounded _ h.1
  have hy := tight_bounded _ h.2.1
  have hz := tight_bounded _ h.2.2.1
  have hxx := sq_tight P.X hx
  have hyy := sq_tight P.Y hy
  have hsum := add_bounded _ _ hyy hxx
  have hdiff := tight_bounded _ (sub_safe _ _ (tight_bounded _ hyy)
    (tight_bounded _ hxx)).2.2
  rw [asExtended_value]
  dsimp only [doubleCompleted]
  rw [sub_value _ _ hsum, sub_value _ _ hdiff]
  simp only [sub_value _ _ (tight_bounded _ hxx)]
  simp only [add_value, sq, square_value, serialDouble, pointValue]
  congr 1 <;> ring

theorem doubleCompleted_bounded (P : LimbPoint) (h : PointTight P) :
    PointBounded (doubleCompleted P) := by
  have hx := tight_bounded _ h.1
  have hy := tight_bounded _ h.2.1
  have hz := tight_bounded _ h.2.2.1
  have hxx := sq_tight P.X hx
  have hyy := sq_tight P.Y hy
  have hzz := sq_tight P.Z hz
  have hsum := add_bounded _ _ hyy hxx
  have hsqsum := tight_bounded _ (sq_tight _ (add_bounded _ _ h.1 h.2.1))
  have hdiff := tight_bounded _ (sub_safe _ _ (tight_bounded _ hyy)
    (tight_bounded _ hxx)).2.2
  exact ⟨tight_bounded _ (sub_safe _ _ hsqsum hsum).2.2, hsum, hdiff,
    tight_bounded _ (sub_safe _ _ (add_bounded _ _ hzz hzz) hdiff).2.2⟩

theorem double_tight (P : LimbPoint) (h : PointTight P) :
    PointTight (asExtended (doubleCompleted P)) :=
  asExtended_tight _ (doubleCompleted_bounded P h)

/-- This common tail is also the cached-add body after its field multiplications. -/
def addCompleted (pp mm zz2 tt : Limbs) : LimbPoint :=
  ⟨sub pp mm, add pp mm, add zz2 tt, sub zz2 tt⟩

/-- Cached subtraction exchanges the final Z/T operations. -/
def subCompleted (pm mp zz2 tt : Limbs) : LimbPoint :=
  ⟨sub pm mp, add pm mp, sub zz2 tt, add zz2 tt⟩

@[simp] theorem addCompleted_value (pp mm zz2 tt : Limbs)
    (hmm : Bounded mm) (htt : Bounded tt) :
    pointValue (asExtended (addCompleted pp mm zz2 tt)) =
      completedToExtended (value pp - value mm) (value pp + value mm)
        (value zz2 + value tt) (value zz2 - value tt) := by
  simp only [asExtended_value, addCompleted, sub_value _ _ hmm,
    sub_value _ _ htt, add_value]

@[simp] theorem subCompleted_value (pm mp zz2 tt : Limbs)
    (hmp : Bounded mp) (htt : Bounded tt) :
    pointValue (asExtended (subCompleted pm mp zz2 tt)) =
      completedToExtended (value pm - value mp) (value pm + value mp)
        (value zz2 - value tt) (value zz2 + value tt) := by
  simp only [asExtended_value, subCompleted, sub_value _ _ hmp,
    sub_value _ _ htt, add_value]

/-- Cache fields use the mathematical order (Y-X,Y+X,Z,2dT). The physical
Rust `ProjectiveNielsPoint` stores Y+X first; the memory decoder must swap them. -/
def cachedAddCompleted (P C : LimbPoint) : LimbPoint :=
  addCompleted (mul (add P.Y P.X) C.Y) (mul (sub P.Y P.X) C.X)
    (add (mul P.Z C.Z) (mul P.Z C.Z)) (mul P.T C.T)

def cachedSubCompleted (P C : LimbPoint) : LimbPoint :=
  subCompleted (mul (add P.Y P.X) C.X) (mul (sub P.Y P.X) C.Y)
    (add (mul P.Z C.Z) (mul P.Z C.Z)) (mul P.T C.T)

theorem cachedAdd_value (P C : LimbPoint) (hP : PointTight P) (hC : PointBounded C) :
    pointValue (asExtended (cachedAddCompleted P C)) =
      serialAddCached (pointValue P) (pointValue C) := by
  have hp := pointTight_bounded P hP
  have hsub := tight_bounded _ (sub_safe _ _ hp.2.1 hp.1).2.2
  have hmm := (mul_output_bounds _ _ hsub hC.1).2.2
  have htt := (mul_output_bounds _ _ hp.2.2.2 hC.2.2.2).2.2
  unfold cachedAddCompleted mul
  rw [addCompleted_value _ _ _ _ hmm htt]
  simp only [mul, mul_value, sub_value _ _ hp.1, add_value,
    serialAddCached, pointValue]
  congr 1 <;> ring

theorem cachedSub_value (P C : LimbPoint) (hP : PointTight P) (hC : PointBounded C) :
    pointValue (asExtended (cachedSubCompleted P C)) =
      serialAddCached (pointValue P) (negateCache (pointValue C)) := by
  have hp := pointTight_bounded P hP
  have hsub := tight_bounded _ (sub_safe _ _ hp.2.1 hp.1).2.2
  have hmp := (mul_output_bounds _ _ hsub hC.2.1).2.2
  have htt := (mul_output_bounds _ _ hp.2.2.2 hC.2.2.2).2.2
  unfold cachedSubCompleted mul
  rw [subCompleted_value _ _ _ _ hmp htt]
  simp only [mul, mul_value, sub_value _ _ hp.1, add_value,
    serialAddCached, negateCache, pointValue]
  congr 1 <;> ring

/-- Three tight coefficients fit the 54-bit multiplication caller bound. -/
theorem add_three_bounded (a b c : Limbs) (ha : Tight a) (hb : Tight b)
    (hc : Tight c) : Bounded (add (add a b) c) := by
  intro i
  have := ha i; have := hb i; have := hc i
  simp only [add]
  norm_num at *
  omega

theorem addCompleted_bounded (pp mm zz tt : Limbs)
    (hpp : Tight pp) (hmm : Tight mm) (hzz : Tight zz) (htt : Tight tt) :
    PointBounded (addCompleted pp mm (add zz zz) tt) :=
  ⟨tight_bounded _ (sub_safe _ _ (tight_bounded _ hpp) (tight_bounded _ hmm)).2.2,
    add_bounded _ _ hpp hmm, add_three_bounded _ _ _ hzz hzz htt,
    tight_bounded _ (sub_safe _ _ (add_bounded _ _ hzz hzz) (tight_bounded _ htt)).2.2⟩

theorem subCompleted_bounded (pm mp zz tt : Limbs)
    (hpm : Tight pm) (hmp : Tight mp) (hzz : Tight zz) (htt : Tight tt) :
    PointBounded (subCompleted pm mp (add zz zz) tt) :=
  ⟨tight_bounded _ (sub_safe _ _ (tight_bounded _ hpm) (tight_bounded _ hmp)).2.2,
    add_bounded _ _ hpm hmp,
    tight_bounded _ (sub_safe _ _ (add_bounded _ _ hzz hzz) (tight_bounded _ htt)).2.2,
    add_three_bounded _ _ _ hzz hzz htt⟩

theorem cachedAdd_tight (P C : LimbPoint) (hP : PointTight P) (hC : PointBounded C) :
    PointTight (asExtended (cachedAddCompleted P C)) := by
  have hp := pointTight_bounded P hP
  have hsub := tight_bounded _ (sub_safe _ _ hp.2.1 hp.1).2.2
  apply asExtended_tight
  exact addCompleted_bounded _ _ _ _
    (mul_tight _ _ (add_bounded _ _ hP.2.1 hP.1) hC.2.1)
    (mul_tight _ _ hsub hC.1)
    (mul_tight _ _ hp.2.2.1 hC.2.2.1)
    (mul_tight _ _ hp.2.2.2 hC.2.2.2)

theorem cachedSub_tight (P C : LimbPoint) (hP : PointTight P) (hC : PointBounded C) :
    PointTight (asExtended (cachedSubCompleted P C)) := by
  have hp := pointTight_bounded P hP
  have hsub := tight_bounded _ (sub_safe _ _ hp.2.1 hp.1).2.2
  apply asExtended_tight
  exact subCompleted_bounded _ _ _ _
    (mul_tight _ _ (add_bounded _ _ hP.2.1 hP.1) hC.1)
    (mul_tight _ _ hsub hC.2.1)
    (mul_tight _ _ hp.2.2.1 hC.2.2.1)
    (mul_tight _ _ hp.2.2.2 hC.2.2.2)

def affineAddCompleted (P : LimbPoint) (ymx ypx xy2d : Limbs) : LimbPoint :=
  addCompleted (mul (add P.Y P.X) ypx) (mul (sub P.Y P.X) ymx)
    (add P.Z P.Z) (mul P.T xy2d)

def affineSubCompleted (P : LimbPoint) (ymx ypx xy2d : Limbs) : LimbPoint :=
  subCompleted (mul (add P.Y P.X) ymx) (mul (sub P.Y P.X) ypx)
    (add P.Z P.Z) (mul P.T xy2d)

theorem affineAdd_value (P : LimbPoint) (ymx ypx xy2d : Limbs)
    (hP : PointTight P) (hm : Bounded ymx) (ht : Bounded xy2d) :
    pointValue (asExtended (affineAddCompleted P ymx ypx xy2d)) =
      serialAffineAddCached (pointValue P) (value ymx) (value ypx) (value xy2d) := by
  have hp := pointTight_bounded P hP
  have hsub := tight_bounded _ (sub_safe _ _ hp.2.1 hp.1).2.2
  have hmm := (mul_output_bounds _ _ hsub hm).2.2
  have htt := (mul_output_bounds _ _ hp.2.2.2 ht).2.2
  unfold affineAddCompleted mul
  rw [addCompleted_value _ _ _ _ hmm htt]
  simp only [mul, mul_value, sub_value _ _ hp.1, add_value,
    serialAffineAddCached, pointValue]
  congr 1 <;> ring

theorem affineSub_value (P : LimbPoint) (ymx ypx xy2d : Limbs)
    (hP : PointTight P) (hp' : Bounded ypx) (ht : Bounded xy2d) :
    pointValue (asExtended (affineSubCompleted P ymx ypx xy2d)) =
      serialAffineAddCached (pointValue P) (value ypx) (value ymx) (-value xy2d) := by
  have hp := pointTight_bounded P hP
  have hsub := tight_bounded _ (sub_safe _ _ hp.2.1 hp.1).2.2
  have hmp := (mul_output_bounds _ _ hsub hp').2.2
  have htt := (mul_output_bounds _ _ hp.2.2.2 ht).2.2
  unfold affineSubCompleted mul
  rw [subCompleted_value _ _ _ _ hmp htt]
  simp only [mul, mul_value, sub_value _ _ hp.1, add_value,
    serialAffineAddCached, pointValue]
  congr 1 <;> ring

theorem affineAdd_tight (P : LimbPoint) (ymx ypx xy2d : Limbs)
    (hP : PointTight P) (hm : Bounded ymx) (hp' : Bounded ypx) (ht : Bounded xy2d) :
    PointTight (asExtended (affineAddCompleted P ymx ypx xy2d)) := by
  have hp := pointTight_bounded P hP
  have hsub := tight_bounded _ (sub_safe _ _ hp.2.1 hp.1).2.2
  apply asExtended_tight
  exact addCompleted_bounded _ _ _ _
    (mul_tight _ _ (add_bounded _ _ hP.2.1 hP.1) hp')
    (mul_tight _ _ hsub hm) hP.2.2.1
    (mul_tight _ _ hp.2.2.2 ht)

theorem affineSub_tight (P : LimbPoint) (ymx ypx xy2d : Limbs)
    (hP : PointTight P) (hm : Bounded ymx) (hp' : Bounded ypx) (ht : Bounded xy2d) :
    PointTight (asExtended (affineSubCompleted P ymx ypx xy2d)) := by
  have hp := pointTight_bounded P hP
  have hsub := tight_bounded _ (sub_safe _ _ hp.2.1 hp.1).2.2
  apply asExtended_tight
  exact subCompleted_bounded _ _ _ _
    (mul_tight _ _ (add_bounded _ _ hP.2.1 hP.1) hm)
    (mul_tight _ _ hsub hp') hP.2.2.1
    (mul_tight _ _ hp.2.2.2 ht)

end
end Agave.Ed25519.SerialPoint
