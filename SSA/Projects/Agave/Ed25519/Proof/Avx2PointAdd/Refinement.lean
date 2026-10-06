import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.Composition
import Mathlib.Data.ZMod.Basic

/-! Field refinement of the concrete integer-limb cached-add composition.
The RIR execution-to-limb connection is intentionally not an assumption of any
result here and remains a separate proof obligation. -/
namespace Agave.Ed25519.Avx2PointAdd
open Avx2FieldMul PointArithmetic
abbrev K := ZMod Field.p

def value (a : Limbs) : K := Field.decode10 a
def pointValue (P : Point) : Extended K := ⟨value P.X, value P.Y, value P.Z, value P.T⟩

@[simp] theorem value_product (a b : Limbs) :
    value (product a b) = value a * value b := by
  unfold value
  rw [← Nat.cast_mul]
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr (product_mod a b)

@[simp] theorem value_lazySum (a b : Limbs) :
    value (lazySum a b) = value b + value a := by
  simp [value, lazySum, Field.decode10, Nat.add_mul, Finset.sum_add_distrib]

private theorem twiceP_decode : Field.decode10 twiceP = 2 * Field.p := by
  norm_num [Field.decode10, Field.exponent, twiceP, Field.p, Fin.sum_univ_succ]

theorem lazyNeg_conservation {a : Limbs} (ha : reduced a) :
    Field.decode10 (lazyNeg a) + Field.decode10 a = 2 * Field.p := by
  rw [← twiceP_decode]
  unfold Field.decode10
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Nat.add_mul]
  congr 1
  exact Nat.sub_add_cancel (reduced_le_twiceP ha i)

theorem value_lazyNeg {a : Limbs} (ha : reduced a) : value (lazyNeg a) = -value a := by
  have h := congrArg (fun n : Nat => (n : K)) (lazyNeg_conservation ha)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_self, mul_zero] at h
  exact eq_neg_iff_add_eq_zero.mpr h

theorem value_lazyDiff {a : Limbs} (ha : reduced a) (b : Limbs) :
    value (lazyDiff a b) = value b - value a := by
  change value (lazySum (lazyNeg a) b) = _
  rw [value_lazySum, value_lazyNeg ha, sub_eq_add_neg]

theorem pointValue_prepare {P : Point} (h : pointReduced P) :
    pointValue (prepare P) =
      ⟨(pointValue P).Y - (pointValue P).X,
       (pointValue P).Y + (pointValue P).X, (pointValue P).Z, (pointValue P).T⟩ := by
  ext <;> simp [pointValue, prepare, value_lazyDiff h.1]

theorem pointValue_multiply (P Q : Point) :
    pointValue (multiply P Q) = laneMul (pointValue P) (pointValue Q) := by
  ext <;> simp [pointValue, multiply, laneMul]

theorem pointValue_diffSum {P : Point} (h : pointReduced P) :
    pointValue (diffSum P) = laneDiffSum (pointValue P) := by
  ext <;> simp [pointValue, diffSum, laneDiffSum, value_lazyDiff h.1,
    value_lazyDiff h.2.2.1]

/-- Concrete limb arithmetic, reductions, and physical lane permutations
refine the cached-add field formula; tightness is restored on output. -/
theorem add_refines {P C : Point} (hP : pointReduced P) (hC : pointWide C) :
    pointValue (add P C) = avx2AddCached (pointValue P) (pointValue C) := by
  have hm := multiply_reduced (prepare_wide hP) hC
  have hs : pointReduced (shuffleABDC (multiply (prepare P) C)) :=
    ⟨hm.1, hm.2.1, hm.2.2.2, hm.2.2.1⟩
  have hd := pointValue_diffSum hs
  have hp := pointValue_prepare hP
  have hv := pointValue_multiply (prepare P) C
  unfold add
  rw [pointValue_multiply]
  change laneMul
    ⟨(pointValue (diffSum (shuffleABDC (multiply (prepare P) C)))).X,
     (pointValue (diffSum (shuffleABDC (multiply (prepare P) C)))).T,
     (pointValue (diffSum (shuffleABDC (multiply (prepare P) C)))).T,
     (pointValue (diffSum (shuffleABDC (multiply (prepare P) C)))).X⟩
    ⟨(pointValue (diffSum (shuffleABDC (multiply (prepare P) C)))).Z,
     (pointValue (diffSum (shuffleABDC (multiply (prepare P) C)))).Y,
     (pointValue (diffSum (shuffleABDC (multiply (prepare P) C)))).Z,
     (pointValue (diffSum (shuffleABDC (multiply (prepare P) C)))).Y⟩ = _
  rw [hd]
  have hab : pointValue (shuffleABDC (multiply (prepare P) C)) =
      ⟨(pointValue (multiply (prepare P) C)).X,
       (pointValue (multiply (prepare P) C)).Y,
       (pointValue (multiply (prepare P) C)).T,
       (pointValue (multiply (prepare P) C)).Z⟩ := rfl
  rw [hab, hv, hp]
  rfl

theorem pointValue_negate {C : Point} (h : pointReduced C) :
    pointValue (negate C) = negateCache (pointValue C) := by
  ext <;> simp [pointValue, negate, negateCache, value_lazyNeg h.2.2.2]

/-- Subtraction performs precisely one safe lazy negation of a reduced cache. -/
theorem sub_refines {P C : Point} (hP : pointReduced P) (hC : pointReduced C) :
    pointValue (sub P C) = avx2AddCached (pointValue P) (negateCache (pointValue C)) := by
  have hc : pointWide C := ⟨reduced_wide hC.1, reduced_wide hC.2.1,
    reduced_wide hC.2.2.1, reduced_wide hC.2.2.2⟩
  change pointValue (add P (negate C)) = _
  rw [add_refines hP (negate_wide hc), pointValue_negate hC]

/-- The only additional premise is the representation relation with the
serial cache; field arithmetic correctness is discharged by `add_refines`. -/
theorem add_refines_serial {P C : Point} (hP : pointReduced P) (hC : pointWide C)
    (c : K) (serial : Extended K) (hc : pointValue C = cacheScale c serial) :
    pointValue (add P C) = scale (c^2) (serialAddCached (pointValue P) serial) := by
  rw [add_refines hP hC, hc, avx2AddCached_cacheScale]

end Agave.Ed25519.Avx2PointAdd
