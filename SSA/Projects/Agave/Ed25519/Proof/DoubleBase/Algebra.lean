import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.Control
import SSA.Projects.Agave.Ed25519.Proof.Tables.Static

/-!
# Algebraic double-base equivalence with concrete lookup tables

This composes the actual source NAF specification, the exact descending scan
and inclusive ladder, proved point-formula identities, the width-five table
constructor, and the kernel-certified static width-eight table constants.
No field-operation correctness or table correctness hypothesis is assumed here.

The theorem remains an algebraic refinement endpoint. The complete compiler
CFGs in SerialCFG/Avx2CFG still need machine-memory and field-limb refinement
to these definitions; this file does not claim that remaining obligation.
-/
namespace Agave.Ed25519.DoubleBase

open PointArithmetic Tables

def serialMath (a : Nat) (A : Extended F) (b : Nat) : Extended F :=
  projectiveAsExtended
    (run (serialStep _root_.Ed25519.d (finiteTable (serialDoubleBaseTable A)))
      (nafDigits 5 a) (nafDigits 8 b)
      (startIndex (nafDigits 5 a) (nafDigits 8 b) 255) identityPoint)

def avx2Math (a : Nat) (A : Extended F) (b : Nat) : Extended F :=
  run (avx2Step (finiteTable (avx2DoubleBaseTable A)))
    (nafDigits 5 a) (nafDigits 8 b)
    (startIndex (nafDigits 5 a) (nafDigits 8 b) 255) identityPoint

/-- The serial and vector algebraic algorithms have the same affine result for
all input tuples and scalars, with the actual table construction and constants.
No on-curve premise is needed for this equivalence of the polynomial formulas. -/
theorem double_base_math_affine_eq (a b : Nat) (A : Extended F) :
    affine (avx2Math a A b) = affine (serialMath a A b) := by
  unfold serialMath avx2Math
  rw [affine_projectiveAsExtended]
  exact double_base_affine_eq _root_.Ed25519.d _root_.Ed25519.d_spec (by decide)
    _ _ (finiteTable_related _ _ (doubleBaseTable_related (related_refl A)))
    _ _ (related_refl identityPoint)

/-- Any common canonical affine encoding gives exactly the same bytes. -/
theorem double_base_math_compress_eq {Bytes : Type*} (encode : F × F → Bytes)
    (a b : Nat) (A : Extended F) :
    compressWith encode (avx2Math a A b) = compressWith encode (serialMath a A b) := by
  simp only [compressWith, double_base_math_affine_eq]

end Agave.Ed25519.DoubleBase
