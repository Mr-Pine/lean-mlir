/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanMLIR.Dialects.LLVM.Basic
public import LeanMLIR.Util.Poison

@[expose] public section

namespace InstCombine
open LLVM.Ty

/-- Vectors refine lane-wise. `List.Forall₂` relates two lists only when they have
the same length, so vectors of differing lengths never refine one another --
mirroring the way `HVector.IsRefinedBy` treats mismatched shapes.

NOTE: this is not LLVM-specific; it could move next to the `Prod` and `HVector`
instances in `LeanMLIR.Framework.Refinement` if another dialect needs it. -/
instance instVectorRefinement {α β : Type} {n m : Nat} [inst : HRefinement α β] :
    HRefinement (Vector α n) (Vector β m) where
  IsRefinedBy a b := List.Forall₂ (· ⊑ ·) a.toList b.toList

/-- Refinement of LLVM values, by recursion on the two types: bitvectors lift
`PoisonOr` refinement, vectors go lane-wise, and values of differently-shaped
types never refine one another. -/
def refinement : (t u : LLVM.Ty) → HRefinement (TyDenote.toType t) (TyDenote.toType u)
  | bitvec w, bitvec w' => inferInstanceAs (HRefinement (LLVM.IntW w) (LLVM.IntW w'))
  | MTy.vector _ e, MTy.vector _ f => instVectorRefinement (inst := refinement e f)
  | _, _ => ⟨fun _ _ => False⟩

@[simp, simp_denote]
instance instRefinement : DialectHRefinement LLVM LLVM where
  IsRefinedBy := @fun t u => refinement t u

/-- v4.34 wraps `inferInstanceAs` in an auxiliary def, so `LLVM.IntW.isRefinedBy_iff`
no longer matches `refinement (bitvec w) (bitvec w')`; this bridges the two. -/
@[simp, simp_llvm, simp_denote]
theorem refinement_bitvec_iff {w w' : Nat} (x : LLVM.IntW w) (y : LLVM.IntW w') :
    @HRefinement.IsRefinedBy (LLVM.IntW w) (LLVM.IntW w') (refinement (bitvec w) (bitvec w')) x y ↔
      @HRefinement.IsRefinedBy (LLVM.IntW w) (LLVM.IntW w') LLVM.IntW.instRefinement x y :=
  Iff.rfl
