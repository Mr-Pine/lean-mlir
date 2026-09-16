/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_neg
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.Ref.Proof.Point

/-!
# `fd_ed25519_point_neg` (ref)

`r = -a` as the projective coordinates `(-X : Y : Z : -T)`: coordinate-wise, so
the same representation negated, not merely some representation of `-a`.

`X` and `T` go through `fd_f25519_neg`, which does not carry, so they need
`BiasBounds` on the way in and give `BiasBounds` back -- which is what lets a
result be negated again. `Y` and `Z` go through `fd_f25519_set` and come back
limb for limb.

`r.id ≠ a.id` is `fd_f25519_set`'s disjointness: its region interleaves loads
and stores. The in-place `fd_ed25519_point_neg( A, A )` is not covered.
-/

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_point_neg_spec (r a : Pointer) (s : GlobalState) (_ : r.id ≠ a.id)
    (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) : Prop :=
  let invocation :=
    runFunction (fd_ed25519_point_neg.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s
  let P := readPoint ha
  -- `a`'s coordinates, at the offsets the region's `getelementptr`s compute:
  -- `Z` is field 3 and `T` field 2.
  have haX : IsFieldElemPtr s.mem a := coordPtr_zero a ▸ isCoordPtr ha 0
  have haY : IsFieldElemPtr s.mem (a.withOffset 40) := coordPtr_one a ▸ isCoordPtr ha 1
  have haT : IsFieldElemPtr s.mem (a.withOffset 80) := coordPtr_two a ▸ isCoordPtr ha 2
  have haZ : IsFieldElemPtr s.mem (a.withOffset 120) := coordPtr_three a ▸ isCoordPtr ha 3
  BiasBounds haX →
    BiasBounds haT →
      ∃ s' : GlobalState,
        result = .value ([.value r]ₕ, s') ∧
          ∃ oX oY oZ oT : BitVec (5 * 64),
            let outMem :=
              (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120)
                    oZ).splice
                (r.withOffset 80) oT
            let output_state : GlobalState := { s with mem := outMem }
            have hpt : IsPointPtr outMem r :=
              isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
            have hoX : IsFieldElemPtr outMem r := coordPtr_zero r ▸ isCoordPtr hpt 0
            have hoY : IsFieldElemPtr outMem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr hpt 1
            have hoT : IsFieldElemPtr outMem (r.withOffset 80) := coordPtr_two r ▸ isCoordPtr hpt 2
            have hoZ : IsFieldElemPtr outMem (r.withOffset 120) :=
              coordPtr_three r ▸ isCoordPtr hpt 3
            output_state ≈ s' ∧
              readPoint hpt = { X := -P.X, Y := P.Y, Z := P.Z, T := -P.T } ∧
              BiasBounds hoX ∧
              BiasBounds hoT ∧
              (∀ i : Fin 5, readLimb i hoY = readLimb i haY) ∧
              (∀ i : Fin 5, readLimb i hoZ = readLimb i haZ)

end Firedancer.Ref
