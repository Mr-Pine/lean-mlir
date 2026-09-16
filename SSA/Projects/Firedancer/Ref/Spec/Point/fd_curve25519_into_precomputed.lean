/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_curve25519_into_precomputed
import SSA.Projects.Firedancer.Ref.Proof.RefWF
import SSA.Projects.Firedancer.Ref.Proof.Point
import SSA.Projects.Firedancer.Ref.Spec.Bias
import SSA.Projects.Firedancer.Common.Spec.fd_curve25519_into_precomputed

/-!
# `fd_curve25519_into_precomputed` (ref)

The point at `r` becomes its `toPrecomputed`, in place. `X` and `Y` are
`fd_f25519_sub_nr` and `fd_f25519_add_nr` results, so loose; `T` is
`fd_f25519_mul` by `@fd_f25519_k`, so tight; `Z` is not written.

The input bounds are the callees': `Y` tight and `X` bias-bounded for `add_nr` and
`sub_nr`, `T` loose for `mul`. `RefWF [r]` holds `@fd_f25519_k` apart from `r`, which `mul`
writes through.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_curve25519_into_precomputed_spec (r : Pointer) (s : GlobalState)
    (hr : IsPointPtr s.mem r) : Prop :=
  let invocation := runFunction
    (fd_curve25519_into_precomputed.denote (Ctxt.Valuation.singleton (.value r)))
  let result := StateT.run invocation s
  let P := readPoint hr

  have hX : IsFieldElemPtr s.mem r := coordPtr_zero r ▸ isCoordPtr hr 0
  have hY : IsFieldElemPtr s.mem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr hr 1
  have hT : IsFieldElemPtr s.mem (r.withOffset 80) := coordPtr_two r ▸ isCoordPtr hr 2

  s.RefWF [r] → BiasBounds hX → LimbBounds hY → LimbBounds.Loose hT →
  ∃ s' : GlobalState, result = .value ([]ₕ, s') ∧
  ∃ oX oY oT : BitVec (5 * 64),
    let outMem :=
      ((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 80) oT
    let output_state : GlobalState := { s with mem := outMem }

    have hpt : IsPointPtr outMem r :=
      isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr))
    have hoX : IsFieldElemPtr outMem r := coordPtr_zero r ▸ isCoordPtr hpt 0
    have hoY : IsFieldElemPtr outMem (r.withOffset 40) := coordPtr_one r ▸ isCoordPtr hpt 1
    have hoT : IsFieldElemPtr outMem (r.withOffset 80) := coordPtr_two r ▸ isCoordPtr hpt 2

    output_state ≈ s'
    ∧ PrecomputedPoint.ofSlots (readPoint hpt) = P.toPrecomputed
    ∧ LimbBounds.Loose hoX ∧ LimbBounds.Loose hoY ∧ LimbBounds hoT

end Firedancer.Ref
