/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_curve25519_into_precomputed
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_frombytes_2x
import SSA.Projects.Firedancer.Avx512.Spec.Point.fd_ed25519_point_neg
import SSA.Projects.Firedancer.Common.Spec.fd_curve25519_into_precomputed

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- The point at `r` becomes its `toPrecomputed`, in place, `u44`. All three
vectors are loaded before the stores, so the memory is one QUAD store. `u62` in
keeps `Y + X` below `2^63`, which `FD_R43X6_QUAD_FOLD_SIGNED` needs. The final fold leaves `2d·T`
within `2p`'s limbs, so the point can be subtracted. -/
abbrev fd_curve25519_into_precomputed_spec (r : Pointer) (s : GlobalState)
    (hr : IsQuadPtr s.mem r) : Prop :=
  let invocation := runFunction
    (fd_curve25519_into_precomputed.denote (Ctxt.Valuation.singleton (.value r)))
  let result := StateT.run invocation s
  let q := readQuad hr

  R43x6.U62 q.v03 → R43x6.U62 q.v14 → R43x6.U62 q.v25 →
  ∃ q' : Quad,
    let output_state : GlobalState := { s with mem := s.mem.writeQuad r q' }

    (∃ s' : GlobalState, result = .value ([]ₕ, s') ∧ output_state ≈ s')
    ∧ PrecomputedPoint.ofSlots q'.toPoint = q.toPoint.toPrecomputed
    ∧ R43x6.U44 q'.v03 ∧ R43x6.U44 q'.v14 ∧ R43x6.U44 q'.v25 ∧ q'.NegBounds 3

end Firedancer.Avx512
