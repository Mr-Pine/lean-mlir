/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_add_final_mul_projective
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Spec.Point.Dbl

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `fd_ed25519_point_add_final_mul` without `T`: one `fd_f25519_mul3` stored
`X, Y, Z` (byte offsets 0, 40, 120); `r`'s `T` is left as it was. `r` and `a`
lie in different blocks. -/
abbrev fd_ed25519_point_add_final_mul_projective_spec (r a : Pointer) (s : GlobalState)
    (_ : r.id ≠ a.id) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_add_final_mul_projective.denote
      (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s

  ∃ oX oY oZ : BitVec (5 * 64),
    let outMem := ((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ
    let output_state : GlobalState := { s with mem := outMem }

    have hpt : IsPointPtr outMem r :=
      isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr))

    (∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s')
    ∧ readPoint hpt = { (readPoint ha).finalMul with T := (readPoint hr).T }
    ∧ LimbBounds (isCoordPtr hpt 0) ∧ LimbBounds (isCoordPtr hpt 1)
    ∧ LimbBounds (isCoordPtr hpt 3)

end Firedancer.Ref
