/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_dbln
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Common.Spec.fd_ed25519_point_dbln

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = 2^n a`. The final `fd_ed25519_point_add_final_mul` writes all four
coordinates of `r`, so the loop's earlier stores leave no trace in the memory.
`a` is read only by the first `fd_ed25519_partial_dbl`, into a local, so it may
overlap `r`. -/
abbrev fd_ed25519_point_dbln_spec (r a : Pointer) (n : BitVec 32) (s : GlobalState)
    (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) : Prop :=
  let invocation :=
    runFunction
      (fd_ed25519_point_dbln.denote (Ctxt.Valuation.ofHVector [.value n, .value a, .value r]ₕ))
  let result := StateT.run invocation s
  ∃ oX oY oZ oT : BitVec (5 * 64),
    let outMem :=
      (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice (r.withOffset 120) oZ).splice
        (r.withOffset 80) oT
    let output_state : GlobalState := { s with mem := outMem }
    have hpt : IsPointPtr outMem r :=
      isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))
    (∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s') ∧
      readPoint hpt = (readPoint ha).dbln n ∧ AllLimbBounds hpt

end Firedancer.Ref
