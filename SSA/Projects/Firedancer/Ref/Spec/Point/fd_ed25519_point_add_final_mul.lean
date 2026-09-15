/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_add_final_mul
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Spec.Point.Dbl

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

/-- `r = finalMul a`, one `fd_f25519_mul4` stored `X, Y, Z, T` (byte offsets 0,
40, 120, 80). The C declares `r` `restrict`; here `r` and `a` lie in different
blocks. -/
abbrev fd_ed25519_point_add_final_mul_spec (r a : Pointer) (s : GlobalState)
    (_ : r.id ≠ a.id) (hr : IsPointPtr s.mem r) (ha : IsPointPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_point_add_final_mul.denote (Ctxt.Valuation.ofHVector [.value a, .value r]ₕ))
  let result := StateT.run invocation s

  ∃ oX oY oZ oT : BitVec (5 * 64),
    let outMem := (((s.mem.splice r oX).splice (r.withOffset 40) oY).splice
      (r.withOffset 120) oZ).splice (r.withOffset 80) oT
    let output_state : GlobalState := { s with mem := outMem }

    have hpt : IsPointPtr outMem r :=
      isPointPtr_splice (isPointPtr_splice (isPointPtr_splice (isPointPtr_splice hr)))

    (∃ s' : GlobalState, result = .value ([.value r]ₕ, s') ∧ output_state ≈ s')
    ∧ readPoint hpt = (readPoint ha).finalMul
    ∧ AllLimbBounds hpt

end Firedancer.Ref
