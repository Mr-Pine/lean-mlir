/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.Point.fd_ed25519_point_set_zero
import SSA.Projects.Firedancer.Avx512.Spec.Quad
import SSA.Projects.Firedancer.Curve

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519
open Quad

abbrev fd_ed25519_point_set_zero_spec (p: Pointer) (s: GlobalState) : Prop :=
  let invocation := runFunction (fd_ed25519_point_set_zero.denote (Ctxt.Valuation.singleton (.value p)))
  let result := StateT.run invocation s

  ∃ q : Quad ,
    let output_state := { s with mem := s.mem.splice p q.BV }
    (R43x6.U44 q.v03 ∧ R43x6.U44 q.v14 ∧ R43x6.U44 q.v25) ∧ q.toPoint.SamePoint .zero ∧ IsUnit q.toPoint.Z ∧
    ∃ s' : GlobalState , result = .value ([.value p]ₕ, s') ∧ output_state ≈ s'

end Firedancer.Avx512
