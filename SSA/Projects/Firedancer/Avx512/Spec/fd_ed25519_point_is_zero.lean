/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_ed25519_point_is_zero
import SSA.Projects.Firedancer.Avx512.Spec.Quad
import SSA.Projects.Firedancer.Curve

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519
open Quad

abbrev fd_ed25519_point_is_zero_spec (p: Pointer) (s: GlobalState) (hp : IsQuadPtr s.mem p) : Prop :=
  let invocation := runFunction (fd_ed25519_point_is_zero.denote (Ctxt.Valuation.singleton (.value p)))
  let result := StateT.run invocation s
  let inputPoint := (readQuad hp).toPoint
  let isZero := inputPoint.SamePoint .zero
  let output := if isZero then 1#32 else 0#32

  ∃ s' : GlobalState , result = .value ([.value output]ₕ, s') ∧ s ≈ s'

end Firedancer.Avx512
