/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Avx512.Mlir.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Avx512.Spec.Quad
import SSA.Projects.Firedancer.Curve

namespace Firedancer.Avx512
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519
open Quad

/-- As `fd_ed25519_point_eq_spec`, under the header's precondition that the
second point is affine: `b->Z = 1`. -/
abbrev fd_ed25519_point_eq_z1_spec (p q: Pointer) (s: GlobalState) (hp : IsQuadPtr s.mem p) (hq : IsQuadPtr s.mem q) : Prop :=
  let invocation := runFunction (fd_ed25519_point_eq_z1.denote (Ctxt.Valuation.ofPair (.value q) (.value p)))
  let result := StateT.run invocation s
  let input1 := (readQuad hp).toPoint
  let input2 := (readQuad hq).toPoint
  let isEq := input1.SamePoint input2
  let output := if isEq then 1#32 else 0#32

  input2.Z = 1 →
    ∃ s' : GlobalState , result = .value ([.value output]ₕ, s') ∧ s ≈ s'

end Firedancer.Avx512
