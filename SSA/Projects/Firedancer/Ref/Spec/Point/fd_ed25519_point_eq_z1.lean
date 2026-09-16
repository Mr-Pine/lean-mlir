import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_point_eq_z1
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Curve

namespace Firedancer.Ref

open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_point_eq_z1_spec (a b : Pointer) (s : GlobalState) (ha : IsPointPtr s.mem a)
    (hb : IsPointPtr s.mem b) : Prop :=
  let invocation :=
    runFunction (fd_ed25519_point_eq_z1.denote (Ctxt.Valuation.ofPair (.value b) (.value a)))
  let result := StateT.run invocation s
  let pointA := readPoint ha
  let pointB := readPoint hb
  let isEq := pointA.SamePoint pointB
  let output_value : LLVM.IntW _ := .value (if isEq then 1#32 else 0#32)
  pointB.Z = 1 → ∃ s' : GlobalState, result = .value ([output_value]ₕ, s') ∧ s ≈ s'

end Firedancer.Ref
