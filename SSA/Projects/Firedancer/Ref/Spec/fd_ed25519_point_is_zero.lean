import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.fd_ed25519_point_is_zero
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Curve

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_point_is_zero_spec (p: Pointer) (s: GlobalState) (h: IsPointPtr s.mem p) : Prop :=
  let invocation := runFunction (fd_ed25519_point_is_zero.denote (Ctxt.Valuation.singleton (.value p)))
  let result := StateT.run invocation s
  let extracted_point := readPoint h
  let is_zero := Point.zero.SamePoint extracted_point
  let output_value: LLVM.IntW _ := .value (if is_zero then 1#32 else 0#32)

  -- `X = 0 ∧ Y = Z` is the projective test; it decides `SamePoint` only where
  -- `Z` is invertible. Without this an all-zero buffer decodes to `⟨0,0,0,0⟩`,
  -- which the region reports as zero while `SamePoint` does not.
  IsUnit extracted_point.Z →
    ∃ s' : GlobalState , result = .value ([output_value]ₕ, s') ∧ s ≈ s'

end Firedancer.Ref
