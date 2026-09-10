/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Ref.Mlir.Point.fd_ed25519_affine_is_small_order
import SSA.Projects.Firedancer.Ref.Spec.Point
import SSA.Projects.Firedancer.Ref.Proof.RefWF -- Should move out of Proof

/-!
# `fd_ed25519_affine_is_small_order` (ref)

The region copies the point out with `fd_ed25519_point_to` and `or`s four
predicates: `X == 0`, `Y == 0`, `Y == y0`, `Y == y1`. Each is `0` or `1`, so
their `or` is the indicator of that disjunction.

The statement is not the disjunction but what it decides: the point is one of
the eight in `lowOrder`, listed in
`Common/Spec/fd_ed25519_affine_is_small_order.lean`. The two are the same
predicate only for an affine point on the curve, which is what
`isSmallOrderTest_iff_mem` proves and why `Z = 1` and the curve equation are
hypotheses here. The region checks neither, and its *behaviour* depends on
neither -- they buy the reading of the answer, not the answer.

The two globals are not arguments. `@fd_ed25519_order8_point_y{0,1}` are part of
what the module loads, so they come in through `RefWF` along with `@fd_f25519_d`
and the rest: the region reaches them by `llvm.mlir.addressof`, at addresses the
loader chose, and a spec that named those addresses would be quantifying over
something already fixed. `RefWF` also carries their values and their tight limb
bound, which `LimbBounds.bias` turns into what `fd_f25519_eq` asks of its second
operand.

`apart` is empty: the region writes only through its own four allocas, which are
fresh blocks, so no global needs to be held apart from anything a caller owns.

`AllLimbBounds ha` is what the callees need of the argument.
`fd_ed25519_point_to` copies limbs verbatim, so the `x` and `y` slots inherit
the argument's bounds, which is what `fd_f25519_is_zero` and `fd_f25519_eq`'s
first operand ask for.
-/

namespace Firedancer.Ref
open LeanMLIR SLLVM
open InstCombine (LLVM)
open Ed25519

abbrev fd_ed25519_affine_is_small_order_spec (a : Pointer) (s : GlobalState)
    (ha : IsPointPtr s.mem a) : Prop :=
  let invocation := runFunction
    (fd_ed25519_affine_is_small_order.denote (Ctxt.Valuation.singleton (.value a)))
  let result := StateT.run invocation s
  let P := readPoint ha
  let output_value : LLVM.IntW _ := .value (if (P.X, P.Y) ∈ lowOrder then 1#32 else 0#32)

  s.RefWF [] → P.Z = 1 → OnCurve P.x P.y → AllLimbBounds ha →
    ∃ s' : GlobalState, result = .value ([output_value]ₕ, s') ∧ s ≈ s'

end Firedancer.Ref
