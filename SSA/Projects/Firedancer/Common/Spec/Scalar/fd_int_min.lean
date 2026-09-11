/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_int_min

/-!
# `fd_int_min` (common)

The region is `fd_int_min( x, 14 )` with the `14` folded in: one `llvm.intr.smin`
against the constant. Pure, so the state comes back equivalent. `x` is any
register value, poison included -- `smin` passes poison through.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

abbrev fd_int_min_spec (x : LLVM.IntW 32) (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_int_min.denote (Ctxt.Valuation.singleton x))
  ∃ s' : GlobalState,
    StateT.run invocation s = .value ([SLLVM.smin x (.value 14#32)]ₕ, s') ∧ s ≈ s'

end Firedancer.Common
