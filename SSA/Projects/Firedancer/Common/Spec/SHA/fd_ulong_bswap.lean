/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_ulong_bswap
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_ulong_rotate_right

/-!
# `fd_ulong_bswap` and `fd_ulong_rotate_right` (common)

Both are pure: no memory operand, no call, no flagged arithmetic. So unlike the
SHA-512 entry points these get a full specification rather than a frame one --
the value is pinned and the state comes back equivalent, with no poison escape
hatch, because a total operation on a value cannot produce one.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fd_ulong_bswap x` is the byte reversal of `x`, and touches nothing. -/
abbrev fd_ulong_bswap_spec (x : BitVec 64) (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_ulong_bswap.denote (Ctxt.Valuation.singleton (.value x)))
  ∃ s' : GlobalState, StateT.run invocation s = .value ([.value (SLLVM.bswapBV x)]ₕ, s') ∧ s ≈ s'

/-- `fd_ulong_rotate_right x n` is `fshr x x n`, the rotation, and touches
nothing. The shift amount arrives as an `i32` and is zero-extended, so the
rotation is by `n.toNat % 64` -- `fshr`'s own reduction of the amount. -/
abbrev fd_ulong_rotate_right_spec (x : BitVec 64) (n : BitVec 32) (s : GlobalState) : Prop :=
  let invocation :=
    runFunction (fd_ulong_rotate_right.denote (Ctxt.Valuation.ofHVector [.value n, .value x]ₕ))
  ∃ s' : GlobalState,
    StateT.run invocation s = .value ([.value (SLLVM.fshrBV x x (BitVec.setWidth 64 n))]ₕ, s') ∧
      s ≈ s'

end Firedancer.Common
