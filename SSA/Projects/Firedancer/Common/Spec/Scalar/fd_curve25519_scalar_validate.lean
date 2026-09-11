/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_validate

/-!
# `fd_curve25519_scalar_validate` (common)

The region reads the 32-byte scalar at `s` and returns either `s` or `NULL`; it
allocates nothing and stores nothing. What is specified here is exactly that:
the call succeeds with a definite (non-poison) pointer, which is one of the two
the C returns, and the state it leaves is indistinguishable from the one it was
entered in.

Which of the two comes back -- `s < l`, with `l` the group order -- is not
stated: the callers proven so far only need the return to be a pointer they may
null-check.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- A 32-byte scalar at `p`: the block holds 256 bits from `p`'s offset, and
the offset arithmetic the region's `gep`s do stays in range. -/
abbrev IsScalarPtr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (32 * 8) ∧ p.offset.toNat + 32 ≤ 2^64

abbrev fd_curve25519_scalar_validate_spec (p : Pointer) (s : GlobalState) : Prop :=
  let invocation := runFunction
    (fd_curve25519_scalar_validate.denote (Ctxt.Valuation.singleton (.value p)))
  let result := StateT.run invocation s

  ∃ (s' : GlobalState) (ret : Pointer),
    result = .value ([.value ret]ₕ, s') ∧ (ret = p ∨ ret = ⟨nullBlock, 0#64⟩) ∧ s ≈ s'

end Firedancer.Common
