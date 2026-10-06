/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import SSA.Projects.SLLVM.Dialect
public import SSA.Projects.Firedancer.ByteBuf
public import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_validate

/-!
# `fd_curve25519_scalar_validate` (common)

The region reads the 32-byte scalar at `s` and returns `s` if it is below `ℓ`, the group order,
and `NULL` otherwise; it allocates nothing and stores nothing, so the state it leaves is
indistinguishable from the one it was entered in.
-/

@[expose] public section

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `ℓ`, the order of edwards25519's prime-order subgroup. -/
def groupOrder : Nat :=
  2 ^ 252 + 27742317777372353535851937790883648493

/-- **The region returns `p` if the scalar at `p` is below `ℓ`, else `NULL`, and leaves the
state unchanged.** -/
abbrev fd_curve25519_scalar_validate_spec (p : Pointer) (s : GlobalState)
    (hp : IsByteBufPtr s.mem p) : Prop :=
  let invocation :=
    runFunction (fd_curve25519_scalar_validate.denote (Ctxt.Valuation.singleton (.value p)))
  let result := StateT.run invocation s
  ∃ s' : GlobalState,
    result =
        .value ([.value (if (readBuf hp).toNat < groupOrder then p else ⟨nullBlock, 0#64⟩)]ₕ, s') ∧
      s ≈ s'

end Firedancer.Common
