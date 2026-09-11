/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_memcpy
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_memset
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_memcpy` and `fd_memset` (common)

Both are one intrinsic and a return. The length is a *runtime* operand, not a
literal, so the specifications quantify over it and ask the caller for room at
both ends.

These are frame statements in the same sense as `fd_curve25519_scalar_reduce`'s:
they say where the write lands, and `readWord` says what it leaves there.
Nothing is claimed about the bytes beyond that, which for `memcpy` is exactly
the source's own content and for `memset` a fill of zeroes.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- `fd_memcpy(d, s, sz)` copies `sz` bytes and returns `d`.

`memcpy` reads before it writes, so the bytes that land at `d` are the source
block's as they were on entry -- which is what makes the statement meaningful
even when the two ranges overlap, a case LLVM leaves undefined and the model
resolves by reading first. -/
abbrev fd_memcpy_spec (d src : Pointer) (sz : BitVec 64) (s : GlobalState)
    (hsrc : Fits s.mem src (8 * sz.toNat)) : Prop :=
  let invocation := runFunction
    (fd_memcpy.denote (Ctxt.Valuation.ofHVector [.value sz, .value src, .value d]ₕ))
  ∃ s' : GlobalState,
    StateT.run invocation s = .value ([.value d]ₕ, s')
      ∧ s' ≈ ({ s with mem := s.mem.splice d (readWord hsrc) } : GlobalState)

/-- `fd_memset(d, sz)` fills `sz` bytes with zero and returns `d`. The fill byte
is a constant in the region: SHA-512 only ever zeroes. -/
abbrev fd_memset_spec (d : Pointer) (sz : BitVec 64) (s : GlobalState) : Prop :=
  let invocation := runFunction
    (fd_memset.denote (Ctxt.Valuation.ofHVector [.value sz, .value d]ₕ))
  ∃ s' : GlobalState,
    StateT.run invocation s = .value ([.value d]ₕ, s')
      ∧ s' ≈ ({ s with mem := s.mem.splice d (BitVec.replicate sz.toNat (0#8)) } : GlobalState)

end Firedancer.Common
