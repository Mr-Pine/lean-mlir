/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_append
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_sha512_append` (common) -- the memory footprint

`fd_sha512_append(sha, data, sz)` buffers `sz` bytes of `data` into the hash
state, compressing whole blocks as they fill. This file says only where it
writes: the hash state `sha`, and no other block -- not `data`, even when the
compression reads straight from it. What lands in `sha` is not stated.

Partial, like `fd_sha512_core_ref`'s: a run that goes to UB has no resulting
state, and the implication is vacuous. `data` and `sz` are arbitrary registers.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- **`fd_sha512_append` writes only `sha`.** If the call returns, the state is
well formed, the allocation counter and symbol table are as on entry, and every
block other than `sha`'s reads as it did. -/
abbrev fd_sha512_append_frame_spec (sha : Pointer) (data : SLLVM.Ptr) (sz : LLVM.IntW 64)
    (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_sha512_append.denote
    (Ctxt.Valuation.ofHVector [sz, data, .value sha]ₕ))
  ∃ res, StateT.run invocation s = res
    ∧ ∀ r s', res = .value (r, s') →
        s'.WF ∧ s'.alloc = s.alloc ∧ s'.globals = s.globals
          ∧ ∀ b : BlockId, b ≠ sha.id → s'.mem.live? b = s.mem.live? b

end Firedancer.Common
