/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_fini
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_sha512_fini` (common) -- the memory footprint

`fd_sha512_fini(sha, hash)` pads the buffered message, compresses the last one
or two blocks, and byte-swaps the eight state words into `hash`. This file says
only where it writes: the hash state `sha` and the digest buffer `hash`, and no
other block. What lands there is not stated.

Partial, like `fd_sha512_core_ref`'s: a run that goes to UB -- `buf_used` out of
range, say -- has no resulting state, and the implication is vacuous.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- **`fd_sha512_fini` writes only `sha` and `hash`.** If the call returns, the
state is well formed, the allocation counter and symbol table are as on entry,
and every block other than those two reads as it did. -/
abbrev fd_sha512_fini_frame_spec (sha hash : Pointer) (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_sha512_fini.denote
    (Ctxt.Valuation.ofHVector [.value hash, .value sha]ₕ))
  ∃ res, StateT.run invocation s = res
    ∧ ∀ r s', res = .value (r, s') →
        s'.WF ∧ s'.alloc = s.alloc ∧ s'.globals = s.globals
          ∧ ∀ b : BlockId, ¬ (b = sha.id ∨ b = hash.id) → s'.mem.live? b = s.mem.live? b

end Firedancer.Common
