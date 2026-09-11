/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.SHA.fd_sha512_core_ref
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_sha512_core_ref` (common) -- the memory footprint

`fd_sha512_core_ref(state, block, block_cnt)` compresses `block_cnt` 128-byte
blocks into the eight-word hash state. This file does not say what it writes,
only where: if the call returns, the hash state's block is the only one that
changed.

The statement is partial. A run that goes to UB -- an out-of-range read, a
poison value reaching a store, `block_cnt = 0` running off the message -- has no
resulting state to speak of, and makes the implication vacuous. That is what
lets the message pointer and the count be arbitrary registers: whatever they
are, a returning call wrote nothing else.

Internally the region allocates the round buffer `X[16]` and writes it every
round, but that block is freed on return, so the caller's view is the one
stated here.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- **`fd_sha512_core_ref` writes only the hash state.** If the call returns,
the state is well formed, the allocation counter and symbol table are as on
entry, and every block other than `st`'s reads as it did. -/
abbrev fd_sha512_core_ref_frame_spec (st : Pointer) (blk : SLLVM.Ptr) (cnt : LLVM.IntW 64)
    (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_sha512_core_ref.denote
    (Ctxt.Valuation.ofHVector [cnt, blk, .value st]ₕ))
  ∃ res, StateT.run invocation s = res
    ∧ ∀ r s', res = .value (r, s') →
        s'.WF ∧ s'.alloc = s.alloc ∧ s'.globals = s.globals
          ∧ ∀ b : BlockId, b ≠ st.id → s'.mem.live? b = s.mem.live? b

end Firedancer.Common
