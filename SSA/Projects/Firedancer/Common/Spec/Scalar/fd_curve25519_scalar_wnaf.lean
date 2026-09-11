/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.SLLVM.Dialect
import SSA.Projects.Firedancer.Common.Mlir.Scalar.fd_curve25519_scalar_wnaf

/-!
# `fd_curve25519_scalar_wnaf` (common) -- the memory footprint

The digits are *not* what this file states. What it states is that the region's
only effect on memory is on the 256 `short`s at `slides`: if the run returns,
the state it leaves is equivalent to the entry state with some 4096 bits spliced
in at `slides`.

"If the run returns" carries the weight. Every way the region can fail -- an
out-of-bounds load or store, poison reaching a store or a branch, a loop that
never exits (`Cfg.denote` takes nontermination as UB) -- denotes poison, and on
poison the statement is vacuous.

One splice of the whole buffer is exact rather than an over-approximation of
the loops' scattered stores: `^bb2` and `^bb1` write all 256 entries before any
other store, so whatever the absorb loop does afterwards the buffer ends as some
4096 bits. That nothing *past* the buffer is written rests on the C's argument
that the carry never propagates beyond `slides[255]` (the comment above the
subtract case in `fd_curve25519_scalar.c`), which the proof carries as an
invariant; it needs only `s.WF` and `IsSlidesPtr s.mem slides`.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

/-- 256 `short`s at `p`, the output's shape. -/
abbrev IsSlidesPtr (m : MemoryState) (p : Pointer) : Prop :=
  Fits m p (256 * 16) ∧ p.offset.toNat + 512 ≤ 2 ^ 64

/-- **The region writes nowhere but `slides`.**

If the run returns, the state it leaves is the entry state with the 256 entries
at `slides` replaced by some `w`; the allocation counter, the symbol table and
every other block -- the scalar `n`'s included -- are untouched.

Stated in the named-result form of `fd_curve25519_scalar_reduce_frame_spec`, so
the run term occurs once and a walk can decide poison or value where the region
forces it. -/
abbrev fd_curve25519_scalar_wnaf_frame_spec (slides n : Pointer) (bits : BitVec 32)
    (s : GlobalState) : Prop :=
  let invocation := runFunction (fd_curve25519_scalar_wnaf.denote
    (Ctxt.Valuation.ofHVector [.value bits, .value n, .value slides]ₕ))

  ∃ res, StateT.run invocation s = res
    ∧ ∀ s' : GlobalState, res = .value ([]ₕ, s') →
        ∃ w : BitVec (256 * 16),
          s' ≈ ({ s with mem := s.mem.splice slides w } : GlobalState)

end Firedancer.Common
