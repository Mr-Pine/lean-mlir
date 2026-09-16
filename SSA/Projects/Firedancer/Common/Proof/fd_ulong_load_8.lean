/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Mlir.fd_ulong_load_8
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics

/-!
# `fd_ulong_load_8` conforms

One unaligned 64-bit load. The statement is in the shape a caller's
`peel_call` consumes: the value is `readWord` of the 64 bits at `p`, the state
comes back equivalent.
-/

namespace Firedancer.Common

open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fd_ulong_load_8_conforms (p : Pointer) (s : GlobalState) (hs : s.WF)
    (hp : Fits s.mem p 64) :
    ∃ s' : GlobalState,
      StateT.run (runFunction (fd_ulong_load_8.denote (Ctxt.Valuation.singleton (.value p)))) s =
          .value ([.value (readWord hp)]ₕ, s') ∧
        s ≈ s' := by
  simp only [Cfg.denote]
  refine ⟨s.popFrame s.mem, run_runFunction (s' := s) ?_, hs.popFrame_equiv⟩
  obtain ⟨blk, hblk, hlen⟩ := hp
  dsimp only [fd_ulong_load_8]
  peel_load (.bitvec (.concrete 64)), blk, p, hblk, s
  simp_return
  simp only [readWord, readWord?, MemoryState.live?, hblk, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.get_some]

/-- `fd_ulong_load_8_conforms` in continuation form.

The three facts arrive as lambda binders instead of through `obtain`, which
destructs by `cases` and so reverts and reintroduces the goal once per layer.
That is free on a small goal and is not free on a caller mid-walk: the residual
program is the whole rest of the region, and `fd_curve25519_scalar_reduce` pays
it eight times over. -/
theorem fd_ulong_load_8_conforms_cont {P : Prop} (p : Pointer) (s : GlobalState) (hs : s.WF)
    (hp : Fits s.mem p 64)
    (k :
      ∀ t : GlobalState,
        StateT.run (runFunction (fd_ulong_load_8.denote (Ctxt.Valuation.singleton (.value p)))) s =
            .value ([.value (readWord hp)]ₕ, t) →
          s ≈ t → P) :
    P :=
  let ⟨t, hrun, he⟩ := fd_ulong_load_8_conforms p s hs hp
  k t hrun he

end Firedancer.Common
