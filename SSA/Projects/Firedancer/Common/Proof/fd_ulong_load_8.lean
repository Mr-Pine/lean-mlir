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
      StateT.run (runFunction (fd_ulong_load_8.denote (Ctxt.Valuation.singleton (.value p)))) s
        = .value ([.value (readWord hp)]ₕ, s') ∧ s ≈ s' := by
  simp only [Cfg.denote]
  refine ⟨s.popFrame s.mem, run_runFunction (s' := s) ?_, hs.popFrame_equiv⟩
  obtain ⟨blk, hblk, hlen⟩ := hp
  dsimp only [fd_ulong_load_8]
  peel_load (.bitvec (.concrete 64)), blk, p, hblk, s
  simp_return
  simp only [readWord, readWord?, MemoryState.live?, hblk, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def, Option.get_some]

end Firedancer.Common
