/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.SHA.fd_ulong_bswap
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics
import SSA.Projects.Firedancer.Proof.Memory

/-!
# `fd_ulong_bswap` and `fd_ulong_rotate_right` conform

One instruction each, and both pure, so the walk is the whole proof: step, read
the value off, and note that a region which allocates nothing and stores nothing
returns the state it was handed.
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fd_ulong_bswap_conforms (x : BitVec 64) (s : GlobalState) (hs : s.WF) :
    fd_ulong_bswap_spec x s := by
  simp only [fd_ulong_bswap_spec, Cfg.denote]
  refine ⟨s.popFrame s.mem, run_runFunction (s' := s) ?_, hs.popFrame_equiv⟩
  denote_step_all v 0
  denote_eval v 0 0
  simp only [SLLVM.bswap, Ctxt.Valuation.singleton, simp_denote, simp_sllvm] at hv0
  subst hv0
  simp_return

theorem fd_ulong_rotate_right_conforms (x : BitVec 64) (n : BitVec 32) (s : GlobalState)
    (hs : s.WF) : fd_ulong_rotate_right_spec x n s := by
  simp only [fd_ulong_rotate_right_spec, Cfg.denote]
  refine ⟨s.popFrame s.mem, run_runFunction (s' := s) ?_, hs.popFrame_equiv⟩
  denote_step_all v 1
  denote_eval v 0 1
  simp only [SLLVM.fshr, LLVM.zext, LLVM.zext?,
    simp_denote, simp_sllvm] at hv0 hv1
  subst hv0
  subst hv1
  simp_return

end Firedancer.Common
