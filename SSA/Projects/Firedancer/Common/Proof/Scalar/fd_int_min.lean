/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import SSA.Projects.Firedancer.Common.Spec.Scalar.fd_int_min
import SSA.Projects.Firedancer.MLIR.DenoteStep
import SSA.Projects.Firedancer.Proof.Tactics

/-!
# `fd_int_min` conforms
-/

namespace Firedancer.Common
open LeanMLIR SLLVM
open InstCombine (LLVM)

theorem fd_int_min_conforms (x : LLVM.IntW 32) (s : GlobalState) (hs : s.WF) :
    fd_int_min_spec x s := by
  simp only [fd_int_min_spec, Cfg.denote]
  refine ⟨s.popFrame s.mem, run_runFunction (s' := s) ?_, hs.popFrame_equiv⟩
  denote_step_all v 1
  denote_eval v 0 1
  simp only [LLVM.const?, Ctxt.Valuation.singleton, simp_denote] at hv0 hv1
  subst hv0
  subst hv1
  simp_return

end Firedancer.Common
