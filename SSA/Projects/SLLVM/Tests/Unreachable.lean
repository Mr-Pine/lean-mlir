/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.SLLVM.Cfg

namespace LeanMLIR.SLLVM.Tests.Unreachable
open LeanMLIR

/-- Quotation retains the trap block, even when its predecessor takes the
other branch. This exercises parsing and reification, not a hand-built CFG. -/
def branch : Cfg (Ctxt.ofList [SLLVM.Ty.bitvec 1]) [] := [sllvm_cfg| {
  ^bb0(%condition: i1):
    "llvm.cond_br"(%condition)[^bb1, ^bb2]
      <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    "llvm.unreachable"() : () -> ()
  ^bb2:
    "llvm.return"() : () -> ()
}]

theorem eval_reachable (s : GlobalState) :
    branch.eval 1 (Ctxt.Valuation.singleton (.value 1#1)) s = some .poison := by
  simp [branch, Cfg.eval, BlockCom.eval, Blocks.next, Blocks.iterate,
    Blocks.get, Terminator.denote, Target.denote,
    Ctxt.Valuation.singleton, Fuel.andThen]

theorem eval_dead (s : GlobalState) :
    branch.eval 1 (Ctxt.Valuation.singleton (.value 0#1)) s =
      some (.value ([]ₕ, s)) := by
  simp [branch, Cfg.eval, BlockCom.eval, Blocks.next, Blocks.iterate,
    Blocks.get, Terminator.denote, Target.denote,
    Ctxt.Valuation.singleton, Fuel.andThen]

theorem denote_reachable (s : GlobalState) :
    StateT.run (branch.denote (Ctxt.Valuation.singleton (.value 1#1))) s = .poison :=
  Cfg.eval_sound (eval_reachable s)

theorem denote_dead (s : GlobalState) :
    StateT.run (branch.denote (Ctxt.Valuation.singleton (.value 0#1))) s =
      .value ([]ₕ, s) :=
  Cfg.eval_sound (eval_dead s)

end LeanMLIR.SLLVM.Tests.Unreachable
