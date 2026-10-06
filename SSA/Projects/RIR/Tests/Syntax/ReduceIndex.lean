import SSA.Projects.RIR.Syntax.Elab
import SSA.Projects.RIR.Run.Tactic

namespace LeanMLIR.RIR.Tests.ReduceIndex
open LeanMLIR.RIR

/-- Three blocks force nested dependent `Fin.cases` in the imported block
parameters, while stepping normalizes the unrelated instruction index 0+1. -/
mlir_def three_blocks := {
  ^bb0(%arg0: i64):
    %0 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    "llvm.br"(%arg0)[^bb1] : (i64) -> ()
  ^bb1(%1: i64):
    %2 = "llvm.add"(%1, %0) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    "llvm.br"()[^bb2] : () -> ()
  ^bb2:
    "llvm.return"(%2) : (i64) -> ()
}

theorem three_blocks_call (x : BitVec 64) (s : GlobalState) (hwf : s.WF) :
    three_blocks.call (three_blocks.args (.value x)) s =
      .value (.cons (.value (x + 1)) .nil, s) := by
  func_init
  block_init
  step_pure
  finish_block
  block_init
  step_pure
  finish_block
  block_init
  finish_block
  rw [hS]
  rfl

end LeanMLIR.RIR.Tests.ReduceIndex
