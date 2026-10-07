import SSA.Projects.RIR.Syntax.Elab
import SSA.Projects.RIR.Run.Tactic

/-! GEP operands must be resolved before the environment is sealed. The
liveness scan already finds registers nested under `GepIndex.scaled`; the
index-reading helpers must also expose their reads to the step simplifier. -/

namespace LeanMLIR.RIR.Tests.GepLiveness
open Lean Meta Elab Tactic

-- %0 and %1 are used only as GEP indices; %2 is genuinely dead.
mlir_def nested := {
  ^bb0(%arg0: !llvm.ptr, %arg1: i64, %arg2: i32):
    %0 = "llvm.add"(%arg1, %arg1) <{overflowFlags = #llvm.overflow<none>}> : (i64, i64) -> i64
    %1 = "llvm.add"(%arg2, %arg2) <{overflowFlags = #llvm.overflow<none>}> : (i32, i32) -> i32
    %2 = "llvm.mlir.constant"() <{value = 99 : i64}> : () -> i64
    %3 = "llvm.getelementptr"(%arg0, %0, %1) <{elem_type = !llvm.struct<(i8, array<2 x i64>)>, rawConstantIndices = array<i32: -2147483648, 1, -2147483648>}> : (!llvm.ptr, i64, i32) -> !llvm.ptr
    "llvm.return"(%3) : (!llvm.ptr) -> ()
}

-- A folded constant has no register dependency, even with checked GEP flags.
mlir_def folded := {
  ^bb0(%arg0: !llvm.ptr):
    %0 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %1 = "llvm.mlir.constant"() <{value = 99 : i64}> : () -> i64
    %2 = "llvm.getelementptr"(%arg0, %0) <{elem_type = i8, noWrapFlags = 7 : i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.return"(%2) : (!llvm.ptr) -> ()
}

run_elab do
  let parts ← LeanMLIR.RIR.blockParts (mkConst ``nested.entry) (mkNatLit 2)
  let live ← LeanMLIR.RIR.exposedRegs parts
  unless live.size == 2 && live.contains 0 && live.contains 1 do
    throwError "nested GEP liveness mismatch: {live.toArray}"
  let parts ← LeanMLIR.RIR.blockParts (mkConst ``folded.entry) (mkNatLit 1)
  let live ← LeanMLIR.RIR.exposedRegs parts
  unless live.isEmpty do
    throwError "folded constant unexpectedly live: {live.toArray}"

example (env : ⟪nested.Γ⟫) (i : BitVec 64) :
    GepIndex.inboundsOffset (env.write ⟨0, rfl⟩ (.value i))
      (.scaled 24 (.val 0 rfl)) = Operation.gepInboundsIndex 24 (.value i) := by
  simp only [mlir_env]

-- Before the fix, stepping the GEP left `GepIndex.offset E₀ (.scaled ... %0)`
-- and the corresponding %1 expression in the result. The reads had not been
-- resolved before sealing abstracted E₀, so this whole-call proof failed.
theorem nested_call (p : Pointer) (i : BitVec 64) (j : BitVec 32)
    (s : GlobalState) (hwf : s.WF) :
    nested.call (nested.args (.value p) (.value i) (.value j)) s =
      .value (.cons (Operation.gepUnflagged (.value p)
        [Operation.gepIndex 24 (.value (i + i)), .value 8,
         Operation.gepIndex 8 (.value (j + j))]) .nil, s) := by
  func_init
  block_init
  step_pure
  step_pure
  step_pure
  step_pure
  finish_block
  rw [hS]
  rfl

end LeanMLIR.RIR.Tests.GepLiveness
