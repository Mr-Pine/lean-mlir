module

public import SSA.Projects.RIR.Syntax.Elab
import all SSA.Projects.RIR.Semantics.Func
meta import SSA.Projects.RIR.Semantics.Func

/-! Zeroization fences are kept in the instruction stream. Their effects are
proved only in sequential RIR, without concurrent threads or signal handlers.
Other fence orders and scopes remain rejected. -/
namespace LeanMLIR.RIR.Tests.Syntax.SingleThreadFence
@[expose] public section

mlir_def fenced := {
  ^bb0(%arg0: i64):
    "llvm.fence"() <{ordering = 7 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.return"(%arg0) : (i64) -> ()
}

example : fenced.entry.body = [.fenceSingleThread] := rfl

theorem instruction_run (env : ⟪fenced.Γ⟫) (state : GlobalState) :
    Instr.run env (fenced.entry.body[0]'(by decide)) state = .value (env, state) := rfl

/-- error: ^bb0: "llvm.fence"() : () -> (): only seq_cst singlethread fences are supported -/
#guard_msgs in
mlir_def systemFence := {
  ^bb0:
    "llvm.fence"() <{ordering = 7 : i64}> : () -> ()
    "llvm.return"() : () -> ()
}

/-- error: ^bb0: "llvm.fence"() : () -> (): only seq_cst singlethread fences are supported -/
#guard_msgs in
mlir_def weakerFence := {
  ^bb0:
    "llvm.fence"() <{ordering = 4 : i64, syncscope = "singlethread"}> : () -> ()
    "llvm.return"() : () -> ()
}

end
end LeanMLIR.RIR.Tests.Syntax.SingleThreadFence
