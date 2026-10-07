import SSA.Projects.Agave.Ed25519.Proof.ScalarReduce32.Program
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBox

namespace Agave.Ed25519.ScalarReduce32.Execution
open LeanMLIR.RIR
set_option maxRecDepth 10000

/-- The exact linked callee preserves the byte and caller memory, while its
private allocation advances the same allocator used by the scalar reducer. -/
theorem subtract_black_box (E : Env program.Γ) (state : GlobalState)
    (byte : BitVec 8) (hwf : state.WF)
    (hbyte : E.read (%326) = .value byte) :
    List.foldlM Instr.run E ((program.entry.body.drop 376).take 1) state =
      .value (E[%327 := .value byte], {state with alloc := (state.alloca 1).alloc}) := by
  have hcall := Encoding.Decompress.Execution.BlackBox.program_call byte state hwf
  dsimp only [Encoding.Decompress.Execution.BlackBox.program.args] at hcall
  simp [program.entry, List.foldlM_cons, List.foldlM_nil, Instr.run,
    hbyte, hcall, Env.writeMany_cons, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect]

end Agave.Ed25519.ScalarReduce32.Execution
