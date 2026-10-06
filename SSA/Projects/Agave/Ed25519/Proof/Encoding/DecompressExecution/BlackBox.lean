import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.BlackBoxProgram
import SSA.Projects.RIR.Run.Tactic
import SSA.Projects.RIR.Run.Memory

/-!
The exact extracted subtle black_box body returns the byte unchanged and leaves
caller memory unchanged. The volatile attribute remains present in the imported
region. RIR models its sequential memory value as an ordinary load; this theorem
does not claim volatile-event or concurrent-memory trace equivalence.
-/
namespace Agave.Ed25519.Encoding.Decompress.Execution.BlackBox
open LeanMLIR.RIR

theorem program_call (byte : BitVec 8) (state : GlobalState) (hwf : state.WF) :
    program.call (program.args (.value byte)) state =
      .value (.cons (.value byte) .nil, {state with alloc := (state.alloca 1).alloc}) := by
  rw [Func.call_eq_run_bind, Func.run_runFrom_eq]
  extract_state
  extract_env
  have hwf₀ : S₀.WF := by rw [← hS]; exact hwf
  block_init
  step_pure
  step_alloca with slot
  step_store
  step_load
  finish_block
  rw [hS]
  subst_vars
  erase_frame

end Agave.Ed25519.Encoding.Decompress.Execution.BlackBox
