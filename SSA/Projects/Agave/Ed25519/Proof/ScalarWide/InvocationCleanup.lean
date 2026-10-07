import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationSum

/-! Instantiate every cleanup instruction before serialization. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem invocation_inputCleanup_run (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) :
    (program.entry linkedPrimitives g).runBodyFrom (subtractPhaseEnv E g state input bytes) 405
        (resultState g state input bytes) =
      (program.entry linkedPrimitives g).runBodyFrom (subtractPhaseEnv E g state input bytes) 443
        (inputCleanState g state input bytes) := by
  apply ScalarMontgomeryMul.runBodyFrom_chunk (count := 38)
  apply inputCleanup_run linkedPrimitives g _ _ (inputSlots state)
    (slot state 6) (slot state 5) (slot state 10) (slot state 9)
  · exact fun i => (resultState_range g state input _ bytes 8 (startup_input_range state i)).fits
  · exact (resultState_range g state input _ bytes 40 (startup_slot_range state ⟨6, by decide⟩)).fits
  · exact (resultState_range g state input _ bytes 40 (startup_slot_range state ⟨5, by decide⟩)).fits
  · exact (resultState_range g state input _ bytes 40 (startup_slot_range state ⟨10, by decide⟩)).fits
  · exact (resultState_range g state input _ bytes 40 (startup_slot_range state ⟨9, by decide⟩)).fits
  · exact slot_ne state 10 6 (by decide)
  · exact slot_ne state 9 5 (by decide)
  all_goals
    rw [subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
      first | omega | simp [inputSlots, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]

end Agave.Ed25519.Verifier.Execution.ScalarWide
