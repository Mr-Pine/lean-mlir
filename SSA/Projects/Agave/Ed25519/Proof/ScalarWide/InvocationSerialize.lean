import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationCleanup

/-! Instantiate all five scalar loads and 65 serialization operations. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem invocation_serialize_run (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) :
    (program.entry linkedPrimitives g).runBodyFrom (subtractPhaseEnv E g state input bytes) 443
        (inputCleanState g state input bytes) =
      (program.entry linkedPrimitives g).runBodyFrom (serializePhaseEnv E g state input bytes) 513
        (inputCleanState g state input bytes) := by
  apply ScalarMontgomeryMul.runBodyFrom_chunk (count := 70)
  apply serialize_run linkedPrimitives g _ _ (finalWords g state bytes) (resultSlots state)
  · exact fun i => (inputCleanState_range g state input _ bytes 8 (startup_result_range state i)).fits
  · exact inputCleanState_read g state input bytes
  all_goals
    rw [subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
      first | omega | simp [resultSlots, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]

end Agave.Ed25519.Verifier.Execution.ScalarWide
