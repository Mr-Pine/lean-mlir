import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationByteStores

/-! Instantiate the final 31 zeroization/lifetime instructions. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem byteStoresEnv_read_early (E : Env program.Γ) (out : Pointer)
    (i : Fin program.Γ.n) (ht : program.Γ.ty i = t) (hi : i.val < 425) :
    (byteStoresEnv E out).read (.val i ht) = E.read (.val i ht) := by
  unfold byteStoresEnv
  repeat' rw [Env.read_write_ne _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega)]

theorem invocation_finalCleanup_run (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (out input : Pointer) (bytes : BitVec 512) :
    (program.entry linkedPrimitives g).runBodyFrom
        (byteStoresEnv (serializePhaseEnv E g state input bytes) out) 576
        (byteState g state out input bytes) =
      .value (returnEnv E g state out input bytes, returnState g state out input bytes) := by
  apply finalCleanup_run linkedPrimitives g _ _ (zeroSlots state) (resultSlots state)
  · exact fun i => (byteState_range g state out input _ bytes 8 (startup_zero_range state i)).fits
  · exact fun i => (byteState_range g state out input _ bytes 8 (startup_result_range state i)).fits
  all_goals
    rw [byteStoresEnv_read_early, serializePhaseEnv, serializeEnv_read_early, subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
      first | omega | simp [zeroSlots, resultSlots, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]

end Agave.Ed25519.Verifier.Execution.ScalarWide
