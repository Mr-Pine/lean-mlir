import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationResultRead
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationSlots

/-! Derive the complete addition/black-box/subtraction/result-store phase from
the two actual call outputs and startup registers. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
attribute [local irreducible] lowWords highWords

theorem sumEnv_read_early (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (i : Fin program.Γ.n) (ht : program.Γ.ty i = t) (hi : i.val < 285) :
    (sumEnv E a b).read (.val i ht) = E.read (.val i ht) := by
  unfold sumEnv
  repeat' rw [Env.read_write_ne _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega)]

theorem wrapperSubtractEnv_read_early (E : Env program.Γ) (x : Fin 5 → BitVec 52)
    (i : Fin program.Γ.n) (ht : program.Γ.ty i = t) (hi : i.val < 313) :
    (wrapperSubtractEnv E x).read (.val i ht) = E.read (.val i ht) := by
  unfold wrapperSubtractEnv wrapperAddbackEnv wrapperBorrowEnv
  repeat' rw [Env.read_write_ne _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega)]

theorem invocation_sum_run (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) :
    (program.entry linkedPrimitives g).runBodyFrom (splitInputEnv E g state input bytes) 330
        (bothCallState g state input bytes) =
      (program.entry linkedPrimitives g).runBodyFrom (sumPhaseEnv E g state input bytes) 358
        (bothCallState g state input bytes) := by
  apply ScalarMontgomeryMul.runBodyFrom_chunk (count := 28)
  apply sum_run linkedPrimitives g _ _ (lowWords g state bytes) (highWords g state bytes)
    (slot state 10) (slot state 9)
  · exact bothCallState_range g state input _ bytes 40 (startup_slot_range state ⟨10, by decide⟩)
  · exact bothCallState_range g state input _ bytes 40 (startup_slot_range state ⟨9, by decide⟩)
  · exact bothCallState_low_read g state input bytes
  · exact bothCallState_high_read g state input bytes
  all_goals simp [splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]

theorem invocation_subtract_ready (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) :
    WrapperSubtractReady (sumPhaseEnv E g state input bytes)
      (sum52 (lowWords g state bytes) (highWords g state bytes)) := by
  have hw := sumEnv_words (splitInputEnv E g state input bytes)
    (lowWords g state bytes) (highWords g state bytes)
  constructor
  · simpa only [sumPhaseEnv, sum52_widen] using hw.1
  · simpa only [sumPhaseEnv, sum52_widen] using hw.2.1
  · simpa only [sumPhaseEnv, sum52_widen] using hw.2.2.1
  · simpa only [sumPhaseEnv, sum52_widen] using hw.2.2.2.1
  · simpa only [sumPhaseEnv, sum52_widen] using hw.2.2.2.2
  all_goals
    rw [sumPhaseEnv, sumEnv_read_early] <;> first | omega | simp [splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]

theorem invocation_result_run (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) (hwf : state.WF) :
    (program.entry linkedPrimitives g).runBodyFrom (sumPhaseEnv E g state input bytes) 358
        (bothCallState g state input bytes) =
      (program.entry linkedPrimitives g).runBodyFrom (subtractPhaseEnv E g state input bytes) 405
        (resultState g state input bytes) := by
  have hr := invocation_subtract_ready g E state input bytes
  have hsub := wrapper_subtract_run g (sumPhaseEnv E g state input bytes)
    (bothCallState g state input bytes) (sum52 (lowWords g state bytes) (highWords g state bytes))
    hr (bothCallState_wf g state input bytes hwf)
  have hs : ∀ i, Fits (bothCallState g state input bytes).mem (resultSlots state i) 64 :=
    fun i => (bothCallState_range g state input _ bytes 8 (startup_result_range state i)).fits
  have hw := wrapperSubtractEnv_words (sumPhaseEnv E g state input bytes)
    (sum52 (lowWords g state bytes) (highWords g state bytes))
  have hstores : List.foldlM Instr.run (subtractPhaseEnv E g state input bytes)
      (((program.entry linkedPrimitives g).body.drop 400).take 5)
      {bothCallState g state input bytes with alloc := ((bothCallState g state input bytes).alloca 1).alloc} =
      .value (subtractPhaseEnv E g state input bytes, resultState g state input bytes) := by
    apply resultSlots_run linkedPrimitives g _ _ (resultSlots state) (finalWords g state bytes)
    · exact hs
    · rw [subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
        first | omega | simp [resultSlots, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
    · rw [subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
        first | omega | simp [resultSlots, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
    · rw [subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
        first | omega | simp [resultSlots, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
    · rw [subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
        first | omega | simp [resultSlots, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
    · rw [subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
        first | omega | simp [resultSlots, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
    · exact hw.1
    · exact hw.2.1
    · exact hw.2.2.1
    · exact hw.2.2.2.1
    · exact hw.2.2.2.2
  rw [hsub]
  exact ScalarMontgomeryMul.runBodyFrom_chunk hstores

end Agave.Ed25519.Verifier.Execution.ScalarWide
