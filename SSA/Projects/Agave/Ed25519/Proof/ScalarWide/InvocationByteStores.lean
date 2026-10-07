import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationSerialize

/-! Instantiate all 32 emitted byte stores under the original output range. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
attribute [local irreducible] lowWords highWords finalWords

theorem serializeEnv_read_early (E : Env program.Γ) (words : Fin 5 → BitVec 64)
    (i : Fin program.Γ.n) (ht : program.Γ.ty i = t) (hi : i.val < 355) :
    (serializeEnv E words).read (.val i ht) = E.read (.val i ht) := by
  unfold serializeEnv
  repeat' rw [Env.read_write_ne _ _ (by
    intro h
    have hv := congrArg Fin.val h
    simp only at hv
    omega)]

private theorem sumEnv_read_arg (E : Env program.Γ) (a b : Fin 5 → BitVec 64)
    (i : Fin program.Γ.args.length) (ht : program.Γ.args[i] = t) :
    (sumEnv E a b).read (.arg i ht) = E.read (.arg i ht) := by
  simp only [sumEnv, Env.read_write_arg]

private theorem wrapperSubtractEnv_read_arg (E : Env program.Γ) (x : Fin 5 → BitVec 52)
    (i : Fin program.Γ.args.length) (ht : program.Γ.args[i] = t) :
    (wrapperSubtractEnv E x).read (.arg i ht) = E.read (.arg i ht) := by
  simp only [wrapperSubtractEnv, wrapperAddbackEnv, wrapperBorrowEnv, Env.read_write_arg]

private theorem serializeEnv_read_arg (E : Env program.Γ) (words : Fin 5 → BitVec 64)
    (i : Fin program.Γ.args.length) (ht : program.Γ.args[i] = t) :
    (serializeEnv E words).read (.arg i ht) = E.read (.arg i ht) := by
  simp only [serializeEnv, Env.read_write_arg]

private def serializeByteReg : Fin 32 → Reg program.Γ (.bv 8) :=
  ![%356, %358, %360, %362, %364, %366, %371, %373, %375, %377, %379, %381, %383, %385, %387, %389, %391, %393, %395, %400, %402, %404, %406, %408, %410, %412, %414, %416, %418, %420, %422, %424]

private theorem serializeEnv_read_byte (E : Env program.Γ) (words : Fin 5 → BitVec 64)
    (i : Fin 32) :
    (serializeEnv E words).read (serializeByteReg i) = .value (serializedBytes words i) := by
  fin_cases i <;> rfl

theorem invocation_byteStores_run (g : Globals) (E : Env program.Γ) (state : GlobalState)
    (out input : Pointer) (bytes : BitVec 512) (hwf : state.WF)
    (harg : E.read (%arg0) = .value out) (hout : SmallRange state.mem out 32) :
    (program.entry linkedPrimitives g).runBodyFrom (serializePhaseEnv E g state input bytes) 513
        (inputCleanState g state input bytes) =
      (program.entry linkedPrimitives g).runBodyFrom
        (byteStoresEnv (serializePhaseEnv E g state input bytes) out) 576
        (byteState g state out input bytes) := by
  have hs : SmallRange (startupState state).mem out 32 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf out 32 hout 24
  apply ScalarMontgomeryMul.runBodyFrom_chunk (count := 63)
  apply byteStores_run linkedPrimitives g _ _ out (serializedBytes (finalWords g state bytes))
  · rw [serializePhaseEnv, serializeEnv_read_arg, subtractPhaseEnv, wrapperSubtractEnv_read_arg,
      sumPhaseEnv, sumEnv_read_arg]
    change E.args 0 = .value out at harg
    simpa [splitInputEnv, splitEnv, inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env,
      inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env,
      mlir_env] using harg
  · exact inputCleanState_range g state input out bytes 32 hs
  · exact serializeEnv_read_byte _ _ 0
  · exact serializeEnv_read_byte _ _ 1
  · exact serializeEnv_read_byte _ _ 2
  · exact serializeEnv_read_byte _ _ 3
  · exact serializeEnv_read_byte _ _ 4
  · exact serializeEnv_read_byte _ _ 5
  · exact serializeEnv_read_byte _ _ 6
  · exact serializeEnv_read_byte _ _ 7
  · exact serializeEnv_read_byte _ _ 8
  · exact serializeEnv_read_byte _ _ 9
  · exact serializeEnv_read_byte _ _ 10
  · exact serializeEnv_read_byte _ _ 11
  · exact serializeEnv_read_byte _ _ 12
  · exact serializeEnv_read_byte _ _ 13
  · exact serializeEnv_read_byte _ _ 14
  · exact serializeEnv_read_byte _ _ 15
  · exact serializeEnv_read_byte _ _ 16
  · exact serializeEnv_read_byte _ _ 17
  · exact serializeEnv_read_byte _ _ 18
  · exact serializeEnv_read_byte _ _ 19
  · exact serializeEnv_read_byte _ _ 20
  · exact serializeEnv_read_byte _ _ 21
  · exact serializeEnv_read_byte _ _ 22
  · exact serializeEnv_read_byte _ _ 23
  · exact serializeEnv_read_byte _ _ 24
  · exact serializeEnv_read_byte _ _ 25
  · exact serializeEnv_read_byte _ _ 26
  · exact serializeEnv_read_byte _ _ 27
  · exact serializeEnv_read_byte _ _ 28
  · exact serializeEnv_read_byte _ _ 29
  · exact serializeEnv_read_byte _ _ 30
  · exact serializeEnv_read_byte _ _ 31
  all_goals
    rw [serializePhaseEnv, serializeEnv_read_early, subtractPhaseEnv, wrapperSubtractEnv_read_early, sumPhaseEnv, sumEnv_read_early] <;>
      first | omega | simp [ splitInputEnv, splitEnv, inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]

end Agave.Ed25519.Verifier.Execution.ScalarWide
