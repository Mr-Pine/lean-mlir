import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationInputPhase
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.SplitStores
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperFrame
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationGlobals

/-! Instantiate the exact input split from original bytes and the invocation
startup state, without assuming any phase execution or intermediate register. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def splitState (state : GlobalState) (input : Pointer) (bytes : BitVec 512) : GlobalState :=
  {inputStates state input 7 with mem := splitStores (inputStates state input 7).mem (slot state 10) (slot state 9) bytes}

def splitInputEnv (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) : Env program.Γ :=
  splitEnv (inputEnvs E g state input 7) (slot state 10) (slot state 9) bytes

theorem invocation_split_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (bytes : BitVec 512)
    (hwf : state.WF) (harg : E.read (%arg1) = .value input)
    (hlive : SmallRange state.mem input 64) (hread : state.mem.readAt input 512 = bytes) :
    (program.entry p g).runBodyFrom E 0 state =
      (program.entry p g).runBodyFrom (splitInputEnv E g state input bytes) 320
        (splitState state input bytes) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have hsread : (startupState state).mem.readAt input 512 = bytes := by
    rw [startupState_eq_wrapperAllocSteps,
      wrapperAllocSteps_read state hwf input 512 hlive.fits 24, hread]
  have hv105 : (inputEnvs E g state input 7).read (%105) =
      .value (inputFragment bytes 0 56 0) := by
    have h := inputFragment_reg105 (startupEnv E g state) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv110 : (inputEnvs E g state input 7).read (%110) =
      .value (inputFragment bytes 0 64 0) := by
    have h := inputFragment_reg110 (startupEnv E g state) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv118 : (inputEnvs E g state input 7).read (%118) =
      .value (inputFragment bytes 64 40 0) := by
    have h := inputFragment_reg118 (inputEnvs E g state input 0) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv127 : (inputEnvs E g state input 7).read (%127) =
      .value (inputFragment bytes 104 24 40) := by
    have h := inputFragment_reg127 (inputEnvs E g state input 0) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv141 : (inputEnvs E g state input 7).read (%141) =
      .value (inputFragment bytes 128 32 0) := by
    have h := inputFragment_reg141 (inputEnvs E g state input 1) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv151 : (inputEnvs E g state input 7).read (%151) =
      .value (inputFragment bytes 128 64 0) := by
    have h := inputFragment_reg151 (inputEnvs E g state input 1) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv159 : (inputEnvs E g state input 7).read (%159) =
      .value (inputFragment bytes 192 16 0) := by
    have h := inputFragment_reg159 (inputEnvs E g state input 2) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv173 : (inputEnvs E g state input 7).read (%173) =
      .value (inputFragment bytes 208 48 16) := by
    have h := inputFragment_reg173 (inputEnvs E g state input 2) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv177 : (inputEnvs E g state input 7).read (%177) =
      .value (inputFragment bytes 256 8 0) := by
    have h := inputFragment_reg177 (inputEnvs E g state input 3) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv195 : (inputEnvs E g state input 7).read (%195) =
      .value (inputFragment bytes 304 16 48) := by
    have h := inputFragment_reg195 (inputEnvs E g state input 3) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv197 : (inputEnvs E g state input 7).read (%197) =
      .value (inputFragment bytes 256 64 0) := by
    have h := inputFragment_reg197 (inputEnvs E g state input 3) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv210 : (inputEnvs E g state input 7).read (%210) =
      .value (inputFragment bytes 320 48 0) := by
    have h := inputFragment_reg210 (inputEnvs E g state input 4) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv215 : (inputEnvs E g state input 7).read (%215) =
      .value (inputFragment bytes 320 64 0) := by
    have h := inputFragment_reg215 (inputEnvs E g state input 4) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv228 : (inputEnvs E g state input 7).read (%228) =
      .value (inputFragment bytes 384 32 0) := by
    have h := inputFragment_reg228 (inputEnvs E g state input 5) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv237 : (inputEnvs E g state input 7).read (%237) =
      .value (inputFragment bytes 416 32 32) := by
    have h := inputFragment_reg237 (inputEnvs E g state input 5) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv246 : (inputEnvs E g state input 7).read (%246) =
      .value (inputFragment bytes 448 24 0) := by
    have h := inputFragment_reg246 (inputEnvs E g state input 6) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hv261 : (inputEnvs E g state input 7).read (%261) =
      .value (inputFragment bytes 448 64 0) := by
    have h := inputFragment_reg261 (inputEnvs E g state input 6) (startupState state).mem input bytes hs hsread
    simpa [inputEnvs, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_fin_one,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env] using h
  have hl := inputStates_range state input (slot state 10) 40
    (startup_slot_range state ⟨10, by decide⟩) 7
  have hh := inputStates_range state input (slot state 9) 40
    (startup_slot_range state ⟨9, by decide⟩) 7
  have hsplit : List.foldlM Instr.run (inputEnvs E g state input 7)
      (((program.entry p g).body.drop 284).take 36) (inputStates state input 7) =
      .value (splitInputEnv E g state input bytes, splitState state input bytes) := by
    apply split_run p g (inputEnvs E g state input 7) (inputStates state input 7)
      (slot state 10) (slot state 9) bytes
    · simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
        Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
    · simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
        Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
    · exact hl
    · exact hh
    · exact hv105
    · exact hv110
    · exact hv118
    · exact hv127
    · exact hv141
    · exact hv151
    · exact hv159
    · exact hv173
    · exact hv177
    · exact hv195
    · exact hv197
    · exact hv210
    · exact hv215
    · exact hv228
    · exact hv237
    · exact hv246
    · exact hv261
    all_goals simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
  rw [invocation_input_run p g E state input hwf harg hlive]
  exact ScalarMontgomeryMul.runBodyFrom_chunk hsplit

theorem splitState_erase (state : GlobalState) (input : Pointer) (bytes : BitVec 512)
    (hwf : state.WF) :
    (splitState state input bytes).mem.eraseFrom state.alloc.nextFreeBlock = state.mem := by
  rw [splitState, splitStores_erase _ _ _ _ _ (slot_local state 10) (slot_local state 9),
    inputStates_erase state input hwf 7]

theorem splitState_ready (g : Globals) (state : GlobalState) (out input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) (hr : Ready g state out) :
    Ready g (splitState state input bytes) out :=
  ready_of_erase g state _ out hwf hr (splitState_erase state input bytes hwf)

end Agave.Ed25519.Verifier.Execution.ScalarWide
