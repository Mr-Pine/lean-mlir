import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationInputState
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.MontgomeryTail

/-! Compose all mixed-width input assembly chunks under their actual startup
registers. Every scratch range and input-read preservation premise is derived. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

theorem invocation_input_chunk0 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    List.foldlM Instr.run (startupEnv E g state)
      (((program.entry p g).body.drop 89).take 37) (startupState state) =
      .value (inputEnvs E g state input 0, inputStates state input 0) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have harg' : (startupEnv E g state).read (%arg1) = .value input := by
    change E.args 1 = .value input at harg
    simp [inputEnvs, startupEnv, harg, mlir_env]
  have hc1 : (startupEnv E g state).read (%1) = .value 4#64 := by
    simp [inputEnvs, startupEnv, mlir_env]
  have hc2 : (startupEnv E g state).read (%2) = .value 32#64 := by
    simp [inputEnvs, startupEnv, mlir_env]
  have hc3 : (startupEnv E g state).read (%3) = .value 5#64 := by
    simp [inputEnvs, startupEnv, mlir_env]
  have hc4 : (startupEnv E g state).read (%4) = .value 40#64 := by
    simp [inputEnvs, startupEnv, mlir_env]
  have hc5 : (startupEnv E g state).read (%5) = .value 6#64 := by
    simp [inputEnvs, startupEnv, mlir_env]
  have hc6 : (startupEnv E g state).read (%6) = .value 48#64 := by
    simp [inputEnvs, startupEnv, mlir_env]
  have hc7 : (startupEnv E g state).read (%7) = .value 7#64 := by
    simp [inputEnvs, startupEnv, mlir_env]
  have hc8 : (startupEnv E g state).read (%8) = .value 56#64 := by
    simp [inputEnvs, startupEnv, mlir_env]
  have hc := inputChunk0_run p g (startupEnv E g state) (startupState state) input
    harg' hs hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8
  simpa [inputEnvs, inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one] using hc

theorem invocation_input_chunk1 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    List.foldlM Instr.run (inputEnvs E g state input 0)
      (((program.entry p g).body.drop 126).take 19) (inputStates state input 0) =
      .value (inputEnvs E g state input 1, inputStates state input 1) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have hi := inputStates_range state input input 64 hs 0
  have hf := inputStates_fits state input (slot state 12) 64
    (startup_slot_fits64 state ⟨12, by decide⟩) 0
  have harg' : (inputEnvs E g state input 0).read (%arg1) = .value input := by
    change E.args 1 = .value input at harg
    simp [inputEnvs, startupEnv, inputChunk0Env, harg, mlir_env]
  have hc2 : (inputEnvs E g state input 0).read (%2) = .value 32#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, mlir_env]
  have hc4 : (inputEnvs E g state input 0).read (%4) = .value 40#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, mlir_env]
  have hc6 : (inputEnvs E g state input 0).read (%6) = .value 48#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, mlir_env]
  have hc9 : (inputEnvs E g state input 0).read (%9) = .value 8#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, mlir_env]
  have hc10 : (inputEnvs E g state input 0).read (%10) = .value 12#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, mlir_env]
  have hc11 : (inputEnvs E g state input 0).read (%11) = .value 13#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, mlir_env]
  have hc12 : (inputEnvs E g state input 0).read (%12) = .value 14#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, mlir_env]
  have hp : (inputEnvs E g state input 0).read (%77) = .value (slot state 12) := by
    simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
      Nat.add_assoc, inputChunk0Env, mlir_env]
  have hc := inputChunk1_run p g (inputEnvs E g state input 0) (inputStates state input 0) input
    harg' hi hc2 hc4 hc6 hc9 hc10 hc11 hc12 (slot state 12) hp hf
  have hr8_32 := inputStates_read_caller state input (input.add 8#64) 32 hwf
    (hlive.fits_add (k := 8) (count := 4) (by decide)) 0
  have hr12_8 := inputStates_read_caller state input (input.add 12#64) 8 hwf
    (hlive.fits_add (k := 12) (count := 1) (by decide)) 0
  have hr13_8 := inputStates_read_caller state input (input.add 13#64) 8 hwf
    (hlive.fits_add (k := 13) (count := 1) (by decide)) 0
  have hr14_16 := inputStates_read_caller state input (input.add 14#64) 16 hwf
    (hlive.fits_add (k := 14) (count := 2) (by decide)) 0
  simp only [inputChunk1Env, inputChunk1Word, hr8_32, hr12_8, hr13_8, hr14_16] at hc
  simpa [inputEnvs, inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, inputChunk1Env, inputChunk1Word] using hc

theorem invocation_input_chunk2 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    List.foldlM Instr.run (inputEnvs E g state input 1)
      (((program.entry p g).body.drop 145).take 24) (inputStates state input 1) =
      .value (inputEnvs E g state input 2, inputStates state input 2) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have hi := inputStates_range state input input 64 hs 1
  have hf := inputStates_fits state input (slot state 13) 64
    (startup_slot_fits64 state ⟨13, by decide⟩) 1
  have harg' : (inputEnvs E g state input 1).read (%arg1) = .value input := by
    change E.args 1 = .value input at harg
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, harg, mlir_env]
  have hc2 : (inputEnvs E g state input 1).read (%2) = .value 32#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, mlir_env]
  have hc6 : (inputEnvs E g state input 1).read (%6) = .value 48#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, mlir_env]
  have hc13 : (inputEnvs E g state input 1).read (%13) = .value 16#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, mlir_env]
  have hc14 : (inputEnvs E g state input 1).read (%14) = .value 18#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, mlir_env]
  have hc15 : (inputEnvs E g state input 1).read (%15) = .value 19#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, mlir_env]
  have hc16 : (inputEnvs E g state input 1).read (%16) = .value 24#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, mlir_env]
  have hc17 : (inputEnvs E g state input 1).read (%17) = .value 20#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, mlir_env]
  have hc18 : (inputEnvs E g state input 1).read (%18) = .value 22#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, mlir_env]
  have hp : (inputEnvs E g state input 1).read (%78) = .value (slot state 13) := by
    simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
      Nat.add_assoc, inputChunk0Env, inputChunk1Env, mlir_env]
  have hc := inputChunk2_run p g (inputEnvs E g state input 1) (inputStates state input 1) input
    harg' hi hc2 hc6 hc13 hc14 hc15 hc16 hc17 hc18 (slot state 13) hp hf
  have hr16_16 := inputStates_read_caller state input (input.add 16#64) 16 hwf
    (hlive.fits_add (k := 16) (count := 2) (by decide)) 1
  have hr18_8 := inputStates_read_caller state input (input.add 18#64) 8 hwf
    (hlive.fits_add (k := 18) (count := 1) (by decide)) 1
  have hr19_8 := inputStates_read_caller state input (input.add 19#64) 8 hwf
    (hlive.fits_add (k := 19) (count := 1) (by decide)) 1
  have hr20_16 := inputStates_read_caller state input (input.add 20#64) 16 hwf
    (hlive.fits_add (k := 20) (count := 2) (by decide)) 1
  have hr22_16 := inputStates_read_caller state input (input.add 22#64) 16 hwf
    (hlive.fits_add (k := 22) (count := 2) (by decide)) 1
  simp only [inputChunk2Env, inputChunk2Word, hr16_16, hr18_8, hr19_8, hr20_16, hr22_16] at hc
  simpa [inputEnvs, inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, inputChunk2Env, inputChunk2Word] using hc

theorem invocation_input_chunk3 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    List.foldlM Instr.run (inputEnvs E g state input 2)
      (((program.entry p g).body.drop 169).take 24) (inputStates state input 2) =
      .value (inputEnvs E g state input 3, inputStates state input 3) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have hi := inputStates_range state input input 64 hs 2
  have hf := inputStates_fits state input (slot state 14) 64
    (startup_slot_fits64 state ⟨14, by decide⟩) 2
  have harg' : (inputEnvs E g state input 2).read (%arg1) = .value input := by
    change E.args 1 = .value input at harg
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, harg, mlir_env]
  have hc2 : (inputEnvs E g state input 2).read (%2) = .value 32#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc6 : (inputEnvs E g state input 2).read (%6) = .value 48#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc9 : (inputEnvs E g state input 2).read (%9) = .value 8#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc13 : (inputEnvs E g state input 2).read (%13) = .value 16#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc16 : (inputEnvs E g state input 2).read (%16) = .value 24#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc19 : (inputEnvs E g state input 2).read (%19) = .value 25#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc20 : (inputEnvs E g state input 2).read (%20) = .value 26#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc21 : (inputEnvs E g state input 2).read (%21) = .value 28#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc22 : (inputEnvs E g state input 2).read (%22) = .value 30#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hp : (inputEnvs E g state input 2).read (%79) = .value (slot state 14) := by
    simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
      Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, mlir_env]
  have hc := inputChunk3_run p g (inputEnvs E g state input 2) (inputStates state input 2) input
    harg' hi hc2 hc6 hc9 hc13 hc16 hc19 hc20 hc21 hc22 (slot state 14) hp hf
  have hr24_8 := inputStates_read_caller state input (input.add 24#64) 8 hwf
    (hlive.fits_add (k := 24) (count := 1) (by decide)) 2
  have hr25_8 := inputStates_read_caller state input (input.add 25#64) 8 hwf
    (hlive.fits_add (k := 25) (count := 1) (by decide)) 2
  have hr26_16 := inputStates_read_caller state input (input.add 26#64) 16 hwf
    (hlive.fits_add (k := 26) (count := 2) (by decide)) 2
  have hr28_16 := inputStates_read_caller state input (input.add 28#64) 16 hwf
    (hlive.fits_add (k := 28) (count := 2) (by decide)) 2
  have hr30_16 := inputStates_read_caller state input (input.add 30#64) 16 hwf
    (hlive.fits_add (k := 30) (count := 2) (by decide)) 2
  simp only [inputChunk3Env, inputChunk3Word, hr24_8, hr25_8, hr26_16, hr28_16, hr30_16] at hc
  simpa [inputEnvs, inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, inputChunk3Env, inputChunk3Word] using hc

theorem invocation_input_chunk4 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    List.foldlM Instr.run (inputEnvs E g state input 3)
      (((program.entry p g).body.drop 193).take 24) (inputStates state input 3) =
      .value (inputEnvs E g state input 4, inputStates state input 4) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have hi := inputStates_range state input input 64 hs 3
  have hf := inputStates_fits state input (slot state 15) 64
    (startup_slot_fits64 state ⟨15, by decide⟩) 3
  have harg' : (inputEnvs E g state input 3).read (%arg1) = .value input := by
    change E.args 1 = .value input at harg
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, harg, mlir_env]
  have hc2 : (inputEnvs E g state input 3).read (%2) = .value 32#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hc6 : (inputEnvs E g state input 3).read (%6) = .value 48#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hc9 : (inputEnvs E g state input 3).read (%9) = .value 8#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hc13 : (inputEnvs E g state input 3).read (%13) = .value 16#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hc23 : (inputEnvs E g state input 3).read (%23) = .value 33#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hc24 : (inputEnvs E g state input 3).read (%24) = .value 34#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hc25 : (inputEnvs E g state input 3).read (%25) = .value 36#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hc26 : (inputEnvs E g state input 3).read (%26) = .value 38#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hp : (inputEnvs E g state input 3).read (%80) = .value (slot state 15) := by
    simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
      Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, mlir_env]
  have hc := inputChunk4_run p g (inputEnvs E g state input 3) (inputStates state input 3) input
    harg' hi hc2 hc6 hc9 hc13 hc23 hc24 hc25 hc26 (slot state 15) hp hf
  have hr32_8 := inputStates_read_caller state input (input.add 32#64) 8 hwf
    (hlive.fits_add (k := 32) (count := 1) (by decide)) 3
  have hr33_8 := inputStates_read_caller state input (input.add 33#64) 8 hwf
    (hlive.fits_add (k := 33) (count := 1) (by decide)) 3
  have hr34_16 := inputStates_read_caller state input (input.add 34#64) 16 hwf
    (hlive.fits_add (k := 34) (count := 2) (by decide)) 3
  have hr36_16 := inputStates_read_caller state input (input.add 36#64) 16 hwf
    (hlive.fits_add (k := 36) (count := 2) (by decide)) 3
  have hr38_16 := inputStates_read_caller state input (input.add 38#64) 16 hwf
    (hlive.fits_add (k := 38) (count := 2) (by decide)) 3
  simp only [inputChunk4Env, inputChunk4Word, hr32_8, hr33_8, hr34_16, hr36_16, hr38_16] at hc
  simpa [inputEnvs, inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, inputChunk4Env, inputChunk4Word] using hc

theorem invocation_input_chunk5 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    List.foldlM Instr.run (inputEnvs E g state input 4)
      (((program.entry p g).body.drop 217).take 19) (inputStates state input 4) =
      .value (inputEnvs E g state input 5, inputStates state input 5) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have hi := inputStates_range state input input 64 hs 4
  have hf := inputStates_fits state input (slot state 16) 64
    (startup_slot_fits64 state ⟨16, by decide⟩) 4
  have harg' : (inputEnvs E g state input 4).read (%arg1) = .value input := by
    change E.args 1 = .value input at harg
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, harg, mlir_env]
  have hc2 : (inputEnvs E g state input 4).read (%2) = .value 32#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, mlir_env]
  have hc4 : (inputEnvs E g state input 4).read (%4) = .value 40#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, mlir_env]
  have hc6 : (inputEnvs E g state input 4).read (%6) = .value 48#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, mlir_env]
  have hc27 : (inputEnvs E g state input 4).read (%27) = .value 44#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, mlir_env]
  have hc28 : (inputEnvs E g state input 4).read (%28) = .value 45#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, mlir_env]
  have hc29 : (inputEnvs E g state input 4).read (%29) = .value 46#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, mlir_env]
  have hp : (inputEnvs E g state input 4).read (%81) = .value (slot state 16) := by
    simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
      Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, mlir_env]
  have hc := inputChunk5_run p g (inputEnvs E g state input 4) (inputStates state input 4) input
    harg' hi hc2 hc4 hc6 hc27 hc28 hc29 (slot state 16) hp hf
  have hr40_32 := inputStates_read_caller state input (input.add 40#64) 32 hwf
    (hlive.fits_add (k := 40) (count := 4) (by decide)) 4
  have hr44_8 := inputStates_read_caller state input (input.add 44#64) 8 hwf
    (hlive.fits_add (k := 44) (count := 1) (by decide)) 4
  have hr45_8 := inputStates_read_caller state input (input.add 45#64) 8 hwf
    (hlive.fits_add (k := 45) (count := 1) (by decide)) 4
  have hr46_16 := inputStates_read_caller state input (input.add 46#64) 16 hwf
    (hlive.fits_add (k := 46) (count := 2) (by decide)) 4
  simp only [inputChunk5Env, inputChunk5Word, hr40_32, hr44_8, hr45_8, hr46_16] at hc
  simpa [inputEnvs, inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, inputChunk5Env, inputChunk5Word] using hc

theorem invocation_input_chunk6 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    List.foldlM Instr.run (inputEnvs E g state input 5)
      (((program.entry p g).body.drop 236).take 24) (inputStates state input 5) =
      .value (inputEnvs E g state input 6, inputStates state input 6) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have hi := inputStates_range state input input 64 hs 5
  have hf := inputStates_fits state input (slot state 17) 64
    (startup_slot_fits64 state ⟨17, by decide⟩) 5
  have harg' : (inputEnvs E g state input 5).read (%arg1) = .value input := by
    change E.args 1 = .value input at harg
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, harg, mlir_env]
  have hc2 : (inputEnvs E g state input 5).read (%2) = .value 32#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hc6 : (inputEnvs E g state input 5).read (%6) = .value 48#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hc13 : (inputEnvs E g state input 5).read (%13) = .value 16#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hc16 : (inputEnvs E g state input 5).read (%16) = .value 24#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hc30 : (inputEnvs E g state input 5).read (%30) = .value 50#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hc31 : (inputEnvs E g state input 5).read (%31) = .value 51#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hc32 : (inputEnvs E g state input 5).read (%32) = .value 52#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hc33 : (inputEnvs E g state input 5).read (%33) = .value 54#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hp : (inputEnvs E g state input 5).read (%82) = .value (slot state 17) := by
    simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
      Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, mlir_env]
  have hc := inputChunk6_run p g (inputEnvs E g state input 5) (inputStates state input 5) input
    harg' hi hc2 hc6 hc13 hc16 hc30 hc31 hc32 hc33 (slot state 17) hp hf
  have hr48_16 := inputStates_read_caller state input (input.add 48#64) 16 hwf
    (hlive.fits_add (k := 48) (count := 2) (by decide)) 5
  have hr50_8 := inputStates_read_caller state input (input.add 50#64) 8 hwf
    (hlive.fits_add (k := 50) (count := 1) (by decide)) 5
  have hr51_8 := inputStates_read_caller state input (input.add 51#64) 8 hwf
    (hlive.fits_add (k := 51) (count := 1) (by decide)) 5
  have hr52_16 := inputStates_read_caller state input (input.add 52#64) 16 hwf
    (hlive.fits_add (k := 52) (count := 2) (by decide)) 5
  have hr54_16 := inputStates_read_caller state input (input.add 54#64) 16 hwf
    (hlive.fits_add (k := 54) (count := 2) (by decide)) 5
  simp only [inputChunk6Env, inputChunk6Word, hr48_16, hr50_8, hr51_8, hr52_16, hr54_16] at hc
  simpa [inputEnvs, inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, inputChunk6Env, inputChunk6Word] using hc

theorem invocation_input_chunk7 (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    List.foldlM Instr.run (inputEnvs E g state input 6)
      (((program.entry p g).body.drop 260).take 24) (inputStates state input 6) =
      .value (inputEnvs E g state input 7, inputStates state input 7) := by
  have hs : SmallRange (startupState state).mem input 64 := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_range state hwf input 64 hlive 24
  have hi := inputStates_range state input input 64 hs 6
  have hf := inputStates_fits state input (slot state 18) 64
    (startup_slot_fits64 state ⟨18, by decide⟩) 6
  have harg' : (inputEnvs E g state input 6).read (%arg1) = .value input := by
    change E.args 1 = .value input at harg
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, harg, mlir_env]
  have hc2 : (inputEnvs E g state input 6).read (%2) = .value 32#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc6 : (inputEnvs E g state input 6).read (%6) = .value 48#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc8 : (inputEnvs E g state input 6).read (%8) = .value 56#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc13 : (inputEnvs E g state input 6).read (%13) = .value 16#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc16 : (inputEnvs E g state input 6).read (%16) = .value 24#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc34 : (inputEnvs E g state input 6).read (%34) = .value 58#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc35 : (inputEnvs E g state input 6).read (%35) = .value 59#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc36 : (inputEnvs E g state input 6).read (%36) = .value 60#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc37 : (inputEnvs E g state input 6).read (%37) = .value 62#64 := by
    simp [inputEnvs, startupEnv, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hp : (inputEnvs E g state input 6).read (%83) = .value (slot state 18) := by
    simp [inputEnvs, startupEnv, slot, GlobalState.alloca, GlobalState.allocaPtr,
      Nat.add_assoc, inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, mlir_env]
  have hc := inputChunk7_run p g (inputEnvs E g state input 6) (inputStates state input 6) input
    harg' hi hc2 hc6 hc8 hc13 hc16 hc34 hc35 hc36 hc37 (slot state 18) hp hf
  have hr56_16 := inputStates_read_caller state input (input.add 56#64) 16 hwf
    (hlive.fits_add (k := 56) (count := 2) (by decide)) 6
  have hr58_8 := inputStates_read_caller state input (input.add 58#64) 8 hwf
    (hlive.fits_add (k := 58) (count := 1) (by decide)) 6
  have hr59_8 := inputStates_read_caller state input (input.add 59#64) 8 hwf
    (hlive.fits_add (k := 59) (count := 1) (by decide)) 6
  have hr60_16 := inputStates_read_caller state input (input.add 60#64) 16 hwf
    (hlive.fits_add (k := 60) (count := 2) (by decide)) 6
  have hr62_16 := inputStates_read_caller state input (input.add 62#64) 16 hwf
    (hlive.fits_add (k := 62) (count := 2) (by decide)) 6
  simp only [inputChunk7Env, inputChunk7Word, hr56_16, hr58_8, hr59_8, hr60_16, hr62_16] at hc
  simpa [inputEnvs, inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero', Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, inputChunk7Env, inputChunk7Word] using hc

/-- Entire startup plus 195 actual input-assembly instructions. -/
theorem invocation_input_run (p : Primitives) (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (input : Pointer) (hwf : state.WF)
    (harg : E.read (%arg1) = .value input) (hlive : SmallRange state.mem input 64) :
    (program.entry p g).runBodyFrom E 0 state =
      (program.entry p g).runBodyFrom (inputEnvs E g state input 7) 284
        (inputStates state input 7) := by
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (startup_run p g E state)]
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (invocation_input_chunk0 p g E state input hwf harg hlive)]
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (invocation_input_chunk1 p g E state input hwf harg hlive)]
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (invocation_input_chunk2 p g E state input hwf harg hlive)]
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (invocation_input_chunk3 p g E state input hwf harg hlive)]
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (invocation_input_chunk4 p g E state input hwf harg hlive)]
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (invocation_input_chunk5 p g E state input hwf harg hlive)]
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (invocation_input_chunk6 p g E state input hwf harg hlive)]
  rw [ScalarMontgomeryMul.runBodyFrom_chunk (invocation_input_chunk7 p g E state input hwf harg hlive)]

end Agave.Ed25519.Verifier.Execution.ScalarWide
