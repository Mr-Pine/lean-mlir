import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationCallMemory

/-! Instantiate both Montgomery calls and copies from the original invocation
and its immutable initialized globals. No intermediate call premise remains. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

def lowCallState (g : Globals) (state : GlobalState) (input : Pointer) (bytes : BitVec 512) : GlobalState :=
  montgomeryCopyState (splitState state input bytes) (lowSplitWords bytes) rWords
    (slot state 8) (slot state 10) g.address0

def bothCallState (g : Globals) (state : GlobalState) (input : Pointer) (bytes : BitVec 512) : GlobalState :=
  montgomeryCopyState (lowCallState g state input bytes) (highSplitWords bytes) rrWords
    (slot state 7) (slot state 9) g.address1

theorem lowCallState_range (g : Globals) (state : GlobalState) (input q : Pointer)
    (bytes : BitVec 512) (count : Nat) (h : SmallRange (startupState state).mem q count) :
    SmallRange (lowCallState g state input bytes).mem q count :=
  montgomeryCopyState_range _ _ _ _ _ _ q count (splitState_range state input q bytes count h)

theorem bothCallState_range (g : Globals) (state : GlobalState) (input q : Pointer)
    (bytes : BitVec 512) (count : Nat) (h : SmallRange (startupState state).mem q count) :
    SmallRange (bothCallState g state input bytes).mem q count :=
  montgomeryCopyState_range _ _ _ _ _ _ q count (lowCallState_range g state input q bytes count h)

theorem lowCallState_wf (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) : (lowCallState g state input bytes).WF :=
  montgomeryCopyState_wf _ _ _ _ _ _ (splitState_wf state input bytes hwf)

theorem bothCallState_wf (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) : (bothCallState g state input bytes).WF :=
  montgomeryCopyState_wf _ _ _ _ _ _ (lowCallState_wf g state input bytes hwf)

theorem lowCallState_erase (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) :
    (lowCallState g state input bytes).mem.eraseFrom state.alloc.nextFreeBlock = state.mem := by
  rw [lowCallState, montgomeryCopyState_erase _ _ _ _ _ _ _ (slot_local state 8) (slot_local state 10),
    splitState_erase state input bytes hwf]

theorem bothCallState_erase (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) :
    (bothCallState g state input bytes).mem.eraseFrom state.alloc.nextFreeBlock = state.mem := by
  rw [bothCallState, montgomeryCopyState_erase _ _ _ _ _ _ _ (slot_local state 7) (slot_local state 9),
    lowCallState_erase g state input bytes hwf]

theorem bothCallState_count (g : Globals) (state : GlobalState) (input : Pointer) (bytes : BitVec 512) :
    (bothCallState g state input bytes).alloc.nextFreeBlock = state.alloc.nextFreeBlock + 44 := by
  simp only [bothCallState, lowCallState, montgomeryCopyState_count, splitState,
    inputStates_count]

theorem invocation_calls_run (g : Globals) (E : Env program.Γ)
    (state : GlobalState) (out input : Pointer) (bytes : BitVec 512)
    (hwf : state.WF) (hr : Ready g state out) :
    (program.entry linkedPrimitives g).runBodyFrom (splitInputEnv E g state input bytes) 320
        (splitState state input bytes) =
      (program.entry linkedPrimitives g).runBodyFrom (splitInputEnv E g state input bytes) 330
        (bothCallState g state input bytes) := by
  let e := splitInputEnv E g state input bytes
  have hr0 := splitState_ready g state out input bytes hwf hr
  have hr1 := ready_of_erase g state (lowCallState g state input bytes) out hwf hr
    (lowCallState_erase g state input bytes hwf)
  have hp73 : e.read (%73) = .value (slot state 8) := by
    simp [e, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot,
      GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
  have hp75 : e.read (%75) = .value (slot state 10) := by
    simp [e, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot,
      GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
  have hp39 : e.read (%39) = .value (g.address0) := by
    simp [e, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot,
      GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
  have hp72 : e.read (%72) = .value (slot state 7) := by
    simp [e, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot,
      GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
  have hp74 : e.read (%74) = .value (slot state 9) := by
    simp [e, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot,
      GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
  have hp40 : e.read (%40) = .value (g.address1) := by
    simp [e, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot,
      GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
  have hp4 : e.read (%4) = .value (40#64) := by
    simp [e, splitInputEnv, splitEnv, inputEnvs, startupEnv, slot,
      GlobalState.alloca, GlobalState.allocaPtr, Nat.add_assoc,
      inputChunk0Env, inputChunk1Env, inputChunk2Env, inputChunk3Env, inputChunk4Env, inputChunk5Env, inputChunk6Env, inputChunk7Env, mlir_env]
  have hlow := low_call_copy_run g e (splitState state input bytes) (lowSplitWords bytes) rWords
    (slot state 8) (slot state 10) g.address0 hp73 hp75 hp39 hp4
    (splitState_wf state input bytes hwf)
    (splitState_range state input _ bytes 40 (startup_slot_range state ⟨8, by decide⟩))
    (splitState_range state input _ bytes 40 (startup_slot_range state ⟨10, by decide⟩))
    (ready_r_range g _ out hr0) (slot_ne state 10 8 (by decide))
    (splitState_low_read state input bytes) (ready_r_read g _ out hr0)
    (lowSplitWords_bound bytes) rWords_bound rWords_canonical
  have hhighread (i : Fin 5) :
      (lowCallState g state input bytes).mem.readAt
        ((slot state 9).add (BitVec.ofNat 64 (8 * i.val))) 64 = highSplitWords bytes i := by
    rw [lowCallState, montgomeryCopyState_read_other _ _ _ _ _ _ _ 64
      (by simpa only [Pointer.add_id] using slot_ne state 8 9 (by decide))
      (by simpa only [Pointer.add_id] using slot_ne state 10 9 (by decide))]
    exact splitState_high_read state input bytes i
  have hhigh := high_call_copy_run g e (lowCallState g state input bytes) (highSplitWords bytes) rrWords
    (slot state 7) (slot state 9) g.address1 hp72 hp74 hp40 hp4
    (lowCallState_wf g state input bytes hwf)
    (lowCallState_range g state input _ bytes 40 (startup_slot_range state ⟨7, by decide⟩))
    (lowCallState_range g state input _ bytes 40 (startup_slot_range state ⟨9, by decide⟩))
    (ready_rr_range g _ out hr1) (slot_ne state 9 7 (by decide))
    hhighread (ready_rr_read g _ out hr1)
    (highSplitWords_bound bytes) rrWords_bound rrWords_canonical
  exact hlow.trans hhigh

end Agave.Ed25519.Verifier.Execution.ScalarWide
