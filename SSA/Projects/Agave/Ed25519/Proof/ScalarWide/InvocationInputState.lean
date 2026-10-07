import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputRegisterBridge
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperStartupMemory
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.Frame

/-! Exact states through all input assembly chunks, with scratch provenance
fixed by the invocation allocation prefix. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

def inputStates (state : GlobalState) (input : Pointer) : Fin 8 → GlobalState :=
  let s0 := startupState state
  let s1 := {s0 with mem := s0.mem.storeAt (slot state 12) (inputChunk1Word (startupState state).mem input)}
  let s2 := {s1 with mem := s1.mem.storeAt (slot state 13) (inputChunk2Word (startupState state).mem input)}
  let s3 := {s2 with mem := s2.mem.storeAt (slot state 14) (inputChunk3Word (startupState state).mem input)}
  let s4 := {s3 with mem := s3.mem.storeAt (slot state 15) (inputChunk4Word (startupState state).mem input)}
  let s5 := {s4 with mem := s4.mem.storeAt (slot state 16) (inputChunk5Word (startupState state).mem input)}
  let s6 := {s5 with mem := s5.mem.storeAt (slot state 17) (inputChunk6Word (startupState state).mem input)}
  let s7 := {s6 with mem := s6.mem.storeAt (slot state 18) (inputChunk7Word (startupState state).mem input)}
  ![s0, s1, s2, s3, s4, s5, s6, s7]

def inputEnvs (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (input : Pointer) : Fin 8 → Env program.Γ :=
  let e0 := inputChunk0Env (startupEnv E g state) (startupState state).mem input
  let e1 := inputChunk1Env e0 (startupState state).mem input
  let e2 := inputChunk2Env e1 (startupState state).mem input
  let e3 := inputChunk3Env e2 (startupState state).mem input
  let e4 := inputChunk4Env e3 (startupState state).mem input
  let e5 := inputChunk5Env e4 (startupState state).mem input
  let e6 := inputChunk6Env e5 (startupState state).mem input
  let e7 := inputChunk7Env e6 (startupState state).mem input
  ![e0, e1, e2, e3, e4, e5, e6, e7]

theorem inputStates_range (state : GlobalState) (input q : Pointer) (bytes : Nat)
    (h : SmallRange (startupState state).mem q bytes) (i : Fin 8) :
    SmallRange (inputStates state input i).mem q bytes := by
  fin_cases i <;> simp only [inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one]
  all_goals repeat apply SmallRange.storeAt
  all_goals exact h

theorem inputStates_fits (state : GlobalState) (input q : Pointer) (width : Nat)
    (h : Fits (startupState state).mem q width) (i : Fin 8) :
    Fits (inputStates state input i).mem q width := by
  fin_cases i <;> simp only [inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one]
  all_goals repeat apply Fits.storeAt
  all_goals exact h

theorem inputStates_wf (state : GlobalState) (input : Pointer) (hwf : state.WF) (i : Fin 8) :
    (inputStates state input i).WF := by
  have hs : (startupState state).WF := by
    rw [startupState_eq_wrapperAllocSteps]
    exact wrapperAllocSteps_wf state hwf 24
  fin_cases i <;> simp only [inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one]
  all_goals repeat apply GlobalState.WF.storeAt_mk
  all_goals exact hs

theorem inputStates_count (state : GlobalState) (input : Pointer) (i : Fin 8) :
    (inputStates state input i).alloc.nextFreeBlock = state.alloc.nextFreeBlock + 24 := by
  fin_cases i <;> simp only [inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one, startup_allocation_count]

theorem inputStates_read_caller (state : GlobalState) (input q : Pointer) (width : Nat)
    (hwf : state.WF) (h : Fits state.mem q width) (i : Fin 8) :
    (inputStates state input i).mem.readAt q width = (startupState state).mem.readAt q width := by
  have hn1 := slot_ne_caller state hwf q width h 12
  have hn2 := slot_ne_caller state hwf q width h 13
  have hn3 := slot_ne_caller state hwf q width h 14
  have hn4 := slot_ne_caller state hwf q width h 15
  have hn5 := slot_ne_caller state hwf q width h 16
  have hn6 := slot_ne_caller state hwf q width h 17
  have hn7 := slot_ne_caller state hwf q width h 18
  fin_cases i <;> simp only [inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one]
  all_goals simp only [
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn1),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn2),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn3),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn4),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn5),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn6),
    MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hn7)]

theorem inputStates_erase (state : GlobalState) (input : Pointer) (hwf : state.WF) (i : Fin 8) :
    (inputStates state input i).mem.eraseFrom state.alloc.nextFreeBlock = state.mem := by
  fin_cases i <;> simp only [inputStates, Matrix.cons_val_zero, Matrix.cons_val_zero',
    Matrix.cons_val_succ, Matrix.cons_val_succ',
    Matrix.cons_val_fin_one]
  all_goals try simp only [MemoryState.eraseFrom_storeAt,
    MemoryState.storeAt_eraseFrom_of_le (slot_local state _)]
  all_goals exact startupState_erase state hwf

end Agave.Ed25519.Verifier.Execution.ScalarWide
