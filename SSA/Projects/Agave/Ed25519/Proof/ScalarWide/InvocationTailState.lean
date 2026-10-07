import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationWords
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ResultSlots
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InputCleanup
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.ByteStores
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FinalCleanup

/-! Exact post-call states and register environments, through the final return. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

/-- The five source result slots 84–88. -/
def resultSlots (state : GlobalState) (i : Fin 5) : Pointer := slot state (19 + i.val)
def inputSlots (state : GlobalState) (i : Fin 8) : Pointer := slot state (11 + i.val)
def zeroSlots (state : GlobalState) (i : Fin 5) : Pointer := slot state i.val

def sumPhaseEnv (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) : Env program.Γ :=
  sumEnv (splitInputEnv E g state input bytes) (lowWords g state bytes) (highWords g state bytes)

def subtractPhaseEnv (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) : Env program.Γ :=
  wrapperSubtractEnv (sumPhaseEnv E g state input bytes)
    (sum52 (lowWords g state bytes) (highWords g state bytes))

def resultState (g : Globals) (state : GlobalState) (input : Pointer) (bytes : BitVec 512) : GlobalState :=
  { alloc := ((bothCallState g state input bytes).alloca 1).alloc,
    mem := resultSlotMemory (bothCallState g state input bytes).mem
      (resultSlots state) (finalWords g state bytes) }

def inputCleanState (g : Globals) (state : GlobalState) (input : Pointer) (bytes : BitVec 512) : GlobalState :=
  {resultState g state input bytes with
    mem := inputCleanupMemory (resultState g state input bytes).mem (inputSlots state)
      (slot state 6) (slot state 5) (slot state 10) (slot state 9)}

def serializePhaseEnv (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (input : Pointer) (bytes : BitVec 512) : Env program.Γ :=
  serializeEnv (subtractPhaseEnv E g state input bytes) (finalWords g state bytes)

def byteState (g : Globals) (state : GlobalState) (out input : Pointer) (bytes : BitVec 512) : GlobalState :=
  {inputCleanState g state input bytes with
    mem := Agave.Ed25519.ScalarReduce32.Execution.storeBytes (inputCleanState g state input bytes).mem
      out (serializedBytes (finalWords g state bytes))}

def returnState (g : Globals) (state : GlobalState) (out input : Pointer) (bytes : BitVec 512) : GlobalState :=
  {byteState g state out input bytes with
    mem := finalCleanupMemory
      (byteState g state out input bytes).mem (zeroSlots state) (resultSlots state)}

def returnEnv (E : Env program.Γ) (g : Globals) (state : GlobalState)
    (out input : Pointer) (bytes : BitVec 512) : Env program.Γ :=
  finalCleanupEnv (byteStoresEnv (serializePhaseEnv E g state input bytes) out)
    (byteState g state out input bytes).mem (zeroSlots state) (resultSlots state)

theorem bothCallState_low_read (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (i : Fin 5) :
    (bothCallState g state input bytes).mem.readAt
      ((slot state 10).add (BitVec.ofNat 64 (8 * i.val))) 64 = lowWords g state bytes i := by
  rw [bothCallState, montgomeryCopyState_read_other _ _ _ _ _ _ _ 64
    (by simpa only [Pointer.add_id] using slot_ne state 7 10 (by decide))
    (by simpa only [Pointer.add_id] using slot_ne state 9 10 (by decide))]
  exact montgomeryCopyState_read _ _ _ _ _ _
    (splitState_range state input _ bytes 40 (startup_slot_range state ⟨8, by decide⟩))
    (splitState_range state input _ bytes 40 (startup_slot_range state ⟨10, by decide⟩)) i

theorem bothCallState_high_read (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (i : Fin 5) :
    (bothCallState g state input bytes).mem.readAt
      ((slot state 9).add (BitVec.ofNat 64 (8 * i.val))) 64 = highWords g state bytes i := by
  exact montgomeryCopyState_read _ _ _ _ _ _
    (lowCallState_range g state input _ bytes 40 (startup_slot_range state ⟨7, by decide⟩))
    (lowCallState_range g state input _ bytes 40 (startup_slot_range state ⟨9, by decide⟩)) i

theorem resultState_range (g : Globals) (state : GlobalState) (input q : Pointer)
    (bytes : BitVec 512) (count : Nat) (h : SmallRange (startupState state).mem q count) :
    SmallRange (resultState g state input bytes).mem q count := by
  change SmallRange (resultSlotMemory _ _ _) _ _
  unfold resultSlotMemory
  repeat apply SmallRange.storeAt
  exact h

theorem inputCleanState_range (g : Globals) (state : GlobalState) (input q : Pointer)
    (bytes : BitVec 512) (count : Nat) (h : SmallRange (startupState state).mem q count) :
    SmallRange (inputCleanState g state input bytes).mem q count := by
  change SmallRange (inputCleanupMemory _ _ _ _ _ _) _ _
  unfold inputCleanupMemory
  repeat apply SmallRange.storeAt
  exact h

theorem byteState_range (g : Globals) (state : GlobalState) (out input q : Pointer)
    (bytes : BitVec 512) (count : Nat) (h : SmallRange (startupState state).mem q count) :
    SmallRange (byteState g state out input bytes).mem q count := by
  change SmallRange (Agave.Ed25519.ScalarReduce32.Execution.storeBytes _ _ _) _ _
  unfold Agave.Ed25519.ScalarReduce32.Execution.storeBytes
  repeat apply SmallRange.storeAt
  exact h

end Agave.Ed25519.Verifier.Execution.ScalarWide
