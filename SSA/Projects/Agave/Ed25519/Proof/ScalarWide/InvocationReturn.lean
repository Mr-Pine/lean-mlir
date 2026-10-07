import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationFinalCleanup

/-! Exact whole-memory and allocation-counter result after outer frame erasure. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)
set_option maxRecDepth 100000

theorem resultState_erase (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) :
    (resultState g state input bytes).mem.eraseFrom state.alloc.nextFreeBlock = state.mem := by
  dsimp only [resultState, resultSlots]
  rw [resultSlots_erase _ (resultSlots state) _ _ (fun i => slot_local state (19 + i.val)),
    bothCallState_erase g state input bytes hwf]

theorem inputCleanState_erase (g : Globals) (state : GlobalState) (input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) :
    (inputCleanState g state input bytes).mem.eraseFrom state.alloc.nextFreeBlock = state.mem := by
  dsimp only [inputCleanState, inputSlots]
  rw [inputCleanup_erase _ (inputSlots state) _ _ _ _ _
    (fun i => slot_local state (11 + i.val))
    (slot_local state 6) (slot_local state 5) (slot_local state 10) (slot_local state 9),
    resultState_erase g state input bytes hwf]

theorem returnState_count (g : Globals) (state : GlobalState) (out input : Pointer)
    (bytes : BitVec 512) :
    (returnState g state out input bytes).alloc.nextFreeBlock = state.alloc.nextFreeBlock + 45 := by
  simp only [returnState, byteState, inputCleanState, resultState, GlobalState.alloca,
    bothCallState_count]

theorem returnState_memory (g : Globals) (state : GlobalState) (out input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) (hout : SmallRange state.mem out 32) :
    (returnState g state out input bytes).mem.eraseFrom state.alloc.nextFreeBlock =
      state.mem.storeAt out (Agave.Ed25519.Bridge.Challenge.reducedBytes bytes) := by
  dsimp only [returnState, zeroSlots, resultSlots]
  rw [finalCleanup_erase _ (zeroSlots state) (resultSlots state) _
    (fun i => slot_local state i.val) (fun i => slot_local state (19 + i.val))]
  have hbytes : serializedBytes (finalWords g state bytes) =
      fun i => (Agave.Ed25519.Bridge.Challenge.reducedBytes bytes).extractLsb' (8 * i.val) 8 :=
    funext (finalSerializedBytes_eq g state bytes)
  change (Agave.Ed25519.ScalarReduce32.Execution.storeBytes _ _ _).eraseFrom _ = _
  rw [hbytes]
  exact serialized_frame _ state.mem out _ state.alloc.nextFreeBlock
    (inputCleanState_erase g state input bytes hwf) hout

theorem returnState_post (g : Globals) (state : GlobalState) (out input : Pointer)
    (bytes : BitVec 512) (hwf : state.WF) (hout : SmallRange state.mem out 32) :
    {returnState g state out input bytes with
      mem := (returnState g state out input bytes).mem.eraseFrom state.alloc.nextFreeBlock} =
      exactPostState state out bytes := by
  apply GlobalState.ext
  · cases ha : (returnState g state out input bytes).alloc with
    | mk counter =>
      have h := returnState_count g state out input bytes
      rw [ha] at h
      exact congrArg AllocState.mk h
  · exact returnState_memory g state out input bytes hwf hout

end Agave.Ed25519.Verifier.Execution.ScalarWide
