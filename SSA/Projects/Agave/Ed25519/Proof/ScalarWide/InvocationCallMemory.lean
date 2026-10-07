import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.InvocationSplit
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.WrapperCalls

/-! Live ranges, exact limb reads, and allocation validity at the two calls. -/
namespace Agave.Ed25519.Verifier.Execution.ScalarWide
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution (SmallRange)

 theorem splitState_range (state : GlobalState) (input q : Pointer) (bytes : BitVec 512)
    (count : Nat) (h : SmallRange (startupState state).mem q count) :
    SmallRange (splitState state input bytes).mem q count := by
  exact ScalarMontgomeryMul.outputStores_smallRange _ _ _ _ _
    (ScalarMontgomeryMul.outputStores_smallRange _ _ _ _ _
      (inputStates_range state input q count h 7))

theorem splitState_wf (state : GlobalState) (input : Pointer) (bytes : BitVec 512)
    (hwf : state.WF) : (splitState state input bytes).WF := by
  simpa only [splitState, splitStores, ScalarMontgomeryMul.outputStores, GlobalState.WF_storeAt]
    using inputStates_wf state input hwf 7

theorem splitState_low_read (state : GlobalState) (input : Pointer) (bytes : BitVec 512)
    (i : Fin 5) :
    (splitState state input bytes).mem.readAt
      ((slot state 10).add (BitVec.ofNat 64 (8 * i.val))) 64 = lowSplitWords bytes i := by
  have hl := inputStates_range state input (slot state 10) 40
    (startup_slot_range state ⟨10, by decide⟩) 7
  change (ScalarMontgomeryMul.outputStores
    (ScalarMontgomeryMul.outputStores _ (slot state 10) (lowSplitWords bytes))
    (slot state 9) (highSplitWords bytes)).readAt _ _ = _
  rw [ScalarMontgomeryMul.outputStores_read_other _ _ _ _ 64
    (by simpa only [Pointer.add_id] using slot_ne state 9 10 (by decide))]
  exact ScalarMontgomeryMul.outputStores_read _ _ _ hl i

theorem splitState_high_read (state : GlobalState) (input : Pointer) (bytes : BitVec 512)
    (i : Fin 5) :
    (splitState state input bytes).mem.readAt
      ((slot state 9).add (BitVec.ofNat 64 (8 * i.val))) 64 = highSplitWords bytes i := by
  have hh := inputStates_range state input (slot state 9) 40
    (startup_slot_range state ⟨9, by decide⟩) 7
  exact ScalarMontgomeryMul.outputStores_read _ _ _
    (ScalarMontgomeryMul.outputStores_smallRange _ _ _ _ _ hh) i

theorem montgomeryCopyState_wf (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (tmp operand constant : Pointer) (hwf : state.WF) :
    (montgomeryCopyState state a b tmp operand constant).WF := by
  dsimp only [montgomeryCopyState, copy40State, ScalarMontgomeryMul.callPostState,
    ScalarMontgomeryMul.outputStores]
  repeat apply GlobalState.WF.storeAt_mk
  exact hwf.add_blocks (k := 10)

theorem montgomeryCopyState_read_other (state : GlobalState) (a b : Fin 5 → BitVec 64)
    (tmp operand constant q : Pointer) (width : Nat)
    (htmp : tmp.id ≠ q.id) (hop : operand.id ≠ q.id) :
    (montgomeryCopyState state a b tmp operand constant).mem.readAt q width =
      state.mem.readAt q width := by
  change (MemoryState.storeAt _ operand _).readAt q width = _
  rw [MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hop)]
  exact ScalarMontgomeryMul.outputStores_read_other _ _ _ _ width htmp

/-- Exact initialized globals survive either call/copy because its buffers
belong to this invocation, above the original caller frame boundary. -/
theorem montgomeryCopyState_ready (g : Globals) (initial state : GlobalState)
    (out : Pointer) (a b : Fin 5 → BitVec 64) (tmp operand constant : Pointer)
    (hwf : initial.WF) (hr : Ready g initial out)
    (hframe : state.mem.eraseFrom initial.alloc.nextFreeBlock = initial.mem)
    (htmp : initial.alloc.nextFreeBlock ≤ tmp.id.id)
    (hop : initial.alloc.nextFreeBlock ≤ operand.id.id) :
    Ready g (montgomeryCopyState state a b tmp operand constant) out := by
  apply ready_of_erase g initial _ out hwf hr
  rw [montgomeryCopyState_erase state a b tmp operand constant _ htmp hop, hframe]

end Agave.Ed25519.Verifier.Execution.ScalarWide
