import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishPaddingMemory
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishOutputMemory
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.CoreCall

/-! Context and caller-frame facts for composing the actual finalizer. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Installed compression constants; only the exact 80 native words matter. -/
structure ConstantsReady (m : MemoryState) (kp : Pointer) : Prop where
  live : SmallRange m kp 640
  words : ∀ j, j < 80 → m.readAt (kp.add (BitVec.ofNat 64 (8 * j))) 64 =
    constants.toList.getD j 0

theorem ConstantsReady.storeAt {m : MemoryState} {kp p : Pointer} {w : Nat}
    (h : ConstantsReady m kp) (x : BitVec w) (hne : p.id ≠ kp.id) :
    ConstantsReady (m.storeAt p x) kp := by
  refine ⟨h.live.storeAt _ _, ?_⟩
  intro j hj
  rw [MemoryState.readAt_storeAt_disjoint (q := kp.add (BitVec.ofNat 64 (8 * j))) (Or.inl hne)]
  exact h.words j hj

theorem chainMemory_readState (m : MemoryState) (p : Pointer) :
    Core.ChainMemory m (p.add 128#64) (readState m p) := by
  constructor <;> simp [readState, Pointer.add_add]

theorem readState_of_chainMemory (m : MemoryState) (p : Pointer) (s : State)
    (h : Core.ChainMemory m (p.add 128#64) s) : readState m p = s := by
  cases s
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩
  simp only [Pointer.add_add, BitVec.reduceAdd] at h0 h1 h2 h3 h4 h5 h6 h7
  simp only [readState, h0,h1,h2,h3,h4,h5,h6,h7]

/-- Buffer writes up to byte 127 preserve all eight chaining words. -/
theorem readState_store_buffer (m : MemoryState) (p : Pointer) (i count : Nat)
    (x : BitVec (8 * count)) (hr : SmallRange m p 224) (hi : i + count ≤ 128) :
    readState (m.storeAt (p.add (BitVec.ofNat 64 i)) x) p = readState m p := by
  have hd (j : Nat) (hj : 128 ≤ j ∧ j + 8 ≤ 224) :
      (Range.of (p.add (BitVec.ofNat 64 i)) (8 * count)).Disjoint
        (Range.of (p.add (BitVec.ofNat 64 j)) 64) := by
    simpa [Nat.mul_comm] using smallRange_disjoint_offsets hr
      (i := i) (countI := count) (j := j) (countJ := 8)
      (by omega) (by omega) (Or.inl (by omega))
  simp only [readState]
  rw [MemoryState.readAt_storeAt_disjoint (hd 128 (by omega)),
    MemoryState.readAt_storeAt_disjoint (hd 136 (by omega)),
    MemoryState.readAt_storeAt_disjoint (hd 144 (by omega)),
    MemoryState.readAt_storeAt_disjoint (hd 152 (by omega)),
    MemoryState.readAt_storeAt_disjoint (hd 160 (by omega)),
    MemoryState.readAt_storeAt_disjoint (hd 168 (by omega)),
    MemoryState.readAt_storeAt_disjoint (hd 176 (by omega)),
    MemoryState.readAt_storeAt_disjoint (hd 184 (by omega))]

theorem markerMemory_state (m : MemoryState) (p : Pointer) (used : Nat)
    (hr : SmallRange m p 224) (hu : used < 128) :
    readState (markerMemory m p used) p = readState m p :=
  readState_store_buffer m p used 1 128#8 hr (by omega)

theorem longMemory_state (m : MemoryState) (p : Pointer) (used : Nat)
    (hr : SmallRange m p 224) (hu : used < 128) :
    readState (longMemory m p used) p = readState m p :=
  readState_store_buffer m p (used + 1) (127 - used) _ hr (by omega)

theorem lastMemory_state (m : MemoryState) (p : Pointer) (n : Nat) (lo hi : Word)
    (hr : SmallRange m p 224) (hn : n ≤ 112) :
    readState (lastMemory m p n lo hi) p = readState m p := by
  unfold lastMemory
  rw [readState_store_buffer _ p 120 8 _ ((hr.storeAt _ _).storeAt _ _) (by decide),
    readState_store_buffer _ p 112 8 _ (hr.storeAt _ _) (by decide),
    readState_store_buffer _ p n (112 - n) _ hr (by omega)]

theorem coreCallState_state (state : GlobalState) (context : Pointer) (initial : State)
    (hr : SmallRange state.mem context 224) :
    readState (Core.coreCallState state (context.add 128#64) context initial).mem context =
      compressBlock initial (readBytes state.mem context 128) := by
  have hc : SmallRange state.mem (context.add 128#64) 64 := smallRange_add hr (by decide)
  exact readState_of_chainMemory _ context _
    (Core.chainMemory_of_packed _ _ (hc.storeAt _ _) _
      (Core.coreCallState_read state _ _ initial hc))

theorem core_call_context (kp context : Pointer) (state : GlobalState)
    (hwf : state.WF) (hr : SmallRange state.mem context 224)
    (hk : ConstantsReady state.mem kp) :
    (Core.program kp).call
      (Core.program.args (.value (context.add 128#64)) (.value context) (.value 1#64)) state =
      .value (.nil, Core.coreCallState state (context.add 128#64) context
        (readState state.mem context)) :=
  Core.core_call_one kp _ _ state _ hwf (smallRange_add hr (by decide))
    (smallRange_mono hr (by decide)) hk.live (chainMemory_readState _ _) hk.words

theorem outputMemory_state (m : MemoryState) (context output : Pointer) (s : State)
    (ho : SmallRange m output 64) (hne : output.id ≠ context.id) :
    readState (outputMemory m output s) context = readState m context := by
  rw [outputMemory_eq m output ho s]
  have hd (k : Word) : (Range.of output 512).Disjoint (Range.of (context.add k) 64) := Or.inl hne
  simp only [readState, MemoryState.readAt_storeAt_disjoint (hd _)]

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Finish
