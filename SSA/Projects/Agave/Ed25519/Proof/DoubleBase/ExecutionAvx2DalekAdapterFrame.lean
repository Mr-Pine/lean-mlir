import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Backend
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekIdentityMemory

/-! Caller memory is tracked at local arithmetic boundaries. The final
function-frame erasure turns this invariant into the ordinary Dalek frame. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR RIR PointArithmetic
open Reduce64.Execution (SmallRange)
open Verifier.Execution
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

structure CallerFrame (before after : GlobalState) (out : Pointer) : Prop where
  wellFormed : after.WF
  live : ∀ q bytes, SmallRange before.mem q bytes → SmallRange after.mem q bytes
  read : ∀ q width, q.id.id < before.alloc.nextFreeBlock →
    (Range.of q width).Disjoint (Range.of out 1280) →
    after.mem.readAt q width = before.mem.readAt q width

theorem CallerFrame.refl (hwf : s.WF) : CallerFrame s s out :=
  ⟨hwf, fun _ _ h => h, fun _ _ _ _ => rfl⟩

/-- Stores into this call's private stack do not touch any caller byte. -/
theorem CallerFrame.storePrivate (h : CallerFrame before after out)
    (hd : before.alloc.nextFreeBlock ≤ dst.id.id) (x : BitVec width) :
    CallerFrame before {after with mem := after.mem.storeAt dst x} out := by
  refine ⟨h.wellFormed.storeAt, fun q bytes hq => (h.live q bytes hq).storeAt _ _, ?_⟩
  intro q bits hq hdis
  have hne : dst.id ≠ q.id := by
    intro he
    have hid := congrArg (fun id => id.id) he
    omega
  exact (MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hne) x).trans
    (h.read q bits hq hdis)

theorem CallerFrame.storeOutputsPrivate (h : CallerFrame before after out)
    (hd : before.alloc.nextFreeBlock ≤ dst.id.id) (z : Reduce64.Execution.Columns4) :
    CallerFrame before {after with mem := Reduce64.Execution.storeOutputs after.mem dst z} out := by
  simpa only [Reduce64.Execution.storeOutputs] using
    ((((h.storePrivate hd (BitVec.packLanes (Reduce64.Execution.packedOutput z 0))).storePrivate
      (by simpa using hd) (BitVec.packLanes (Reduce64.Execution.packedOutput z 1))).storePrivate
      (by simpa using hd) (BitVec.packLanes (Reduce64.Execution.packedOutput z 2))).storePrivate
      (by simpa using hd) (BitVec.packLanes (Reduce64.Execution.packedOutput z 3))).storePrivate
      (by simpa using hd) (BitVec.packLanes (Reduce64.Execution.packedOutput z 4))

theorem stack_separate_old {q : Pointer} {s : GlobalState} (hq : q.id.id < s.alloc.nextFreeBlock) (n : Nat) :
    (avx2StackPtr s n).id ≠ q.id := by
  intro he
  have hid := congrArg (fun x => x.id) he
  simp only [avx2StackPtr, GlobalState.allocaPtr_id_id, avx2Stack_nextFreeBlock] at hid
  omega

theorem stack_read_old (hq : q.id.id < s.alloc.nextFreeBlock) (n width : Nat) :
    (avx2Stack s n).mem.readAt q width = s.mem.readAt q width := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ((avx2Stack s n).alloca _).mem.readAt q width = _
    rw [show ((avx2Stack s n).alloca _).mem.readAt q width =
      (avx2Stack s n).mem.readAt q width by
        simp only [MemoryState.readAt, GlobalState.getElem?_alloca
          (stack_separate_old hq n).symm]]
    exact ih

theorem prefix_read_old (s : GlobalState) (a b : BitVec 256)
    (hq : q.id.id < s.alloc.nextFreeBlock) (width : Nat) :
    (prefixState s a b).mem.readAt q width = s.mem.readAt q width := by
  unfold prefixState
  rw [nafPhase_read_other 8 _ _ _ q b width
    (stack_separate_old hq 28) (stack_separate_old hq 20),
    nafPhase_read_other 5 _ _ _ q a width
    (stack_separate_old hq 29) (stack_separate_old hq 21), stack_read_old hq]

theorem prefix_callerFrame (s : GlobalState) (a b : BitVec 256) (hwf : s.WF)
    (hf : TableFrame (prefixState s a b) after (avx2StackPtr s 27)) :
    CallerFrame s after out := by
  refine ⟨hf.wellFormed, fun q bytes hq => hf.live q bytes
    (prefixState_buffer s a b hwf hq), ?_⟩
  intro q width hq _
  rw [hf.read q width (Range.disjoint_of_id_ne (stack_separate_old hq 27).symm)]
  exact prefix_read_old s a b hq width

theorem unpackStore_frame (s : GlobalState) (out : Pointer) (v : UnpackBlocks)
    (hwf : s.WF) (h : SmallRange s.mem out 160) :
    Dalek.OutputFrame s {s with mem := unpackStore s.mem out v} out 160 := by
  constructor
  · simpa only [unpackStore, GlobalState.WF_storeAt] using hwf
  · intro q bytes hq
    unfold unpackStore
    repeat' apply SmallRange.storeAt
    exact hq
  · intro q width hd
    have h0 := Dalek.disjoint_add_subrange h hd (k := 0) (count := 16) (by decide)
    have h16 := Dalek.disjoint_add_subrange h hd (k := 16) (count := 16) (by decide)
    have h32 := Dalek.disjoint_add_subrange h hd (k := 32) (count := 32) (by decide)
    have h64 := Dalek.disjoint_add_subrange h hd (k := 64) (count := 8) (by decide)
    have h72 := Dalek.disjoint_add_subrange h hd (k := 72) (count := 32) (by decide)
    have h104 := Dalek.disjoint_add_subrange h hd (k := 104) (count := 32) (by decide)
    have h136 := Dalek.disjoint_add_subrange h hd (k := 136) (count := 16) (by decide)
    have h152 := Dalek.disjoint_add_subrange h hd (k := 152) (count := 8) (by decide)
    simp only [Pointer.add_zero] at h0
    unfold unpackStore
    dsimp only
    refine (MemoryState.readAt_storeAt_disjoint ?_ _).trans ?_
    · exact h152.symm
    refine (MemoryState.readAt_storeAt_disjoint ?_ _).trans ?_
    · exact h136.symm
    refine (MemoryState.readAt_storeAt_disjoint ?_ _).trans ?_
    · exact h104.symm
    refine (MemoryState.readAt_storeAt_disjoint ?_ _).trans ?_
    · exact h72.symm
    refine (MemoryState.readAt_storeAt_disjoint ?_ _).trans ?_
    · exact h64.symm
    refine (MemoryState.readAt_storeAt_disjoint ?_ _).trans ?_
    · exact h32.symm
    refine (MemoryState.readAt_storeAt_disjoint ?_ _).trans ?_
    · exact h16.symm
    refine (MemoryState.readAt_storeAt_disjoint ?_ _).trans ?_
    · exact h0.symm
    rfl

theorem CallerFrame.thenOutput (h : CallerFrame before middle out)
    (ho : Dalek.OutputFrame middle after out 160) : CallerFrame before after out := by
  refine ⟨ho.wellFormed, fun q bytes hq => ho.live q bytes (h.live q bytes hq), ?_⟩
  intro q width hq hd
  exact (ho.read q width hd).trans (h.read q width hq hd)

theorem readAt_eraseFrom_new (m : MemoryState) (q : Pointer) (width : Nat)
    (hq : cutoff ≤ q.id.id) : (m.eraseFrom cutoff).readAt q width = 0 := by
  simp [MemoryState.readAt, MemoryState.eraseFrom, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem?_filter', show ¬q.id.id < cutoff by omega]

theorem eraseFrom_wf (s : GlobalState) (hwf : s.WF) (cutoff : Nat) :
    ({s with mem := s.mem.eraseFrom cutoff} : GlobalState).WF := by
  intro k hk
  simp only [MemoryState.eraseFrom, Std.ExtHashMap.mem_filter] at hk
  exact hwf k hk.1

theorem CallerFrame.erase (hwf : before.WF) (h : CallerFrame before after out) :
    Dalek.OutputFrame before {after with mem := after.mem.eraseFrom before.alloc.nextFreeBlock}
      out 160 := by
  refine ⟨eraseFrom_wf after h.wellFormed _, ?_, ?_⟩
  · intro q bytes hq
    exact smallRange_eraseFrom (h.live q bytes hq) (hwf.lt hq.fits.mem)
  · intro q width hd
    by_cases hq : q.id.id < before.alloc.nextFreeBlock
    · rw [readAt_eraseFrom after.mem q width hq]
      exact h.read q width hq hd
    · rw [readAt_eraseFrom_new after.mem q width (by omega)]
      rw [← hwf.eraseFrom]
      exact (readAt_eraseFrom_new before.mem q width (by omega)).symm

end Agave.Ed25519.DoubleBase.ExecutionAvx2
