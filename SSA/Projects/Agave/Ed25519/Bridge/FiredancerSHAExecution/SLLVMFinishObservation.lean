import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMFinishExecution
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMAppendContext
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSourceInitObservation
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishPaddingMemory
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.FinishCompositionMemory

namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
open LeanMLIR SLLVM Firedancer
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Bridge.Challenge
namespace FinishObservation
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Only one allocation and the pointer offset are observed. This relation
never equates machine states or assumes a hash result. -/
structure Observed (m : MemoryState) (p : Pointer) (r : RIR.MemoryState) (q : RIR.Pointer) : Prop where
  block : m.live? p.id = (r[q.id]?).map ofRirBlock
  offset : p.offset = q.offset

theorem Observed.add {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (o : BitVec 64) : Observed m (p.withOffset o) r (q.add o) :=
  ⟨h.block, congrArg (· + o) h.offset⟩

theorem Observed.read {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (w : Nat) : sourceRead m p w = r.readAt q w := by
  unfold sourceRead RIR.MemoryState.readAt
  rw [h.block]
  cases hb : r[q.id]? <;> simp [ofRirBlock, Pointer.offsetInBits, RIR.Pointer.offsetInBits, h.offset]

theorem Observed.bytes {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (n : Nat) :
    sourceReadBytes m p n = Agave.Ed25519.Verifier.Execution.Challenge.readBytes r q n := by
  unfold sourceReadBytes Agave.Ed25519.Verifier.Execution.Challenge.readBytes
  congr 1
  funext i
  exact (h.add _).read 8

theorem Observed.state {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) : sourceReadState m p = readState r q := by
  unfold sourceReadState readState
  rw [(h.add 128#64).read, (h.add 136#64).read, (h.add 144#64).read,
    (h.add 152#64).read, (h.add 160#64).read, (h.add 168#64).read,
    (h.add 176#64).read, (h.add 184#64).read]

theorem Observed.splice {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (o : BitVec 64) (x : BitVec w) :
    Observed (m.splice (p.withOffset o) x) p (r.storeAt (q.add o) x) q := by
  constructor
  · change (m.splice (p.withOffset o) x).live? (p.withOffset o).id =
      ((r.storeAt (q.add o) x)[(q.add o).id]?).map ofRirBlock
    rw [live_splice_storeBlock, rir_storeAt_block]
    simp only [Pointer.withOffset, RIR.Pointer.add, h.block, h.offset]
  · exact h.offset

def snapshot (b : LiveBlock) : RIR.MemoryState :=
  ⟨(∅ : Std.ExtHashMap RIR.BlockId RIR.MemoryBlock).insert ⟨0⟩ ⟨b.length, b.bytes⟩⟩

def snapshotPtr (p : Pointer) : RIR.Pointer := ⟨⟨0⟩, p.offset⟩

theorem snapshot_get (b : LiveBlock) : (snapshot b)[(⟨0⟩ : RIR.BlockId)]? = some (⟨b.length, b.bytes⟩ : RIR.MemoryBlock) := by
  simp [snapshot, RIR.MemoryState.getElem?_eq]

theorem snapshot_observed {m : MemoryState} {p : Pointer} {b : LiveBlock}
    (h : m.live? p.id = some b) : Observed m p (snapshot b) (snapshotPtr p) := by
  constructor
  · simpa only [snapshotPtr, snapshot_get, Option.map_some, ofRirBlock] using h
  · rfl

theorem snapshot_small {m : MemoryState} {p : Pointer} {b : LiveBlock} {n : Nat}
    (h : Fits m p (8*n)) (hb : m.live? p.id = some b) (hsmall : b.length < 2^63) :
    SmallRange (snapshot b) (snapshotPtr p) n := by
  obtain ⟨b', hb', hlen⟩ := h
  have heq : b' = b := by simpa [MemoryState.live?, hb'] using hb
  subst b'
  refine ⟨⟨b.length, b.bytes⟩, snapshot_get b, hsmall, ?_⟩
  change p.offset.toNat + n ≤ b.length
  simp only [Pointer.offsetInBits, LiveBlock.lengthInBits] at hlen
  omega

theorem word_sourceRead (m : MemoryState) (p : Pointer) :
    FinishExecution.word m p = sourceRead m p 64 := by
  unfold FinishExecution.word readWord? sourceRead
  cases m.live? p.id <;> rfl

theorem Observed.marker {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (used : Nat) :
    Observed (FinishExecution.markerMemory m p used) p (Finish.markerMemory r q used) q :=
  h.splice _ _

theorem Observed.long {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (used : Nat) :
    Observed (FinishExecution.longMemory m p used) p (Finish.longMemory r q used) q :=
  h.splice _ _

theorem Observed.last {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (n : Nat) (lo hi : Word) :
    Observed (FinishExecution.lastMemory m p n lo hi) p (Finish.lastMemory r q n lo hi) q :=
  ((h.splice _ _).splice _ _).splice _ _

theorem first_padding_bytes {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (hr : SmallRange r q 128) (pending : Bytes)
    (hn : pending.length < 128) (hp : sourceReadBytes m p pending.length = pending) :
    sourceReadBytes (FinishExecution.longMemory (FinishExecution.markerMemory m p pending.length)
      p pending.length) p 128 = firstPaddingBlock pending := by
  rw [((h.marker pending.length).long pending.length).bytes]
  exact Finish.firstPaddingBlock_bytes r q pending hr hn ((h.bytes _).symm.trans hp)

theorem only_padding_bytes {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (hr : SmallRange r q 128) (pending : Bytes) (total : Nat)
    (lo hi : Word) (hn : pending.length < 112)
    (hp : sourceReadBytes m p pending.length = pending)
    (hcount : hi ++ lo = BitVec.ofNat 128 (8*total)) :
    sourceReadBytes (FinishExecution.lastMemory (FinishExecution.markerMemory m p pending.length)
      p (pending.length+1) lo hi) p 128 = onlyPaddingBlock pending total := by
  rw [((h.marker pending.length).last (pending.length+1) lo hi).bytes]
  exact Finish.onlyPaddingBlock_bytes r q pending total lo hi hr hn ((h.bytes _).symm.trans hp) hcount

theorem last_padding_bytes {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (hr : SmallRange r q 128) (total : Nat) (lo hi : Word)
    (hcount : hi ++ lo = BitVec.ofNat 128 (8*total)) :
    sourceReadBytes (FinishExecution.lastMemory m p 0 lo hi) p 128 = lastPaddingBlock total := by
  rw [(h.last 0 lo hi).bytes]
  exact Finish.lastPaddingBlock_bytes r q total lo hi hr hcount

theorem marker_state {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (hr : SmallRange r q 224) (used : Nat) (hn : used < 128) :
    sourceReadState (FinishExecution.markerMemory m p used) p = sourceReadState m p := by
  rw [(h.marker used).state, Finish.markerMemory_state r q used hr hn, ← h.state]

theorem long_state {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (hr : SmallRange r q 224) (used : Nat) (hn : used < 128) :
    sourceReadState (FinishExecution.longMemory m p used) p = sourceReadState m p := by
  rw [(h.long used).state, Finish.longMemory_state r q used hr hn, ← h.state]

theorem last_state {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    (h : Observed m p r q) (hr : SmallRange r q 224) (n : Nat) (lo hi : Word) (hn : n ≤ 112) :
    sourceReadState (FinishExecution.lastMemory m p n lo hi) p = sourceReadState m p := by
  rw [(h.last n lo hi).state, Finish.lastMemory_state r q n lo hi hr hn, ← h.state]

theorem Observed.context {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    {completed pending : Bytes} (h : Observed m p r q) (hr : SmallRange r q 224)
    (hp : SLLVMSource.ContextRepresents m p completed pending) :
    FiredancerSHAExecution.ContextRepresents r q completed pending := by
  refine ⟨hr, hp.completedWhole, hp.pendingBound, ?_, ?_, ?_, ?_⟩
  · exact (h.bytes _).symm.trans hp.pendingBytes
  · exact ((h.add 200#64).read 64).symm.trans hp.pendingCount
  · exact h.state.symm.trans hp.chaining
  · rw [← (h.add 216#64).read 64, ← (h.add 208#64).read 64]
    exact hp.bitCount

theorem Observed.context_back {m : MemoryState} {p : Pointer} {r : RIR.MemoryState} {q : RIR.Pointer}
    {completed pending : Bytes} (h : Observed m p r q) (hr : Fits m p (224*8))
    (hn : p.offset.toNat + 224 < 2^63)
    (hp : FiredancerSHAExecution.ContextRepresents r q completed pending) :
    SLLVMSource.ContextRepresents m p completed pending := by
  refine ⟨hr, hn, hp.completedWhole, hp.pendingBound, ?_, ?_, ?_, ?_⟩
  · exact (h.bytes _).trans hp.pendingBytes
  · exact ((h.add 200#64).read 64).trans hp.pendingCount
  · exact h.state.trans hp.chaining
  · rw [(h.add 216#64).read 64, (h.add 208#64).read 64]
    exact hp.bitCount

end FinishObservation
end Agave.Ed25519.Bridge.FiredancerSHAExecution.SLLVMSource
