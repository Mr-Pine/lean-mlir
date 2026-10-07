import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.AppendEntry
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerSHAExecution.InitializerData
import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionFold

/-! A deterministic memory-level append specification. Compression is the
common mathematical SHA-512 fold. The contextual core contract names only one
positive-count core invocation and the exact installed constant initializer. -/
namespace Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
open LeanMLIR.RIR Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512 Agave.Ed25519.SHA512.Spec
open Agave.Ed25519.Verifier.Execution.Challenge
set_option maxRecDepth 100000
set_option maxHeartbeats 600000

/-- Caller-visible result of one core call; the private ring consumes one fresh
allocation id and is erased before returning. -/
def compressionState (s : GlobalState) (chain data : Pointer) (count : Nat) : GlobalState :=
  {alloc := ⟨s.alloc.nextFreeBlock + 1⟩,
   mem := s.mem.storeAt chain (Spec.run (s.mem.readAt chain 512) (readBytes s.mem data (128 * count)))}

def CoreCallContract (core : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (id : BlockId) : Prop :=
  ∀ (s : GlobalState) (chain data : Pointer) (count : Word),
    s.WF → SmallRange s.mem chain 64 → SmallRange s.mem data (128 * count.toNat) →
    constantsGlobal.Present id s.mem → 0 < count.toNat → chain.id ≠ id →
    (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))) →
    core (.cons (.value chain) (.cons (.value data) (.cons (.value count) .nil))) s =
      .value (.nil, compressionState s chain data count.toNat)

def directState (s : GlobalState) (context data : Pointer) (size : Word) : GlobalState :=
  tailState (if size.toNat < 128 then s else
    compressionState s (context.add 128#64) data (size >>> 7).toNat) context data size

def fillState (s : GlobalState) (context data : Pointer) (used : Word) : GlobalState :=
  {s with mem := copyMemory s.mem (context.add used) data (128#64 - used)}

def resultState (s : GlobalState) (context data : Pointer) (size : Word) : GlobalState :=
  if size = 0#64 then s else
  let t := startState s context size
  let used := s.mem.readAt (context.add 200#64) 64
  if used = 0#64 then directState t context data size else
  if size.toNat < (128#64 - used).toNat then shortState t context data used size else
  let t := compressionState (fillState t context data used) (context.add 128#64) context 1
  directState (resetState t context) context (data.add (128#64 - used)) (size - (128#64 - used))

/-- A finite sequence of ordinary stores into one pre-existing allocation.
This is a memory frame relation, not an execution assumption. -/
inductive BlockWrites (id : BlockId) : MemoryState → MemoryState → Prop
  | refl (m) : BlockWrites id m m
  | store {m n : MemoryState} (h : BlockWrites id m n) (p : Pointer) (value : BitVec w)
      (hp : p.id = id) : BlockWrites id m (n.storeAt p value)

namespace BlockWrites
variable {id : BlockId} {m n k : MemoryState} {p : Pointer} {bytes : Nat}
theorem trans (h : BlockWrites id m n) (h' : BlockWrites id n k) : BlockWrites id m k := by
  induction h' with
  | refl => exact h
  | store _ p v hp ih => exact (ih h).store p v hp

theorem live (h : BlockWrites id m n) (hr : SmallRange m p bytes) : SmallRange n p bytes := by
  induction h with
  | refl => exact hr
  | store _ _ _ _ ih => exact (ih hr).storeAt _ _

theorem other (h : BlockWrites id m n) (j : BlockId) (hj : j ≠ id) : n[j]? = m[j]? := by
  induction h with
  | refl => rfl
  | store _ p v hp ih =>
    rw [MemoryState.getElem?_storeAt_ne (q := ⟨j, 0⟩) (by simpa [hp] using hj)]
    exact ih

theorem wf (h : BlockWrites id m n) (alloc : AllocState)
    (hwf : (⟨alloc, m⟩ : GlobalState).WF) : (⟨alloc, n⟩ : GlobalState).WF := by
  induction h with
  | refl => exact hwf
  | store _ _ _ _ ih => exact (ih hwf).storeAt

theorem present (h : BlockWrites id m n) (global : ByteGlobal) (j : BlockId)
    (hj : j ≠ id) (hp : global.Present j m) : global.Present j n :=
  (h.other j hj).trans hp
end BlockWrites

theorem counter_writes (m : MemoryState) (context : Pointer) (lo hi size : Word) :
    BlockWrites context.id m (counterMemory m context lo hi size) := by
  exact ((BlockWrites.refl m).store (context.add 208#64) (appendLow lo size) rfl).store
    (context.add 216#64) (appendHigh hi lo size) rfl

theorem short_writes (s : GlobalState) (context data : Pointer) (used size : Word) :
    BlockWrites context.id s.mem (shortState s context data used size).mem := by
  exact ((BlockWrites.refl s.mem).store (context.add used)
    (s.mem.readAt data (8 * size.toNat)) rfl).store (context.add 200#64) (used + size) rfl

theorem tail_writes (s : GlobalState) (context data : Pointer) (size : Word) :
    BlockWrites context.id s.mem (tailState s context data size).mem := by
  unfold tailState
  split
  · exact .refl _
  · exact ((BlockWrites.refl s.mem).store context
      (s.mem.readAt (data.add (size &&& 18446744073709551488#64)) (8 * (size &&& 127#64).toNat)) rfl).store
        (context.add 200#64) (size &&& 127#64) rfl

theorem compression_writes (s : GlobalState) (context data : Pointer) (n : Nat) :
    BlockWrites context.id s.mem (compressionState s (context.add 128#64) data n).mem :=
  (BlockWrites.refl s.mem).store (context.add 128#64)
    (Spec.run (s.mem.readAt (context.add 128#64) 512) (readBytes s.mem data (128 * n))) rfl

theorem fill_writes (s : GlobalState) (context data : Pointer) (used : Word) :
    BlockWrites context.id s.mem (fillState s context data used).mem :=
  (BlockWrites.refl s.mem).store (context.add used)
    (s.mem.readAt data (8 * (128#64 - used).toNat)) rfl

theorem reset_writes (s : GlobalState) (context : Pointer) :
    BlockWrites context.id s.mem (resetState s context).mem :=
  (BlockWrites.refl s.mem).store (context.add 200#64) 0#64 rfl

theorem direct_writes (s : GlobalState) (context data : Pointer) (size : Word) :
    BlockWrites context.id s.mem (directState s context data size).mem := by
  unfold directState
  split
  · exact tail_writes s context data size
  · exact (compression_writes s context data (size >>> 7).toNat).trans
      (tail_writes (compressionState s (context.add 128#64) data (size >>> 7).toNat) context data size)

theorem result_writes (s : GlobalState) (context data : Pointer) (size : Word) :
    BlockWrites context.id s.mem (resultState s context data size).mem := by
  let t := startState s context size
  let used := s.mem.readAt (context.add 200#64) 64
  let filled := fillState t context data used
  let compressed := compressionState filled (context.add 128#64) context 1
  have hstart : BlockWrites context.id s.mem t.mem := counter_writes _ _ _ _ _
  unfold resultState
  split
  · exact .refl _
  · dsimp only
    split
    · exact hstart.trans (direct_writes t context data size)
    · split
      · exact hstart.trans (short_writes t context data used size)
      · exact (((hstart.trans (fill_writes t context data used)).trans
          (compression_writes filled context context 1)).trans (reset_writes compressed context)).trans
          (direct_writes (resetState compressed context) context
            (data.add (128#64 - used)) (size - (128#64 - used)))

theorem tail_allocator (s : GlobalState) (context data : Pointer) (size : Word) :
    (tailState s context data size).alloc = s.alloc := by
  unfold tailState
  split <;> rfl

theorem direct_allocator (s : GlobalState) (context data : Pointer) (size : Word) :
    s.alloc.nextFreeBlock ≤ (directState s context data size).alloc.nextFreeBlock := by
  unfold directState
  split
  · rw [tail_allocator]
  · rw [tail_allocator]
    exact Nat.le_succ _

theorem result_allocator (s : GlobalState) (context data : Pointer) (size : Word) :
    s.alloc.nextFreeBlock ≤ (resultState s context data size).alloc.nextFreeBlock := by
  let t := startState s context size
  let used := s.mem.readAt (context.add 200#64) 64
  let filled := fillState t context data used
  let compressed := compressionState filled (context.add 128#64) context 1
  unfold resultState
  split
  · exact Nat.le_refl _
  · dsimp only
    split
    · exact direct_allocator t context data size
    · split
      · exact Nat.le_refl _
      · exact (Nat.le_succ _).trans (direct_allocator (resetState compressed context) context
          (data.add (128#64 - used)) (size - (128#64 - used)))

theorem result_wf (s : GlobalState) (context data : Pointer) (size : Word) (hwf : s.WF) :
    (resultState s context data size).WF := by
  have h := (result_writes s context data size).wf s.alloc hwf
  intro j hj
  exact (h j hj).trans_le (result_allocator s context data size)

/-- The append frame has already been removed by each callee; append itself
allocates no block. Thus its final frame erasure changes no memory byte. -/
theorem result_erase (s : GlobalState) (context data : Pointer) (size : Word) (hwf : s.WF) :
    (resultState s context data size).mem.eraseFrom s.alloc.nextFreeBlock =
      (resultState s context data size).mem :=
  congrArg GlobalState.mem (GlobalState.eraseFrom_self ((result_writes s context data size).wf s.alloc hwf))

end Agave.Ed25519.Bridge.FiredancerSHAExecution.Append
