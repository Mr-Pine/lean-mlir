import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionReturn

namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec

structure BulkPairMemFrame (scratch cache : Pointer) (before after : GlobalState) : Prop where
  alloc : after.alloc = before.alloc
  read : ∀ (p : Pointer) (w : Nat), scratch.id ≠ p.id → cache.id ≠ p.id →
    after.mem.readAt p w = before.mem.readAt p w
  live : ∀ {p : Pointer} {bytes : Nat},
    SmallRange before.mem p bytes → SmallRange after.mem p bytes
  erase : ∀ mark, mark ≤ scratch.id.id → mark ≤ cache.id.id →
    after.mem.eraseFrom mark = before.mem.eraseFrom mark

theorem BulkPairMemFrame.refl (scratch cache : Pointer) (mem : GlobalState) :
    BulkPairMemFrame scratch cache mem mem :=
  ⟨rfl, fun _ _ _ _ => rfl, fun h => h, fun _ _ _ => rfl⟩

theorem BulkPairMemFrame.trans {scratch cache : Pointer} {a b c : GlobalState}
    (h₀ : BulkPairMemFrame scratch cache a b) (h₁ : BulkPairMemFrame scratch cache b c) :
    BulkPairMemFrame scratch cache a c :=
  ⟨h₁.alloc.trans h₀.alloc,
    fun p w hs hc => (h₁.read p w hs hc).trans (h₀.read p w hs hc),
    fun h => h₁.live (h₀.live h),
    fun mark hs hc => (h₁.erase mark hs hc).trans (h₀.erase mark hs hc)⟩

theorem bulkPairSpecMem_frame (mem : GlobalState) (scratch cache : Pointer)
    (b j : Nat) (words₀ words₁ : List Word) :
    BulkPairMemFrame scratch cache mem (bulkPairSpecMem mem scratch cache b j words₀ words₁) := by
  constructor
  · rfl
  · intro p w hs hc
    unfold bulkPairSpecMem bulkPairStoreState pairStoreState pairScratchStore
    rw [bulk_read_store_ne _ _ p _ w (by simpa using hc),
      bulk_read_store_ne _ _ p _ w (by simpa using hs)]
  · intro p bytes h
    exact (h.storeAt _ _).storeAt _ _
  · intro mark hs hc
    simp only [bulkPairSpecMem, bulkPairStoreState, pairStoreState, pairScratchStore,
      MemoryState.eraseFrom_storeAt]
    rw [MemoryState.storeAt_eraseFrom_of_le (p := scratch.add _) hs,
      MemoryState.storeAt_eraseFrom_of_le (p := (cache.add _).add _) hc]

end Agave.Ed25519.SHA512.Execution.Avx2
