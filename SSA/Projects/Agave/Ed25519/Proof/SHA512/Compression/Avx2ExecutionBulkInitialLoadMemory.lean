import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkInitialLoadSlices
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionInitialMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairMemoryFrame

/-! Readback and frame of the sixteen interleaved stores in bb9. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Agave.Ed25519.Verifier.Execution.Challenge
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def bulkInitialStores (mem : GlobalState) (scratch cache : Pointer)
    (first second : Bytes) : Nat → GlobalState
  | 0 => mem
  | n+1 => bulkInitialPairState (bulkInitialStores mem scratch cache first second n)
      scratch cache n (initialPairLow first n) (initialPairHigh first n)
        (initialPairLow second n) (initialPairHigh second n)

theorem bulkInitialPairState_frame (mem : GlobalState) (scratch cache : Pointer)
    (j : Nat) (lo hi lo' hi' : Word) :
    BulkPairMemFrame scratch cache mem (bulkInitialPairState mem scratch cache j lo hi lo' hi') := by
  constructor
  · rfl
  · intro p w hs hc
    unfold bulkInitialPairState pairStoreState pairScratchStore
    rw [bulk_read_store_ne _ _ p _ w (by simpa using hc),
      bulk_read_store_ne _ _ p _ w (by simpa using hs)]
  · intro p bytes h
    exact (h.storeAt _ _).storeAt _ _
  · intro mark hs hc
    simp only [bulkInitialPairState, pairStoreState, pairScratchStore,
      MemoryState.eraseFrom_storeAt]
    rw [MemoryState.storeAt_eraseFrom_of_le (p := scratch.add _) hs,
      MemoryState.storeAt_eraseFrom_of_le (p := cache.add _) hc]

theorem bulkInitialStores_frame (mem : GlobalState) (scratch cache : Pointer)
    (first second : Bytes) (n : Nat) :
    BulkPairMemFrame scratch cache mem (bulkInitialStores mem scratch cache first second n) := by
  induction n with
  | zero => exact BulkPairMemFrame.refl _ _ _
  | succ n ih => exact ih.trans (bulkInitialPairState_frame _ _ _ _ _ _ _ _)

theorem bulkInitialStores_scratch_read (mem : GlobalState) (scratch cache : Pointer)
    (first second : Bytes) (n : Nat) (hn : n ≤ 8)
    (hs : SmallRange mem.mem scratch 128) (hsep : scratch.id ≠ cache.id) :
    ∀ t, t < 2*n → (bulkInitialStores mem scratch cache first second n).mem.readAt
      (scratch.add (BitVec.ofNat 64 (8*t))) 64 = scheduleKW (schedule first) t := by
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
    intro t ht
    have hn8 : n < 8 := by omega
    have hslive := (bulkInitialStores_frame mem scratch cache first second n).live hs
    simp only [bulkInitialStores, bulkInitialPairState, pairStoreState]
    unfold pairScratchStore
    rw [bulk_read_store_ne _ _ _ _ 64 (by simpa using hsep.symm)]
    change (pairScratchStore _ scratch n _ _).readAt _ _ = _
    rw [pairScratchStore_read _ scratch hslive n t hn8 (by omega),
      initialPairLow_eq first n hn8, initialPairHigh_eq first n hn8]
    split_ifs with h0 h1
    · subst t; rfl
    · subst t; rfl
    · exact ih (by omega) t (by omega)

theorem bulkInitialStores_scratch (mem : GlobalState) (scratch cache : Pointer)
    (first second : Bytes) (hs : SmallRange mem.mem scratch 128)
    (hsep : scratch.id ≠ cache.id) :
    PairScratch (bulkInitialStores mem scratch cache first second 8).mem scratch (schedule first) 0 0 := by
  refine ⟨(bulkInitialStores_frame mem scratch cache first second 8).live hs, ?_⟩
  intro t ht
  simpa only [Nat.mul_zero, Nat.not_lt_zero, ite_false, Nat.zero_add] using
    bulkInitialStores_scratch_read mem scratch cache first second 8 (by decide) hs hsep t ht

theorem bulkInitialStores_cache (mem : GlobalState) (scratch cache : Pointer)
    (first second : Bytes) (n : Nat) (hn : n ≤ 8)
    (hc : SmallRange mem.mem cache 640) (hsep : scratch.id ≠ cache.id) :
    BulkCachePrefix (bulkInitialStores mem scratch cache first second n).mem cache (schedule second) (2*n) := by
  induction n with
  | zero => exact ⟨hc, by intro t ht; omega⟩
  | succ n ih =>
    have h := (ih (by omega)).store_ne (scratch.add (BitVec.ofNat 64 (16*n)))
      (initialPairHigh first n ++ initialPairLow first n) (by simpa using hsep)
    have ha := h.advance (by omega)
    have hoff : 8*(2*n) = 16*n := by omega
    simpa only [bulkInitialStores, bulkInitialPairState, pairStoreState, pairScratchStore,
      bulkCacheStore, hoff, initialPairLow_eq second n (by omega),
      initialPairHigh_eq second n (by omega), show 2*n+2=2*(n+1) by omega] using ha

theorem bulkInitialStores_constants (mem : GlobalState) (scratch cache k : Pointer)
    (first second : Bytes) (n : Nat) (hk : PairConstants mem.mem k)
    (hsk : scratch.id ≠ k.id) (hck : cache.id ≠ k.id) :
    PairConstants (bulkInitialStores mem scratch cache first second n).mem k := by
  refine ⟨(bulkInitialStores_frame mem scratch cache first second n).live hk.live, ?_⟩
  intro r hr
  rw [(bulkInitialStores_frame mem scratch cache first second n).read _ _
    (by simpa using hsk) (by simpa using hck)]
  exact hk.pairs r hr

/-- Both input halves remain the original bytes throughout initialization. -/
theorem bulkInitialStores_load_first (mem : GlobalState) (data scratch cache : Pointer)
    (first second : Bytes) (n j : Nat) (hj : j < 8)
    (hd : SmallRange mem.mem data 256)
    (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id) :
    (bulkInitialStores mem scratch cache first second n).mem.readAt
      (data.add (BitVec.ofNat 64 (16*j))) 128 =
        readWordNative (readBytes mem.mem data 128) (2*j+1) ++
          readWordNative (readBytes mem.mem data 128) (2*j) := by
  rw [(bulkInitialStores_frame mem scratch cache first second n).read _ _
    (by simpa using hsd) (by simpa using hcd)]
  exact load_initial_pair_native mem.mem data (smallRange_mono hd (by decide)) j hj

theorem bulkInitialStores_load_second (mem : GlobalState) (data scratch cache : Pointer)
    (first second : Bytes) (n j : Nat) (hj : j < 8)
    (hd : SmallRange mem.mem data 256)
    (hsd : scratch.id ≠ data.id) (hcd : cache.id ≠ data.id) :
    (bulkInitialStores mem scratch cache first second n).mem.readAt
      (data.add (BitVec.ofNat 64 (128+16*j))) 128 =
        readWordNative (readBytes mem.mem (data.add 128#64) 128) (2*j+1) ++
          readWordNative (readBytes mem.mem (data.add 128#64) 128) (2*j) := by
  rw [(bulkInitialStores_frame mem scratch cache first second n).read _ _
    (by simpa using hsd) (by simpa using hcd)]
  have hp : (data.add 128#64).add (BitVec.ofNat 64 (16*j)) =
      data.add (BitVec.ofNat 64 (128+16*j)) := by
    rw [Pointer.add_add, ← BitVec.ofNat_add]
  rw [← hp]
  exact load_initial_pair_native mem.mem (data.add 128#64)
    (smallRange_add hd (k := 128) (count := 128) (by decide)) j hj

end Agave.Ed25519.SHA512.Execution.Avx2
