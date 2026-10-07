import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkPairStore
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionPairMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionBulkSecondBody

/-! Readback invariants for the circular first-block scratch and the append-only
second-block cache. Allocation identities suffice to separate the private buffers. -/
namespace Agave.Ed25519.SHA512.Execution.Avx2
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Spec
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000

structure BulkCachePrefix (mem : MemoryState) (cache : Pointer)
    (words : List Word) (n : Nat) : Prop where
  live : SmallRange mem cache 640
  words : ∀ t, t < n → mem.readAt (cache.add (BitVec.ofNat 64 (8*t))) 64 = scheduleKW words t

def bulkCacheStore (mem : MemoryState) (cache : Pointer) (n : Nat)
    (lo hi : Word) : MemoryState :=
  mem.storeAt (cache.add (BitVec.ofNat 64 (8*n))) (hi ++ lo)

private theorem bulk_cache_offset (mem : MemoryState) (cache : Pointer)
    (h : SmallRange mem cache 640) (t : Nat) (ht : t ≤ 80) :
    (cache.add (BitVec.ofNat 64 (8*t))).offsetInBits = cache.offsetInBits + 64*t := by
  have hx := Pointer.offsetInBits_add (h.no_wrap (k := 8*t) (by omega))
  have hsmall : 8*t < 2^64 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall] at hx
  convert hx using 1
  omega

theorem bulkCacheStore_read (mem : MemoryState) (cache : Pointer)
    (h : SmallRange mem cache 640) (n t : Nat) (hn : n+1<80) (ht : t<80)
    (lo hi : Word) :
    (bulkCacheStore mem cache n lo hi).readAt (cache.add (BitVec.ofNat 64 (8*t))) 64 =
      if t=n then lo else if t=n+1 then hi else mem.readAt (cache.add (BitVec.ofNat 64 (8*t))) 64 := by
  have hp := bulk_cache_offset mem cache h n (by omega)
  have hq := bulk_cache_offset mem cache h t (by omega)
  have hfits : Fits mem (cache.add (BitVec.ofNat 64 (8*n))) 128 :=
    h.fits_add (k := 8*n) (count := 16) (by omega)
  unfold bulkCacheStore
  by_cases h0 : t=n
  · subst t
    rw [ite_eq_left rfl]
    have hr := MemoryState.readAt_storeAt_subrange hfits
      (q := cache.add (BitVec.ofNat 64 (8*n))) (w' := 64) rfl (by omega) (by omega) (hi ++ lo)
    simpa only [Nat.sub_self, BitVec.extractLsb'_append_eq_right] using hr
  · rw [ite_eq_right h0]
    by_cases h1 : t=n+1
    · rw [ite_eq_left h1]
      have hoff : (cache.add (BitVec.ofNat 64 (8*t))).offsetInBits -
          (cache.add (BitVec.ofNat 64 (8*n))).offsetInBits = 64 := by
        rw [hp, hq]; omega
      have hr := MemoryState.readAt_storeAt_subrange hfits
        (q := cache.add (BitVec.ofNat 64 (8*t))) (w' := 64) rfl
        (by rw [hp, hq]; omega) (by rw [hoff]) (hi ++ lo)
      simpa only [hoff, BitVec.extractLsb'_append_eq_left] using hr
    · rw [ite_eq_right h1]
      apply MemoryState.readAt_storeAt_disjoint
      simp only [Range.Disjoint, Range.of, Pointer.add_id, hp, hq]
      omega

theorem BulkCachePrefix.advance {mem : MemoryState} {cache : Pointer} {words : List Word}
    {n : Nat} (h : BulkCachePrefix mem cache words n) (hn : n+1<80) :
    BulkCachePrefix (bulkCacheStore mem cache n (scheduleKW words n) (scheduleKW words (n+1)))
      cache words (n+2) := by
  refine ⟨h.live.storeAt _ _, ?_⟩
  intro t ht
  rw [bulkCacheStore_read mem cache h.live n t hn (by omega)]
  split_ifs with h0 h1
  · subst t; rfl
  · subst t; rfl
  · exact h.words t (by omega)

theorem BulkCachePrefix.complete {mem : MemoryState} {cache : Pointer} {words : List Word}
    (h : BulkCachePrefix mem cache words 80) : BulkSecondSchedule mem cache words :=
  ⟨h.live, h.words⟩

theorem bulk_read_store_ne (mem : MemoryState) (p q : Pointer) (x : BitVec w) (w' : Nat)
    (hne : p.id ≠ q.id) : (mem.storeAt p x).readAt q w' = mem.readAt q w' := by
  apply MemoryState.readAt_storeAt_disjoint
  simp [Range.Disjoint, Range.of, hne]

theorem BulkCachePrefix.store_ne {mem : MemoryState} {cache : Pointer} {words : List Word}
    {n : Nat} (h : BulkCachePrefix mem cache words n) (p : Pointer) (x : BitVec w)
    (hne : p.id ≠ cache.id) : BulkCachePrefix (mem.storeAt p x) cache words n := by
  refine ⟨h.live.storeAt p x, ?_⟩
  intro t ht
  rw [bulk_read_store_ne mem p _ x 64 (by simpa using hne)]
  exact h.words t ht

theorem PairScratch.bulk_store_ne {mem : MemoryState} {scratch : Pointer} {words : List Word}
    {b j : Nat} (h : PairScratch mem scratch words b j) (p : Pointer) (x : BitVec w)
    (hne : p.id ≠ scratch.id) : PairScratch (mem.storeAt p x) scratch words b j := by
  refine ⟨h.live.storeAt p x, ?_⟩
  intro t ht
  rw [bulk_read_store_ne mem p _ x 64 (by simpa using hne)]
  exact h.slots t ht

theorem PairConstants.bulk_store_ne {mem : MemoryState} {k : Pointer}
    (h : PairConstants mem k) (p : Pointer) (x : BitVec w) (hne : p.id ≠ k.id) :
    PairConstants (mem.storeAt p x) k := by
  refine ⟨h.live.storeAt p x, ?_⟩
  intro r hr
  rw [bulk_read_store_ne mem p _ x 128 (by simpa using hne)]
  exact h.pairs r hr

/-- Live 128-byte cache group selected by the exact bb11 address computation. -/
theorem bulk_cache_group_live {mem : MemoryState} {cache : Pointer}
    (h : SmallRange mem cache 640) (g : Nat) (hg : g<5) :
    SmallRange mem (cache.add (BitVec.ofNat 64 (128*g))) 128 := by
  have hn := h.no_wrap (k := 128*g) (by omega)
  have hsmall : 128*g<2^64 := by omega
  obtain ⟨block, hb, hsize, hfit⟩ := h
  refine ⟨block, hb, hsize, ?_⟩
  simp only [Pointer.add, BitVec.toNat_add_of_not_uaddOverflow hn,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsmall]
  omega

theorem bulk_cache_pair_pointer (cache : Pointer) (b j : Nat) :
    (cache.add (BitVec.ofNat 64 (128*(b+1)))).add (BitVec.ofNat 64 (16*j)) =
      cache.add (BitVec.ofNat 64 (8*(16*(b+1)+2*j))) := by
  rw [Pointer.add_add, ← BitVec.ofNat_add]
  congr 2
  omega

def bulkPairSpecMem (mem : GlobalState) (scratch cache : Pointer) (b j : Nat)
    (words₀ words₁ : List Word) : GlobalState :=
  bulkPairStoreState mem scratch (cache.add (BitVec.ofNat 64 (128*(b+1)))) j
    (scheduleKW words₀ (16*(b+1)+2*j)) (scheduleKW words₀ (16*(b+1)+2*j+1))
    (scheduleKW words₁ (16*(b+1)+2*j)) (scheduleKW words₁ (16*(b+1)+2*j+1))

theorem bulkPairSpecMem_scratch (mem : GlobalState) (scratch cache : Pointer)
    (b j : Nat) (words₀ words₁ : List Word) (hj : j<8)
    (hs : PairScratch mem.mem scratch words₀ b j) (hsep : scratch.id ≠ cache.id) :
    PairScratch (bulkPairSpecMem mem scratch cache b j words₀ words₁).mem
      scratch words₀ b (j+1) := by
  exact (hs.advance hj).bulk_store_ne _ _ (by simpa using hsep.symm)

theorem bulkPairSpecMem_cache (mem : GlobalState) (scratch cache : Pointer)
    (b j : Nat) (words₀ words₁ : List Word) (hb : b<4) (hj : j<8)
    (hc : BulkCachePrefix mem.mem cache words₁ (16*(b+1)+2*j))
    (hsep : scratch.id ≠ cache.id) :
    BulkCachePrefix (bulkPairSpecMem mem scratch cache b j words₀ words₁).mem
      cache words₁ (16*(b+1)+2*(j+1)) := by
  have hc' := hc.store_ne (scratch.add (BitVec.ofNat 64 (16*j)))
    (scheduleKW words₀ (16*(b+1)+2*j+1) ++ scheduleKW words₀ (16*(b+1)+2*j))
    (by simpa using hsep)
  have ha := hc'.advance (by omega)
  simpa only [bulkPairSpecMem, bulkPairStoreState, pairStoreState, pairScratchStore,
    bulk_cache_pair_pointer, bulkCacheStore, show 16*(b+1)+2*j+2=16*(b+1)+2*(j+1) by omega] using ha

theorem bulkPairSpecMem_constants (mem : GlobalState) (scratch cache k : Pointer)
    (b j : Nat) (words₀ words₁ : List Word) (hk : PairConstants mem.mem k)
    (hsk : scratch.id ≠ k.id) (hck : cache.id ≠ k.id) :
    PairConstants (bulkPairSpecMem mem scratch cache b j words₀ words₁).mem k :=
  (hk.bulk_store_ne _ _ (by simpa using hsk)).bulk_store_ne _ _ (by simpa using hck)

end Agave.Ed25519.SHA512.Execution.Avx2
