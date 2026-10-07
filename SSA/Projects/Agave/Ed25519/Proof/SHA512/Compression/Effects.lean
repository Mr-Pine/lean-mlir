import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Globals

/-! Exact effects for a compressor or finalizer that may initialize its CPU
feature cache. A warm invocation has the original single-store effect. A cold
invocation may additionally change precisely its one-byte cache allocation.
Neither case permits writes to any other allocation or byte range.
-/

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

def CacheWarm (g : CompressionGlobals) (state : GlobalState) : Prop :=
  ∃ value : BitVec 8, (value = 0 ∨ value = 1) ∧
    (cacheMemory value).Present g.cache state.mem

structure WarmCompressionReady (g : CompressionGlobals) (state : GlobalState) : Prop where
  «globals» : CompressionReady g state
  warm : CacheWarm g state

/-- Cached results remain unchanged. Only the initial sentinel may change,
and only to a Boolean result. Leaving the cache untouched is also permitted
so the same effect vocabulary covers a direct backend call. -/
def CacheTransition (old new : BitVec 8) : Prop :=
  new = old ∨ (old = 255 ∧ (new = 0 ∨ new = 1))

theorem CacheTransition.legal (h : CacheTransition old new) (ho : CacheByteLegal old) :
    CacheByteLegal new := by
  rcases h with h | ⟨_, h⟩
  · simpa [h] using ho
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

theorem CacheTransition.warm_eq (h : CacheTransition old new) (ho : old = 0 ∨ old = 1) :
    new = old := by
  rcases h with h | ⟨h, _⟩
  · exact h
  · rcases ho with rfl | rfl <;> norm_num at h

theorem CacheTransition.refl (value : BitVec 8) : CacheTransition value value := Or.inl rfl

theorem CacheTransition.trans (h₁ : CacheTransition a b) (h₂ : CacheTransition b c) :
    CacheTransition a c := by
  rcases h₁ with rfl | ⟨rfl, hb⟩
  · exact h₂
  · rcases h₂ with rfl | ⟨hbad, _⟩
    · exact Or.inr ⟨rfl, hb⟩
    · rcases hb with rfl | rfl <;> norm_num at hbad

/-- The entire memory effect is a legal cache transition followed by one
public store. Private stack allocations must have been erased at return. -/
def CacheFramedStoreEffect (g : CompressionGlobals) (before after : GlobalState)
    (dst : Pointer) (value : BitVec w) : Prop :=
  ∃ old new : BitVec 8,
    CacheByteLegal old ∧ (cacheMemory old).Present g.cache before.mem ∧
    CacheTransition old new ∧
    after.mem = (before.mem.storeAt g.cachePtr new).storeAt dst value ∧
    before.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock

abbrev CompressionStoreEffect (g : CompressionGlobals) (before after : GlobalState)
    (chain : Pointer) (value : BitVec 512) : Prop :=
  CacheFramedStoreEffect g before after chain value

theorem cache_present_unique (g : CompressionGlobals) (m : MemoryState)
    (hx : (cacheMemory x).Present g.cache m) (hy : (cacheMemory y).Present g.cache m) :
    x = y := by
  have hrx : m.readAt g.cachePtr 8 = x := hx.readAt
  have hry : m.readAt g.cachePtr 8 = y := hy.readAt
  exact hrx.symm.trans hry

theorem cache_present_store (g : CompressionGlobals) (m : MemoryState)
    (old new : BitVec 8) (h : (cacheMemory old).Present g.cache m) :
    (cacheMemory new).Present g.cache (m.storeAt g.cachePtr new) := by
  have hm : m[g.cachePtr.id]? = some ⟨1, old⟩ := h
  have hs := MemoryState.getElem?_storeAt_self (p := g.cachePtr) (x := new) hm
  simpa [ByteGlobal.Present, cacheMemory, CompressionGlobals.cachePtr,
    Pointer.offsetInBits, Memory.spliceBits] using hs

/-- Re-storing the already present cache byte is literally a no-op on the
whole memory map, not merely indistinguishable to one selected read. -/
theorem cache_store_same (g : CompressionGlobals) (m : MemoryState) (value : BitVec 8)
    (h : (cacheMemory value).Present g.cache m) : m.storeAt g.cachePtr value = m := by
  apply MemoryState.ext
  apply Std.ExtHashMap.ext_getElem?
  intro id
  change (m.storeAt g.cachePtr value)[id]? = m[id]?
  by_cases hid : id = g.cache
  · subst id
    have hs := cache_present_store g m value value h
    exact hs.trans h.symm
  · exact MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hid

theorem CacheFramedStoreEffect.to_storeEffect
    (he : CacheFramedStoreEffect g before after dst value) (hw : CacheWarm g before) :
    StoreEffect before after dst value := by
  obtain ⟨old, new, _, hp, ht, hm, hc⟩ := he
  obtain ⟨warm, hw, hpw⟩ := hw
  have hold := cache_present_unique g before.mem hp hpw
  have hnew : new = old := ht.warm_eq (by simpa only [hold] using hw)
  rw [hnew, cache_store_same g before.mem old hp] at hm
  exact ⟨hm, hc⟩

theorem CacheFramedStoreEffect.wellFormed
    (he : CacheFramedStoreEffect g before after dst value) (hwf : before.WF) :
    after.WF := by
  obtain ⟨_, new, _, _, _, hm, hc⟩ := he
  rw [GlobalState.WF]
  intro k hk
  rw [hm] at hk
  have hs := (GlobalState.WF.storeAt (p := g.cachePtr) (x := new) hwf).storeAt
    (p := dst) (x := value)
  exact lt_of_lt_of_le (hs k hk) hc

theorem CacheFramedStoreEffect.read_dst
    (he : CacheFramedStoreEffect g before after dst (value : BitVec w))
    (hc : Fits before.mem dst w) : after.mem.readAt dst w = value := by
  obtain ⟨_, new, _, _, _, hm, _⟩ := he
  rw [hm, MemoryState.readAt_storeAt_self (hc.storeAt (x := new) (q := g.cachePtr))]

/-- Every observation outside the declared cache and destination writes is
preserved, including observations in other parts of the same allocation. -/
theorem CacheFramedStoreEffect.read_disjoint
    (he : CacheFramedStoreEffect g before after dst (value : BitVec w))
    (q : Pointer) (width : Nat)
    (hd : (Range.of dst w).Disjoint (Range.of q width))
    (hb : (Range.of g.cachePtr 8).Disjoint (Range.of q width)) :
    after.mem.readAt q width = before.mem.readAt q width := by
  obtain ⟨_, new, _, _, _, hm, _⟩ := he
  rw [hm, MemoryState.readAt_storeAt_disjoint hd value,
    MemoryState.readAt_storeAt_disjoint hb new]

theorem CacheFramedStoreEffect.ready
    (he : CacheFramedStoreEffect g before after dst value)
    (hr : CompressionReady g before)
    (hdc : dst.id ≠ g.constants) (hdb : dst.id ≠ g.cache) :
    CompressionReady g after := by
  obtain ⟨old, new, ho, hp, ht, hm, _⟩ := he
  refine ⟨?_, ⟨new, ht.legal ho, ?_⟩, hr.separate⟩
  · rw [hm]
    exact (hr.constants.storeAt hr.separate).storeAt hdc.symm
  · rw [hm]
    exact (cache_present_store g before.mem old new hp).storeAt hdb.symm

/-- A cache-disjoint public store exposes precisely the recorded legal
transition. This fact can be retained by a larger composable frame relation. -/
theorem CacheFramedStoreEffect.cache_transition
    (he : CacheFramedStoreEffect g before after dst value) (hd : dst.id ≠ g.cache) :
    CacheTransition (before.mem.readAt g.cachePtr 8) (after.mem.readAt g.cachePtr 8) := by
  obtain ⟨old, new, _, hp, ht, hm, _⟩ := he
  have hb : before.mem.readAt g.cachePtr 8 = old := hp.readAt
  have ha : after.mem.readAt g.cachePtr 8 = new := by
    rw [hm, MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne hd) value]
    exact (cache_present_store g before.mem old new hp).readAt
  simpa only [hb, ha] using ht

theorem CacheFramedStoreEffect.cache_unchanged
    (he : CacheFramedStoreEffect g before after dst value) (hw : CacheWarm g before)
    (hd : dst.id ≠ g.cache) :
    after.mem.readAt g.cachePtr 8 = before.mem.readAt g.cachePtr 8 := by
  obtain ⟨old, hw, hp⟩ := hw
  apply (he.cache_transition hd).warm_eq
  have hb : before.mem.readAt g.cachePtr 8 = old := hp.readAt
  simpa only [hb] using hw

theorem CacheWarm.storeAt (hw : CacheWarm g state) (p : Pointer) (v : BitVec w)
    (hp : p.id ≠ g.cache) : CacheWarm g { state with mem := state.mem.storeAt p v } := by
  obtain ⟨value, hv, hc⟩ := hw
  exact ⟨value, hv, hc.storeAt hp.symm⟩

theorem CacheWarm.of_frame (hw : CacheWarm g before) (mark : Nat)
    (hframe : after.mem.eraseFrom mark = before.mem) : CacheWarm g after := by
  obtain ⟨value, hv, hc⟩ := hw
  exact ⟨value, hv, present_of_frame _ _ _ _ _ hframe hc⟩

/-- Any Boolean consumer of the public output observes exactly the specified
value, even when this is the first call and its cache starts cold. -/
theorem CacheFramedStoreEffect.boolean_observation
    (he : CacheFramedStoreEffect g before after dst (value : BitVec w))
    (hf : Fits before.mem dst w) (observe : BitVec w → Bool) :
    observe (after.mem.readAt dst w) = observe value := by
  rw [he.read_dst hf]

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
