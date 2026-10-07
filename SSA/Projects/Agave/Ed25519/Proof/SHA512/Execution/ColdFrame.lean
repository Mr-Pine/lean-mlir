import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ContextContract
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContracts

/-! A cold SHA dispatch may change one designated one-byte allocation. This
frame retains exact allocation/block equality everywhere else, rather than
claiming the ordinary output-only frame used for a warm dispatch. -/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge

set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

variable {g : CompressionGlobals} {w : Nat} {value : BitVec w}

structure CacheFrame (g : CompressionGlobals) (before after : MemoryState) : Prop where
  blocks : ∀ id, id ≠ g.cache → after[id]? = before[id]?
  cache : ∃ value, CacheByteLegal value ∧ (cacheMemory value).Present g.cache after
  transition : CacheTransition (before.readAt g.cachePtr 8) (after.readAt g.cachePtr 8)

/-- The complete effect permits exactly the expected output store and the
single designated cache byte, with no other allocation-domain change. -/
structure CacheOutputEffect (g : CompressionGlobals) (before after : GlobalState)
    (out : Pointer) (value : BitVec w) : Prop where
  memory : CacheFrame g (before.mem.storeAt out value) after.mem
  counter : before.alloc.nextFreeBlock ≤ after.alloc.nextFreeBlock

theorem CacheFrame.refl (g : CompressionGlobals) (m : MemoryState)
    (h : ∃ value, CacheByteLegal value ∧ (cacheMemory value).Present g.cache m) :
    CacheFrame g m m := ⟨fun _ _ => rfl, h, CacheTransition.refl _⟩

theorem CacheFrame.trans (h₁ : CacheFrame g a b) (h₂ : CacheFrame g b c) : CacheFrame g a c :=
  ⟨fun id hi => (h₂.blocks id hi).trans (h₁.blocks id hi), h₂.cache,
    h₁.transition.trans h₂.transition⟩

theorem CacheFrame.read (h : CacheFrame g before after) (ptr : Pointer) (width : Nat)
    (hp : ptr.id ≠ g.cache) : after.readAt ptr width = before.readAt ptr width := by
  unfold MemoryState.readAt
  rw [h.blocks ptr.id hp]

theorem CacheFrame.smallRange (h : CacheFrame g before after) (ptr : Pointer) (n : Nat)
    (hp : ptr.id ≠ g.cache) (hl : SmallRange before ptr n) : SmallRange after ptr n := by
  rcases hl with ⟨block, hb, hsmall, hsize⟩
  exact ⟨block, (h.blocks ptr.id hp).trans hb, hsmall, hsize⟩

theorem CacheFrame.present (h : CacheFrame g before after) (global : ByteGlobal) (id : BlockId)
    (hne : id ≠ g.cache) (hp : global.Present id before) : global.Present id after :=
  (h.blocks id hne).trans hp

theorem CacheFrame.compressionReady (h : CacheFrame g before after)
    (hb : CompressionReady g ⟨alloc, before⟩) : CompressionReady g ⟨alloc', after⟩ :=
  ⟨h.present _ _ hb.separate hb.constants, h.cache, hb.separate⟩

private theorem storeAt_lookup_congr (before after : MemoryState) (ptr : Pointer)
    (value : BitVec w) (h : after[ptr.id]? = before[ptr.id]?) :
    (after.storeAt ptr value)[ptr.id]? = (before.storeAt ptr value)[ptr.id]? := by
  have heq : after.mem[ptr.id]? = before.mem[ptr.id]? := h
  unfold MemoryState.storeAt
  rw [h]
  split <;> simp_all [MemoryState.getElem?_eq]

/-- A store outside the cache can be made on both sides of the relation. -/
theorem CacheFrame.storeAt (h : CacheFrame g before after) (ptr : Pointer) (value : BitVec w)
    (hp : ptr.id ≠ g.cache) : CacheFrame g (before.storeAt ptr value) (after.storeAt ptr value) := by
  constructor
  · intro id hi
    by_cases hid : id = ptr.id
    · subst id
      exact storeAt_lookup_congr before after ptr value (h.blocks ptr.id hp)
    · simpa only [MemoryState.getElem?_eq] using
        (MemoryState.getElem?_storeAt_ne (m := after) (p := ptr) (q := ⟨id, 0⟩)
          (x := value) hid).trans
          ((h.blocks id hi).trans
            (MemoryState.getElem?_storeAt_ne (m := before) (p := ptr) (q := ⟨id, 0⟩)
              (x := value) hid).symm)
  · obtain ⟨byte, hb, hcache⟩ := h.cache
    exact ⟨byte, hb, hcache.storeAt hp.symm⟩
  · simpa only [MemoryState.readAt_storeAt_disjoint (p := ptr) (q := g.cachePtr) (Range.disjoint_of_id_ne hp) value] using h.transition

/-- Removing private frames preserves the relation if the cache is a caller
allocation below the frame mark. -/
theorem CacheFrame.eraseFrom (h : CacheFrame g before after) (mark : Nat)
    (hcache : g.cache.id < mark) : CacheFrame g (before.eraseFrom mark) (after.eraseFrom mark) := by
  constructor
  · intro id hi
    have heq := h.blocks id hi
    simpa [MemoryState.eraseFrom, MemoryState.getElem?_eq,
      Std.ExtHashMap.getElem?_filter'] using congrArg
        (fun x => x.filter (fun _ => decide (id.id < mark))) heq
  · obtain ⟨byte, hb, hc⟩ := h.cache
    refine ⟨byte, hb, ?_⟩
    simpa [ByteGlobal.Present, MemoryState.eraseFrom, MemoryState.getElem?_eq,
      Std.ExtHashMap.getElem?_filter', hcache] using hc
  · have hread (m : MemoryState) :
        (m.eraseFrom mark).readAt g.cachePtr 8 = m.readAt g.cachePtr 8 := by
      simp [MemoryState.readAt, MemoryState.eraseFrom, MemoryState.getElem?_eq,
        Std.ExtHashMap.getElem?_filter', CompressionGlobals.cachePtr, hcache]
      cases m.mem[g.cache]? <;> rfl
    simpa only [hread] using h.transition

/-- Convert the concrete compressor's exact two-store effect into the
composable cache frame. The cache's one-byte shape comes from its postcondition. -/
theorem CacheFramedStoreEffect.cacheOutput (he : CacheFramedStoreEffect g before after chain value)
    (hr : CompressionReady g after) (hchain : chain.id ≠ g.cache) : CacheOutputEffect g before after chain value := by
  have ht := he.cache_transition hchain
  obtain ⟨old, byte, holdLegal, holdPresent, transition, hm, hcounter⟩ := he
  refine ⟨⟨?_, hr.cache, ?_⟩, hcounter⟩
  · intro id hi
    rw [hm]
    by_cases hid : id = chain.id
    · subst id
      by_cases hc : chain.id = g.cache
      · exact False.elim (hi hc)
      · have heq : (before.mem.storeAt g.cachePtr byte)[chain.id]? = before.mem[chain.id]? :=
          MemoryState.getElem?_storeAt_ne (q := chain) hc
        exact storeAt_lookup_congr before.mem (before.mem.storeAt g.cachePtr byte)
          chain value heq
    · rw [MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hid,
        MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hi,
        MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hid]
  · simpa only [MemoryState.readAt_storeAt_disjoint (p := chain) (q := g.cachePtr) (Range.disjoint_of_id_ne hchain) value] using ht

theorem CacheOutputEffect.smallRange (he : CacheOutputEffect g before after out value)
    (ptr : Pointer) (n : Nat) (hp : ptr.id ≠ g.cache)
    (hl : SmallRange before.mem ptr n) : SmallRange after.mem ptr n :=
  he.memory.smallRange ptr n hp (hl.storeAt _ _)

theorem CacheOutputEffect.read (he : CacheOutputEffect g before after out value)
    (ptr : Pointer) (width : Nat) (hp : ptr.id ≠ g.cache)
    (hd : (Range.of out w).Disjoint (Range.of ptr width)) :
    after.mem.readAt ptr width = before.mem.readAt ptr width := by
  rw [he.memory.read ptr width hp, MemoryState.readAt_storeAt_disjoint hd value]

theorem CacheOutputEffect.output (he : CacheOutputEffect g before after out value)
    (hp : out.id ≠ g.cache) (hf : Fits before.mem out w) : after.mem.readAt out w = value := by
  rw [he.memory.read out w hp, MemoryState.readAt_storeAt_self hf]

theorem CacheOutputEffect.readBytes (he : CacheOutputEffect g before after out value)
    (ptr : Pointer) (n : Nat) (hp : ptr.id ≠ g.cache)
    (hl : SmallRange before.mem ptr n)
    (hd : (Range.of out w).Disjoint (Range.of ptr (8 * n))) :
    readBytes after.mem ptr n = readBytes before.mem ptr n := by
  rw [readBytes_eq_bytesOf _ _ _ (he.smallRange ptr n hp hl),
    readBytes_eq_bytesOf _ _ _ hl, he.read ptr (n * 8) hp (by simpa [Nat.mul_comm] using hd)]

/-- An unchanged warm cache collapses the narrowed frame to exact memory
equality. The cache shape is checked on both sides. -/
theorem CacheFrame.eq_of_cache_unchanged (h : CacheFrame g before after)
    (hb : ∃ byte, CacheByteLegal byte ∧ (cacheMemory byte).Present g.cache before)
    (hsame : after.readAt g.cachePtr 8 = before.readAt g.cachePtr 8) : after = before := by
  obtain ⟨old, _, hold⟩ := hb
  obtain ⟨new, _, hnew⟩ := h.cache
  have hn : new = old := by
    have hnr : after.readAt g.cachePtr 8 = new := hnew.readAt
    have hor : before.readAt g.cachePtr 8 = old := hold.readAt
    exact hnr.symm.trans (hsame.trans hor)
  have hall (id : BlockId) : after[id]? = before[id]? := by
    by_cases hi : id = g.cache
    · subst id
      rw [hnew, hold, hn]
    · exact h.blocks id hi
  apply MemoryState.ext
  exact Std.ExtHashMap.ext_getElem? hall

/-- Exact output-only effects are retained for a dispatcher proved to leave
an already initialized cache byte unchanged. -/
theorem CacheOutputEffect.warm (he : CacheOutputEffect g before after out value)
    (hr : CompressionReady g before) (hp : out.id ≠ g.cache)
    (hwarm : CacheWarm g before) : StoreEffect before after out value := by
  have ht : CacheTransition (before.mem.readAt g.cachePtr 8) (after.mem.readAt g.cachePtr 8) := by
    simpa only [MemoryState.readAt_storeAt_disjoint (p := out) (q := g.cachePtr) (Range.disjoint_of_id_ne hp) value] using he.memory.transition
  have hsame : after.mem.readAt g.cachePtr 8 = before.mem.readAt g.cachePtr 8 := by
    obtain ⟨old, hold, hread⟩ := hwarm
    have hr' : before.mem.readAt g.cachePtr 8 = old := hread.readAt
    exact ht.warm_eq (by simpa only [hr'] using hold)
  have hcache : ∃ byte, CacheByteLegal byte ∧
      (cacheMemory byte).Present g.cache (before.mem.storeAt out value) := by
    obtain ⟨byte, hb, hc⟩ := hr.cache
    exact ⟨byte, hb, hc.storeAt hp.symm⟩
  refine ⟨he.memory.eq_of_cache_unchanged hcache ?_, he.counter⟩
  rw [MemoryState.readAt_storeAt_disjoint (p := out) (q := g.cachePtr) (Range.disjoint_of_id_ne hp) value]
  exact hsame

theorem CacheOutputEffect.wellFormed (he : CacheOutputEffect g before after out value)
    (hr : CompressionReady g before) (hwf : before.WF) : after.WF := by
  intro id hid
  apply lt_of_lt_of_le _ he.counter
  by_cases hi : id = g.cache
  · subst id
    obtain ⟨byte, _, hc⟩ := hr.cache
    exact hwf.lt hc.fits.mem
  · have hs : id ∈ (before.mem.storeAt out value).mem := by
      rw [Std.ExtHashMap.mem_iff_isSome_getElem?] at hid ⊢
      change ((before.mem.storeAt out value)[id]?).isSome = true
      change (after.mem[id]?).isSome = true at hid
      rw [he.memory.blocks id hi] at hid
      exact hid
    exact hwf.storeAt id hs

/-- Internal writes disappear under frame erasure, even when the public
cache byte is retained and has changed. -/
theorem CacheOutputEffect.erase_internal (he : CacheOutputEffect g before after out value)
    (mark : Nat) (hcache : g.cache.id < mark) (hout : mark ≤ out.id.id) :
    CacheFrame g (before.mem.eraseFrom mark) (after.mem.eraseFrom mark) := by
  have h := he.memory.eraseFrom mark hcache
  rw [MemoryState.eraseFrom_storeAt, MemoryState.storeAt_eraseFrom_of_le hout] at h
  exact h

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
