import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdFrame
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Locals

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Challenge

variable {g : CompressionGlobals} {s entry before after : GlobalState}
  {base m : MemoryState} {mark w : Nat} {dst : Pointer} {value : BitVec w}

/-- Public SHA and scalar globals, and explicit provenance separation from
the cache's mutable byte. These conditions belong to the actual invocation. -/
structure ColdFinalizerReady (g : CompressionGlobals) (r : ScalarWide.Globals)
    (s : GlobalState) (out src : Pointer) : Prop where
  compression : CompressionReady g s
  reduction : ScalarWide.Ready r s out
  outputCache : out.id ≠ g.cache
  outputConstants : out.id ≠ g.constants
  sourceCache : src.id ≠ g.cache
  reduceRCache : r.address0.id ≠ g.cache
  reduceRRCache : r.address1.id ≠ g.cache

theorem CompressionReady.cache_lt (h : CompressionReady g s) (hwf : s.WF) :
    g.cache.id < s.alloc.nextFreeBlock := by
  obtain ⟨byte, _, hc⟩ := h.cache
  exact hwf.lt hc.fits.mem

theorem CompressionReady.constants_lt (h : CompressionReady g s) (hwf : s.WF) :
    g.constants.id < s.alloc.nextFreeBlock := hwf.lt h.constants.fits.mem

theorem slot_ne_global (s : GlobalState) (i : Nat) (hi : i ≤ 70) (id : BlockId)
    (h : id.id < s.alloc.nextFreeBlock) : (slot s i).id ≠ id := by
  intro heq
  have := congrArg BlockId.id heq
  rw [slot_id s i hi] at this
  omega

/-- The public compression globals are recovered from an erased private
frame, allowing exactly the designated cache change. -/
theorem CompressionReady.of_cacheFrame (g : CompressionGlobals)
    (before after : GlobalState) (mark : Nat)
    (hframe : CacheFrame g before.mem (after.mem.eraseFrom mark))
    (hr : CompressionReady g before) : CompressionReady g after := by
  obtain ⟨byte, hb, hc⟩ := hframe.cache
  exact ⟨present_of_frame _ _ _ _ _ rfl
      (hframe.present _ _ hr.separate hr.constants),
    ⟨byte, hb, present_of_frame _ _ _ _ _ rfl hc⟩, hr.separate⟩

/-- A cold cache update cannot modify either scalar Montgomery constant when
its concrete global allocation identities satisfy the explicit separation. -/
theorem scalarReady_of_cacheFrame (g : CompressionGlobals) (r : ScalarWide.Globals)
    (before after : GlobalState) (out : Pointer) (mark : Nat)
    (hframe : CacheFrame g before.mem (after.mem.eraseFrom mark))
    (hr : ScalarWide.Ready r before out)
    (hR : r.address0.id ≠ g.cache) (hRR : r.address1.id ≠ g.cache) :
    ScalarWide.Ready r after out := by
  obtain ⟨h0, h1, hR0, hR1, hsep, ho0, ho1⟩ := hr
  exact ⟨h0, h1, present_of_frame _ _ _ _ _ rfl (hframe.present _ _ hR hR0),
    present_of_frame _ _ _ _ _ rfl (hframe.present _ _ hRR hR1), hsep, ho0, ho1⟩

theorem CacheFrame.internal_store (h : CacheFrame g base (m.eraseFrom mark))
    (ptr : Pointer) (value : BitVec w) (hi : mark ≤ ptr.id.id) :
    CacheFrame g base ((m.storeAt ptr value).eraseFrom mark) := by
  rw [MemoryState.eraseFrom_storeAt, MemoryState.storeAt_eraseFrom_of_le hi]
  exact h

theorem LocalsLive.cacheEffect (h : LocalsLive entry before.mem)
    (he : CacheOutputEffect g before after dst value)
    (hc : g.cache.id < entry.alloc.nextFreeBlock) : LocalsLive entry after.mem := by
  constructor
  · exact he.smallRange _ _ (slot_ne_global entry 0 (by decide) _ hc) h.block0
  · exact he.smallRange _ _ (slot_ne_global entry 1 (by decide) _ hc) h.block1
  · exact he.smallRange _ _ (slot_ne_global entry 2 (by decide) _ hc) h.block2
  · exact he.smallRange _ _ (slot_ne_global entry 3 (by decide) _ hc) h.buffer
  · exact he.smallRange _ _ (slot_ne_global entry 4 (by decide) _ hc) h.digest
  · exact he.smallRange _ _ (slot_ne_global entry 5 (by decide) _ hc) h.context
  · intro i
    exact he.smallRange _ _ (slot_ne_global entry (i.val + 6) (by omega) _ hc) (h.scratch i)

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
