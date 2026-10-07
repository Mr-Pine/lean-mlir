import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ContextContract
import SSA.Projects.RIR.Run.Call
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ChallengeExecutionMemory

/-! Readiness and whole-memory adapters for the dispatcher's one-byte cache
initialization and final call-frame erasure. -/
namespace Agave.Ed25519.SHA512.Execution.Dispatch.Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization

set_option maxRecDepth 100000
set_option maxHeartbeats 1500000

def initializedState (g : CompressionGlobals) (s : GlobalState) (enabled : Bool) : GlobalState :=
  {s with mem := s.mem.storeAt g.cachePtr (if enabled then 1#8 else 0#8)}

theorem initialized_ready (g : CompressionGlobals) (s : GlobalState) (enabled : Bool)
    (h : CompressionReady g s) : CompressionReady g (initializedState g s enabled) := by
  obtain ⟨old, _, hp⟩ := h.cache
  refine ⟨h.constants.storeAt h.separate, ⟨_, ?_, cache_present_store g s.mem old _ hp⟩,
    h.separate⟩
  cases enabled <;> simp [CacheByteLegal]

theorem initialized_warm (g : CompressionGlobals) (s : GlobalState) (enabled : Bool)
    (h : CompressionReady g s) : CacheWarm g (initializedState g s enabled) := by
  obtain ⟨old, _, hp⟩ := h.cache
  refine ⟨_, ?_, cache_present_store g s.mem old _ hp⟩
  cases enabled <;> simp

theorem initialized_callReady (g : CompressionGlobals) (s : GlobalState) (enabled : Bool)
    (chain data : Pointer) (h : CompressionCallReady g s chain data) :
    CompressionCallReady g (initializedState g s enabled) chain data :=
  ⟨initialized_ready g s enabled h.globals, h.chainConstants, h.chainCache, h.dataCache⟩

theorem initialized_cache_read (g : CompressionGlobals) (s : GlobalState) (enabled : Bool)
    (h : CompressionReady g s) :
    (initializedState g s enabled).mem.readAt g.cachePtr 8 =
      (if enabled then 1#8 else 0#8) :=
  MemoryState.readAt_storeAt_self h.cache_range.fits _

theorem initialized_chain_read (g : CompressionGlobals) (s : GlobalState) (enabled : Bool)
    (chain : Pointer) (h : chain.id ≠ g.cache) :
    (initializedState g s enabled).mem.readAt chain 512 = s.mem.readAt chain 512 :=
  MemoryState.readAt_storeAt_disjoint (Range.disjoint_of_id_ne h.symm) _

theorem initialized_data_read (g : CompressionGlobals) (s : GlobalState) (enabled : Bool)
    (data : Pointer) (n : Nat) (h : data.id ≠ g.cache) (hl : SmallRange s.mem data n) :
    readBytes (initializedState g s enabled).mem data n = readBytes s.mem data n := by
  exact readBytes_storeAt_disjoint _ _ _ _ _ hl (Range.disjoint_of_id_ne h.symm)

theorem public_store_effect (g : CompressionGlobals) (s : GlobalState)
    (chain : Pointer) (value : BitVec 512) (hr : CompressionReady g s) :
    CompressionStoreEffect g s {s with mem := s.mem.storeAt chain value} chain value := by
  obtain ⟨old, ho, hp⟩ := hr.cache
  refine ⟨old, old, ho, hp, CacheTransition.refl old, ?_, Nat.le_refl _⟩
  rw [cache_store_same g s.mem old hp]

/-- The warm backend's effect composes with the exact preceding cold store. -/
theorem initialized_effect (g : CompressionGlobals) (before after : GlobalState)
    (enabled : Bool) (chain : Pointer) (value : BitVec 512)
    (hr : CompressionReady g before) (hcold : before.mem.readAt g.cachePtr 8 = 255#8)
    (he : CompressionStoreEffect g (initializedState g before enabled) after chain value) :
    CompressionStoreEffect g before after chain value := by
  obtain ⟨old, ho, hp⟩ := hr.cache
  have hold : old = 255#8 := hp.readAt.symm.trans hcold
  subst old
  have hs := he.to_storeEffect (initialized_warm g before enabled hr)
  refine ⟨255, (if enabled then 1 else 0), ho, hp, Or.inr ⟨rfl, ?_⟩, hs.1, hs.2⟩
  cases enabled <;> simp

/-- The contextual memory effect already contains no allocations created by
this call. Erasing the dispatcher's call frame therefore changes no byte. -/
theorem effect_erase (g : CompressionGlobals) (before after : GlobalState)
    (chain : Pointer) (value : BitVec 512) (hwf : before.WF)
    (he : CompressionStoreEffect g before after chain value) :
    after.mem.eraseFrom before.alloc.nextFreeBlock = after.mem := by
  obtain ⟨_, new, _, _, _, hm, _⟩ := he
  rw [hm]
  exact (hwf.storeAt (p := g.cachePtr) (x := new)).storeAt.eraseFrom

theorem call_of_run_effect (f : Func) (args : Vals f.Γ.args) (g : CompressionGlobals)
    (before after : GlobalState) (chain : Pointer) (value : BitVec 512)
    (result : Vals f.tRets)
    (hwf : before.WF) (he : CompressionStoreEffect g before after chain value)
    (h : f.run args before = .value (result, after)) :
    f.call args before = .value (result, after) := by
  rw [Func.call_of_run h, effect_erase g before after chain value hwf he]

end Agave.Ed25519.SHA512.Execution.Dispatch.Finalization
