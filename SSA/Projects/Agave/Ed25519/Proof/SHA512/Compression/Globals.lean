import SSA.Projects.Agave.Ed25519.Proof.SHA512.CompressionSpec
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.Ready

/-! Explicit K64/cache allocation readiness and its frame-preservation facts.
No backend execution equation is assumed by these memory invariants. -/

namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Bridge.Challenge
open Challenge

/-- Specification of the native little-endian K64 allocation. The actual
compiler global must be shown equal to these bytes after extraction. -/
def k64Memory : ByteGlobal :=
  ⟨"SHA512.K64.specification", 640,
    BitVec.packLanes (we := 64) (n := 80) Agave.Ed25519.SHA512.Spec.constants, 8, by decide⟩

def cacheMemory (value : BitVec 8) : ByteGlobal :=
  ⟨"SHA512.CPUID.cache.specification", 1, value, 1, by decide⟩

structure CompressionGlobals where
  constants : BlockId
  cache : BlockId

def CompressionGlobals.constantsPtr (g : CompressionGlobals) : Pointer := ⟨g.constants, 0⟩
def CompressionGlobals.cachePtr (g : CompressionGlobals) : Pointer := ⟨g.cache, 0⟩

/-- cpufeatures' initial sentinel or either cached Boolean result. No
relationship between the result and actual hardware capabilities is assumed. -/
def CacheByteLegal (value : BitVec 8) : Prop := value = 0 ∨ value = 1 ∨ value = 255

structure CompressionReady (g : CompressionGlobals) (state : GlobalState) : Prop where
  constants : k64Memory.Present g.constants state.mem
  cache : ∃ value, CacheByteLegal value ∧ (cacheMemory value).Present g.cache state.mem
  separate : g.constants ≠ g.cache

/-- These provenance inequalities follow for the finalizer's fresh context
and block buffer. They exclude caller stores into immutable K64 and exclude
an input alias of the cache that the dispatcher may initialize. -/
structure CompressionCallReady (g : CompressionGlobals) (state : GlobalState)
    (chain data : Pointer) : Prop where
  «globals» : CompressionReady g state
  chainConstants : chain.id ≠ g.constants
  chainCache : chain.id ≠ g.cache
  dataCache : data.id ≠ g.cache

theorem CompressionReady.constants_range (h : CompressionReady g state) :
    SmallRange state.mem g.constantsPtr 640 := by
  refine ⟨⟨640, k64Memory.bytes⟩, h.constants, by decide, ?_⟩
  simp [CompressionGlobals.constantsPtr]

theorem CompressionReady.cache_range (h : CompressionReady g state) :
    SmallRange state.mem g.cachePtr 1 := by
  obtain ⟨value, _, hp⟩ := h.cache
  refine ⟨⟨1, value⟩, hp, by norm_num, ?_⟩
  simp [CompressionGlobals.cachePtr]

/-- The concrete table/cache allocations predate any fresh private frame. -/
theorem CompressionReady.globals_before (h : CompressionReady g state) (hwf : state.WF) :
    g.constants.id < state.alloc.nextFreeBlock ∧ g.cache.id < state.alloc.nextFreeBlock := by
  exact ⟨hwf.lt h.constants_range.fits.mem, hwf.lt h.cache_range.fits.mem⟩

theorem CompressionReady.separate_fresh (h : CompressionReady g state) (hwf : state.WF)
    (p : Pointer) (hp : state.alloc.nextFreeBlock ≤ p.id.id) :
    p.id ≠ g.constants ∧ p.id ≠ g.cache := by
  obtain ⟨hc, hb⟩ := h.globals_before hwf
  constructor
  · intro heq
    have := congrArg BlockId.id heq
    omega
  · intro heq
    have := congrArg BlockId.id heq
    omega

/-- Arbitrary finalizer scratch or output writes with different allocation
identities preserve both the immutable constants and the exact cache byte. -/
theorem CompressionReady.storeAt (g : CompressionGlobals) (s : GlobalState)
    (p : Pointer) (v : BitVec w) (h : CompressionReady g s)
    (hc : p.id ≠ g.constants) (hb : p.id ≠ g.cache) :
    CompressionReady g { s with mem := s.mem.storeAt p v } := by
  obtain ⟨value, hv, hp⟩ := h.cache
  exact ⟨h.constants.storeAt hc.symm, ⟨value, hv, hp.storeAt hb.symm⟩, h.separate⟩

theorem CompressionReady.alloca (g : CompressionGlobals) (s : GlobalState)
    (bytes : Nat) (h : CompressionReady g s) (hwf : s.WF) :
    CompressionReady g (s.alloca bytes) := by
  obtain ⟨value, hv, hp⟩ := h.cache
  exact ⟨h.constants.alloca hwf, ⟨value, hv, hp.alloca hwf⟩, h.separate⟩

/-- Reuse the finalizer's existing erasure equation for an arbitrary private
frame; every original global allocation and its bytes are preserved exactly. -/
theorem CompressionReady.of_frame (g : CompressionGlobals) (before after : GlobalState)
    (mark : Nat) (hframe : after.mem.eraseFrom mark = before.mem)
    (h : CompressionReady g before) : CompressionReady g after := by
  obtain ⟨value, hv, hp⟩ := h.cache
  exact ⟨present_of_frame _ _ _ _ _ hframe h.constants,
    ⟨value, hv, present_of_frame _ _ _ _ _ hframe hp⟩, h.separate⟩

theorem CompressionCallReady.of_frame (g : CompressionGlobals)
    (before after : GlobalState) (chain data : Pointer) (mark : Nat)
    (hframe : after.mem.eraseFrom mark = before.mem)
    (h : CompressionCallReady g before chain data) :
    CompressionCallReady g after chain data := by
  exact ⟨CompressionReady.of_frame g before after mark hframe h.globals,
    h.chainConstants, h.chainCache, h.dataCache⟩

/-- After private-frame work, the public output write also preserves global
readiness whenever the caller supplied a separate output allocation. -/
theorem CompressionReady.frame_then_output (g : CompressionGlobals)
    (before after : GlobalState) (mark : Nat) (output : Pointer) (value : BitVec w)
    (hframe : after.mem.eraseFrom mark = before.mem) (h : CompressionReady g before)
    (hc : output.id ≠ g.constants) (hb : output.id ≠ g.cache) :
    CompressionReady g { after with mem := after.mem.storeAt output value } :=
  CompressionReady.storeAt g after output value
    (CompressionReady.of_frame g before after mark hframe h) hc hb

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
