import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.InitializerData
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Effects

/-!
Link the independently extracted LLVM K64 bytes and original cold-cache
initializer to the compression contracts. LLVM constant data is loaded before
execution; there is no initializer function to assume or execute. `install`
provides an explicit RIR loader construction with no readiness hypothesis.
The imported challenge IV is included and preserved through compression calls.
-/
namespace Agave.Ed25519.Verifier.Execution.SHA512Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.InitializerData
open Challenge

set_option maxRecDepth 10000
set_option maxHeartbeats 0

/-- Every byte of both imported compiler K64 globals agrees with the separate
FIPS round table, in native little-endian address order. -/
theorem extracted_k64_eq : k64Bytes = k64Memory.bytes := by
  change k64Bytes = BitVec.packLanes (we := 64) (n := 80) Agave.Ed25519.SHA512.Spec.constants
  decide +kernel

/-- Exact source initializer data, including the SHA caller's independently
imported IV. A loader binds these addresses once before calls begin. -/
structure ShaSourceGlobals where
  compression : CompressionGlobals
  iv : BlockId

def ShaSourceGlobals.ivPtr (g : ShaSourceGlobals) : Pointer := ⟨g.iv, 0⟩

structure ShaSourceReady (g : ShaSourceGlobals) (s : GlobalState) : Prop where
  compression : CompressionReady g.compression s
  iv : sha512InitialState.Present g.iv s.mem
  ivCache : g.iv ≠ g.compression.cache

/-- The source data entails the abstract memory contract: K64's numerical
contents and the cache sentinel are proved, rather than loader assumptions. -/
theorem compressionReady_of_source_initializers (g : CompressionGlobals) (s : GlobalState)
    (hk : k64Global.Present g.constants s.mem)
    (hc : coldCacheGlobal.Present g.cache s.mem)
    (hsep : g.constants ≠ g.cache) : CompressionReady g s := by
  refine ⟨?_, ⟨255, Or.inr (Or.inr rfl), hc⟩, hsep⟩
  change s.mem[g.constants]? = some ⟨640, k64Memory.bytes⟩
  rw [← extracted_k64_eq]
  exact hk

/-- Installation leaves all already allocated globals intact. -/
private theorem present_install_other (g old : ByteGlobal) (s : GlobalState) (id : BlockId)
    (h : old.Present id s.mem) (hne : id ≠ ⟨s.alloc.nextFreeBlock⟩) :
    old.Present id (g.install s).mem := by
  simpa [ByteGlobal.Present, ByteGlobal.install, MemoryState.getElem?_eq,
    Std.ExtHashMap.getElem?_insert, Ne.symm hne] using h

/-- A concrete pre-execution loader for precisely these three globals. -/
def installShaSource (s : GlobalState) : GlobalState :=
  sha512InitialState.install (coldCacheGlobal.install (k64Global.install s))

def installedShaGlobals (s : GlobalState) : ShaSourceGlobals :=
  ⟨⟨⟨s.alloc.nextFreeBlock⟩, ⟨s.alloc.nextFreeBlock + 1⟩⟩,
    ⟨s.alloc.nextFreeBlock + 2⟩⟩

/-- The exact pinned globals can be loaded into any well-formed caller state. -/
theorem installShaSource_wf (s : GlobalState) (hwf : s.WF) :
    (installShaSource s).WF :=
  sha512InitialState.wf_install (coldCacheGlobal.wf_install (k64Global.wf_install hwf))

/-- Concrete initialization discharges every K64/cache/IV readiness fact.
Only caller memory well-formedness is needed by the separate WF theorem. -/
theorem installShaSource_ready (s : GlobalState) :
    ShaSourceReady (installedShaGlobals s) (installShaSource s) := by
  have hk := k64Global.present_install s
  have hc := coldCacheGlobal.present_install (k64Global.install s)
  have hi := sha512InitialState.present_install (coldCacheGlobal.install (k64Global.install s))
  have hk' := present_install_other coldCacheGlobal k64Global (k64Global.install s)
    ⟨s.alloc.nextFreeBlock⟩ hk (by simp [ByteGlobal.install])
  have hk'' := present_install_other sha512InitialState k64Global
    (coldCacheGlobal.install (k64Global.install s)) ⟨s.alloc.nextFreeBlock⟩ hk'
    (by simp [ByteGlobal.install]; omega)
  have hc' := present_install_other sha512InitialState coldCacheGlobal
    (coldCacheGlobal.install (k64Global.install s)) ⟨s.alloc.nextFreeBlock + 1⟩ hc
    (by simp [ByteGlobal.install])
  refine ⟨compressionReady_of_source_initializers _ _ hk'' hc' ?_, hi, ?_⟩ <;>
    simp [installedShaGlobals]

/-- The initial dispatch sees the original compiler sentinel exactly. -/
theorem installShaSource_cold_cache (s : GlobalState) :
    (cacheMemory 255).Present (installedShaGlobals s).compression.cache
      (installShaSource s).mem := by
  have hc := coldCacheGlobal.present_install (k64Global.install s)
  exact present_install_other sha512InitialState coldCacheGlobal
    (coldCacheGlobal.install (k64Global.install s)) ⟨s.alloc.nextFreeBlock + 1⟩ hc
    (by simp [ByteGlobal.install])

/-- The IV is the independent standard IV, not just an opaque loaded constant. -/
theorem ShaSourceReady.iv_standard (h : ShaSourceReady g s) :
    Agave.Ed25519.SHA512.Spec.unpack (s.mem.readAt g.ivPtr 512) =
      Agave.Ed25519.SHA512.Spec.initial := by
  have hr : s.mem.readAt g.ivPtr 512 = initialWords := h.iv.readAt
  rw [hr]
  exact Agave.Ed25519.SHA512.Spec.extracted_initial_eq

/-- Ready-to-use entry premises for the actual imported challenge caller. -/
theorem ShaSourceReady.iv_entry (h : ShaSourceReady g s) :
    SmallRange s.mem g.ivPtr 64 ∧ s.mem.readAt g.ivPtr 512 = initialWords := by
  refine ⟨⟨⟨64, sha512InitialState.bytes⟩, h.iv, by decide, ?_⟩, h.iv.readAt⟩
  simp [ShaSourceGlobals.ivPtr]

/-- Fresh caller scratch automatically supplies the compression call's
provenance inequalities once source initialization has run. -/
theorem ShaSourceReady.fresh_call (h : ShaSourceReady g s) (hwf : s.WF)
    (chain data : Pointer)
    (hchain : s.alloc.nextFreeBlock ≤ chain.id.id)
    (hdata : s.alloc.nextFreeBlock ≤ data.id.id) :
    CompressionCallReady g.compression s chain data := by
  obtain ⟨hkc, hbc⟩ := h.compression.separate_fresh hwf chain hchain
  obtain ⟨_, hbd⟩ := h.compression.separate_fresh hwf data hdata
  exact ⟨h.compression, hkc, hbc, hbd⟩

/-- An imported cold or warm compressor's declared effect preserves all
source globals. The cache may transition, while K64 and IV remain exact. -/
theorem ShaSourceReady.after_call (h : ShaSourceReady g before)
    (he : CacheFramedStoreEffect g.compression before after dst (value : BitVec w))
    (hkc : dst.id ≠ g.compression.constants) (hbc : dst.id ≠ g.compression.cache)
    (hiv : dst.id ≠ g.iv) : ShaSourceReady g after := by
  refine ⟨he.ready h.compression hkc hbc, ?_, h.ivCache⟩
  obtain ⟨_, _, _, _, _, hm, _⟩ := he
  rw [hm]
  exact (h.iv.storeAt h.ivCache).storeAt hiv.symm

/-- Private-frame calls keep the same source readiness for later invocations. -/
theorem ShaSourceReady.of_frame (h : ShaSourceReady g before) (mark : Nat)
    (hframe : after.mem.eraseFrom mark = before.mem) : ShaSourceReady g after :=
  ⟨CompressionReady.of_frame _ _ _ _ hframe h.compression,
    present_of_frame _ _ _ _ _ hframe h.iv, h.ivCache⟩

end Agave.Ed25519.Verifier.Execution.SHA512Finalization
