import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchContract
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.Avx2ExecutionCountOne
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchInitializer
import SSA.Projects.Agave.Ed25519.Proof.Avx2Cache.Contract
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdLinked

/-! Link the actual imported compression dispatcher, AVX2 backend, CPU-cache
initializer, SHA finalizer and wide reducer. Count-one finalization is proved.
Bulk challenge compression has exactly the explicit AVX2 call equation below
left to discharge, in addition to the external hardware-instruction laws. -/
namespace Agave.Ed25519.SHA512.Execution.Dispatch.Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open Agave.Ed25519.Verifier.Execution.Dalek.Avx2Cache.Instructions
open ScalarFull ScalarBulk

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Each external compressor symbol is linked to its imported RIR function. -/
noncomputable def linkedPrimitives (hardware : HardwareInstructions)
    (g : CompressionGlobals) : Agave.Ed25519.SHA512.Execution.Dispatch.Primitives where
  initializeAvx2Cache := (shaInitializer hardware.link g.cachePtr).call
  avx2Compress := (Avx2.program ⟨g.constantsPtr⟩).call

noncomputable def linkedCall (hardware : HardwareInstructions) (g : CompressionGlobals) :
    Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []) :=
  (program (linkedPrimitives hardware g) (readyGlobals g)).call

/-- No whole-initializer assumption survives: the actual imported initializer
is discharged from its CPUID, gated XGETBV and monotonic-store instruction laws. -/
theorem linked_initializer (hardware : HardwareInstructions)
    (laws : InstructionContracts hardware) (g : CompressionGlobals) :
    CacheInitializer g (linkedPrimitives hardware g).initializeAvx2Cache := by
  intro state hwf hr _
  obtain ⟨enabled, hcall⟩ := initializer_call_of_instructions hardware laws g.cachePtr
    state hwf hr.cache_range
  refine ⟨enabled, ?_⟩
  cases enabled <;>
    simpa [linkedPrimitives, shaInitializer_eq, initializedState,
      Dalek.Avx2Cache.stored, Dalek.choiceByte] using hcall

/-- Both concrete backend paths, cold or warm, are proved at count one. -/
theorem linked_oneBlock_contract (hardware : HardwareInstructions)
    (laws : InstructionContracts hardware) (g : CompressionGlobals) :
    OneBlockCompressContractUnder g (linkedCall hardware g) Spec.compression :=
  dispatch_oneBlock_of_avx2 (linkedPrimitives hardware g) g
    (linked_initializer hardware laws g) (Avx2.count_one_contract g)

/-- Actual SHA finalization and wide reduction need only count-one compression,
so this theorem has no remaining compression execution premise. -/
theorem linked_finalizer_contract (hardware : HardwareInstructions)
    (laws : InstructionContracts hardware) (g : CompressionGlobals) (r : ScalarWide.Globals) :
    ScalarFromSha512ColdContract g r
      (coldLinkedPrimitives r (linkedCall hardware g)).scalarFromSha512 Spec.compression :=
  linked_finalizer_cold g r Spec.compression (linkedCall hardware g)
    (linked_oneBlock_contract hardware laws g) (ScalarWide.execution_obligation r)

/-- Exact remaining backend equation for arbitrary live ABI counts, including
zero. This is solely a direct AVX2 execution boundary; it contains no dispatch,
finalizer, challenge, digest, or caller-correctness conclusion. -/
def Avx2BulkCallEquation (g : CompressionGlobals) : Prop :=
  ∀ (state : GlobalState) (chain data : Pointer) (count : BitVec 64),
    state.WF → SmallRange state.mem chain 64 →
    SmallRange state.mem data (128 * count.toNat) →
    Avx2.PairConstants state.mem g.constantsPtr → chain.id ≠ g.constants →
    (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))) →
    (Avx2.program ⟨g.constantsPtr⟩).call (bulkArgs chain data count) state =
      .value (.nil, {
        alloc := ⟨state.alloc.nextFreeBlock + 3⟩,
        mem := state.mem.storeAt chain (Spec.compression.run (state.mem.readAt chain 512)
          (readBytes state.mem data (128 * count.toNat))) })

/-- Existing K64 readiness and provenance discharge every global/frame premise
needed to turn the exact direct-backend call into the caller-facing contract. -/
theorem avx2_contract_of_call_equation (g : CompressionGlobals)
    (hbulk : Avx2BulkCallEquation g) :
    CompressContractUnder g (Avx2.program ⟨g.constantsPtr⟩).call Spec.compression := by
  intro state chain data count hwf hr hc hd hdis
  let value := Spec.compression.run (state.mem.readAt chain 512)
    (readBytes state.mem data (128 * count.toNat))
  let after : GlobalState := {
    alloc := ⟨state.alloc.nextFreeBlock + 3⟩,
    mem := state.mem.storeAt chain value }
  have hcall := hbulk state chain data count hwf hc hd
    (Avx2.pairConstants_of_ready g state hr.globals) hr.chainConstants hdis
  obtain ⟨old, ho, hp⟩ := hr.globals.cache
  have he : CompressionStoreEffect g state after chain value := by
    refine ⟨old, old, ho, hp, CacheTransition.refl old, ?_, ?_⟩
    · rw [cache_store_same g state.mem old hp]
    · dsimp [after]
      omega
  exact ⟨after, hcall, he, he.ready hr.globals hr.chainConstants hr.chainCache⟩

/-- Exact replacement for `CompressContractUnder scg compressCall compression`
at the linked finalization/challenge boundary. Only the direct AVX2 bulk
execution equation is still required from the compression proof. -/
theorem linked_compress_contract (hardware : HardwareInstructions)
    (laws : InstructionContracts hardware) (g : CompressionGlobals)
    (hbulk : Avx2BulkCallEquation g) :
    CompressContractUnder g (linkedCall hardware g) Spec.compression :=
  dispatch_contract_of_avx2 (linkedPrimitives hardware g) g
    (linked_initializer hardware laws g) (avx2_contract_of_call_equation g hbulk)

/-- The same link accepts a directly proved contextual AVX2 contract. -/
theorem linked_compress_contract_of_avx2 (hardware : HardwareInstructions)
    (laws : InstructionContracts hardware) (g : CompressionGlobals)
    (havx : CompressContractUnder g (Avx2.program ⟨g.constantsPtr⟩).call Spec.compression) :
    CompressContractUnder g (linkedCall hardware g) Spec.compression :=
  dispatch_contract_of_avx2 (linkedPrimitives hardware g) g
    (linked_initializer hardware laws g) havx

end Agave.Ed25519.SHA512.Execution.Dispatch.Finalization
