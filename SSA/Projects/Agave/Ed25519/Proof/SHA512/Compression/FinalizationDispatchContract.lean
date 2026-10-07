import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchMemory
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchScalar

/-! Exact composition of both imported dispatch branches, including a cold
initializer and the real call-frame cleanup. The scalar branch is discharged;
the remaining compression premise concerns only the AVX2 backend. -/
namespace Agave.Ed25519.SHA512.Execution.Dispatch.Finalization

open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.Verifier.Execution.Challenge
open Agave.Ed25519.Verifier.Execution.SHA512Finalization
open ScalarFull ScalarBulk

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-- A single fixed ABI count, used to specialize the proved count-one backend
without pretending it implements arbitrary-count compression. -/
def BackendContractAt (g : CompressionGlobals)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals [])) (count : BitVec 64) : Prop :=
  ∀ (state : GlobalState) (chain data : Pointer),
    state.WF → CompressionCallReady g state chain data →
    SmallRange state.mem chain 64 → SmallRange state.mem data (128 * count.toNat) →
    (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))) →
    ∃ after,
      call (bulkArgs chain data count) state = .value (.nil, after) ∧
      CompressionStoreEffect g state after chain
        (Spec.compression.run (state.mem.readAt chain 512)
          (readBytes state.mem data (128 * count.toNat))) ∧ CompressionReady g after

/-- The cold initializer has one exact cache-byte store. The linked module
discharges this adapter from the imported instruction-level initializer proof. -/
def CacheInitializer (g : CompressionGlobals)
    (call : Vals [] → EffectM (Vals [.bv 1])) : Prop :=
  ∀ state : GlobalState, state.WF → CompressionReady g state →
    state.mem.readAt g.cachePtr 8 = 255#8 → ∃ enabled : Bool,
      call .nil state = .value (.cons (.value (BitVec.ofBool enabled)) .nil,
        initializedState g state enabled)

/-- Either selected suffix has the exact same contextual postcondition. -/
theorem selected_suffix (p : Primitives) (g : CompressionGlobals) (count : BitVec 64)
    (havx : BackendContractAt g p.avx2Compress count)
    (enabled : Bool) (E : Env program.Γ) (state : GlobalState) (chain data : Pointer)
    (hwf : state.WF) (hr : CompressionCallReady g state chain data)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))))
    (hconst : Constants E g.constantsPtr) (hzero : E.read (%2) = .value 0#64)
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value count) :
    ∃ after,
      (program p (readyGlobals g)).runFrom E (if enabled then 6 else 2) state =
        .value (.nil, after) ∧
      CompressionStoreEffect g state after chain
        (Spec.compression.run (state.mem.readAt chain 512)
          (readBytes state.mem data (128 * count.toNat))) ∧ CompressionReady g after := by
  cases enabled with
  | false =>
    have he := public_store_effect g state chain
      (Spec.compression.run (state.mem.readAt chain 512)
        (readBytes state.mem data (128 * count.toNat))) hr.globals
    exact ⟨bulkAfter state chain data count,
      scalar_suffix p (readyGlobals g) E state chain data count hc hd
        (constants_read g state hr.globals) hconst hzero hchain hdata hcount,
      he, he.ready hr.globals hr.chainConstants hr.chainCache⟩
  | true =>
    obtain ⟨after, hcall, he, hready⟩ := havx state chain data hwf hr hc hd hdis
    exact ⟨after, dispatch_avx2_runFrom p (readyGlobals g) E state after chain data count
      hchain hdata hcount hcall, he, hready⟩

/-- Full imported dispatcher run, with legal cold and warm cache states. -/
theorem dispatch_run_at (p : Primitives) (g : CompressionGlobals) (count : BitVec 64)
    (hinit : CacheInitializer g p.initializeAvx2Cache)
    (havx : BackendContractAt g p.avx2Compress count)
    (E : Env program.Γ) (state : GlobalState) (chain data : Pointer)
    (hwf : state.WF) (hr : CompressionCallReady g state chain data)
    (hc : SmallRange state.mem chain 64) (hd : SmallRange state.mem data (128 * count.toNat))
    (hdis : (Range.of chain 512).Disjoint (Range.of data (8 * (128 * count.toNat))))
    (hchain : E.read (%arg0) = .value chain)
    (hdata : E.read (%arg1) = .value data) (hcount : E.read (%arg2) = .value count) :
    ∃ after,
      (program p (readyGlobals g)).runFrom E 0 state = .value (.nil, after) ∧
      CompressionStoreEffect g state after chain
        (Spec.compression.run (state.mem.readAt chain 512)
          (readBytes state.mem data (128 * count.toNat))) ∧ CompressionReady g after := by
  obtain ⟨cache, hlegal, hp⟩ := hr.globals.cache
  rcases hlegal with h0 | h1 | h255
  · subst cache
    obtain ⟨after, hrun, he, hready⟩ := selected_suffix p g count havx false
      (dispatchEntryEnv E (readyGlobals g) 0) state chain data hwf hr hc hd hdis
      (dispatch_entry_constants E (readyGlobals g) 0)
      (dispatch_entry_zero E (readyGlobals g) 0)
      (by change E.args 0 = .value chain; exact hchain)
      (by change E.args 1 = .value data; exact hdata)
      (by change E.args 2 = .value count; exact hcount)
    refine ⟨after, ?_, he, hready⟩
    rw [dispatch_entry_runFrom p (readyGlobals g) E state 0
      hr.globals.constants_range hr.globals.cache_range hp.readAt]
    exact hrun
  · subst cache
    obtain ⟨after, hrun, he, hready⟩ := selected_suffix p g count havx true
      (dispatchEntryEnv E (readyGlobals g) 1) state chain data hwf hr hc hd hdis
      (dispatch_entry_constants E (readyGlobals g) 1)
      (dispatch_entry_zero E (readyGlobals g) 1)
      (by change E.args 0 = .value chain; exact hchain)
      (by change E.args 1 = .value data; exact hdata)
      (by change E.args 2 = .value count; exact hcount)
    refine ⟨after, ?_, he, hready⟩
    rw [dispatch_entry_runFrom p (readyGlobals g) E state 1
      hr.globals.constants_range hr.globals.cache_range hp.readAt]
    exact hrun
  · subst cache
    obtain ⟨enabled, hi⟩ := hinit state hwf hr.globals hp.readAt
    let Ei := (dispatchEntryEnv E (readyGlobals g) 255)[%174 := .value (BitVec.ofBool enabled)]
    have hconst : Constants Ei g.constantsPtr :=
      constants_before (dispatch_entry_constants E (readyGlobals g) 255)
        (Before.write (Before.refl _ _) _ _ (by decide))
    have hzero : Ei.read (%2) = .value 0#64 := by
      simpa [Ei, mlir_env] using dispatch_entry_zero E (readyGlobals g) 255
    obtain ⟨after, hrun, he, hready⟩ := selected_suffix p g count havx enabled Ei
      (initializedState g state enabled) chain data hwf.storeAt
      (initialized_callReady g state enabled chain data hr) (hc.storeAt _ _) (hd.storeAt _ _)
      hdis hconst hzero
      (by change E.args 0 = .value chain; exact hchain)
      (by change E.args 1 = .value data; exact hdata)
      (by change E.args 2 = .value count; exact hcount)
    rw [initialized_chain_read g state enabled chain hr.chainCache,
      initialized_data_read g state enabled data _ hr.dataCache hd] at he
    refine ⟨after, ?_, initialized_effect g state after enabled chain _ hr.globals hp.readAt he,
      hready⟩
    rw [dispatch_entry_runFrom p (readyGlobals g) E state 255
      hr.globals.constants_range hr.globals.cache_range hp.readAt]
    change (program p (readyGlobals g)).runFrom (dispatchEntryEnv E (readyGlobals g) 255) 1 state = _
    rw [dispatch_cold_runFrom p (readyGlobals g) _ state (initializedState g state enabled)
      enabled hi]
    exact hrun

/-- Exact dispatcher call with original frame erasure, at any fixed count
whose AVX2 backend contract is known. -/
theorem dispatch_contract_at (p : Primitives) (g : CompressionGlobals) (count : BitVec 64)
    (hinit : CacheInitializer g p.initializeAvx2Cache)
    (havx : BackendContractAt g p.avx2Compress count) :
    BackendContractAt g (program p (readyGlobals g)).call count := by
  intro state chain data hwf hr hc hd hdis
  obtain ⟨after, hrun, he, hready⟩ := dispatch_run_at p g count hinit havx
    (Env.init (bulkArgs chain data count).get) state chain data hwf hr hc hd hdis rfl rfl rfl
  have hrun' : (program p (readyGlobals g)).run (bulkArgs chain data count) state =
      .value (.nil, after) := by
    rw [Func.run_runFrom_eq]
    exact hrun
  exact ⟨after, call_of_run_effect (program p (readyGlobals g)) (bulkArgs chain data count) g state after chain _ .nil hwf he hrun', he, hready⟩

/-- The only remaining compression execution premise is the direct AVX2
arbitrary-count backend. Scalar, dispatch, cache framing and cleanup are proved. -/
theorem dispatch_contract_of_avx2 (p : Primitives) (g : CompressionGlobals)
    (hinit : CacheInitializer g p.initializeAvx2Cache)
    (havx : CompressContractUnder g p.avx2Compress Spec.compression) :
    CompressContractUnder g (program p (readyGlobals g)).call Spec.compression := by
  intro state chain data count
  exact dispatch_contract_at p g count hinit
    (fun state chain data => havx state chain data count) state chain data

/-- Count-one finalization uses the already-proved single-block backend. -/
theorem dispatch_oneBlock_of_avx2 (p : Primitives) (g : CompressionGlobals)
    (hinit : CacheInitializer g p.initializeAvx2Cache)
    (havx : OneBlockCompressContractUnder g p.avx2Compress Spec.compression) :
    OneBlockCompressContractUnder g (program p (readyGlobals g)).call Spec.compression := by
  have hat : BackendContractAt g p.avx2Compress 1#64 := by
    simpa [BackendContractAt, OneBlockCompressContractUnder, bulkArgs] using havx
  have h := dispatch_contract_at p g 1 hinit hat
  simpa [BackendContractAt, OneBlockCompressContractUnder, bulkArgs] using h

end Agave.Ed25519.SHA512.Execution.Dispatch.Finalization
