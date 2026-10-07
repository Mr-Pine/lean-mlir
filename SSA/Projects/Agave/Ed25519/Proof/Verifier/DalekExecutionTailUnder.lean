import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContractsUnder

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR

theorem backend_tail_of_contracts_under {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (serialReady avx2Ready : BackendReadyPredicate)
    (hserial : DoubleBaseContractUnder serialReady p.serialDoubleBase layout doubleBase)
    (havx2 : DoubleBaseContractUnder avx2Ready p.avx2DoubleBase layout doubleBase)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (useVector : Bool) (q : TailPointers) (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hready : BackendsReady serialReady avx2Ready q state)
    (hregs : TailRegisters q E) (hmem : TailMemory q state layout h scalar a r) :
    ∃ after, (program p g).runFrom E (if useVector then 9 else 8) state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  have hc : DoubleBaseContractUnder (if useVector then avx2Ready else serialReady)
      (if useVector then p.avx2DoubleBase else p.serialDoubleBase) layout doubleBase := by
    cases useVector <;> assumption
  obtain ⟨middle, encoded, hcall, hframe, hresult, hencoded⟩ := hc q.output q.challenge q.point q.scalar
    state h scalar a hmem.wellFormed
    (by cases useVector; exact hready.1; exact hready.2) hmem.output hmem.challenge hmem.point hmem.scalar
    hmem.outputChallenge hmem.outputPoint hmem.outputScalar
  have hr : ReadBytes middle q.signature 32 r :=
    ⟨hframe.live q.signature 32 hmem.signature.1,
      (hframe.read q.signature 256 hmem.signatureOutput).trans hmem.signature.2⟩
  obtain ⟨after, hsuffix⟩ := compression_tail_of_contracts p g layout compress
    hcompress hcompare E middle q.compressed q.output q.signature
    (doubleBase h a scalar) r encoded hregs.compressed hregs.output hregs.signature
    hregs.length hregs.zero hregs.ok hregs.error hframe.wellFormed
    (hframe.live q.compressed 32 hmem.compressed) hresult hencoded hr
    hmem.compressedOutput hmem.signatureCompressed
  refine ⟨after, ?_⟩
  cases useVector with
  | false =>
    change (program p g).runFrom E 8 state = _
    rw [serial_block p g E state middle q.output q.challenge q.point q.scalar
      hregs.output hregs.challenge hregs.point hregs.scalar hcall]
    exact hsuffix
  | true =>
    change (program p g).runFrom E 9 state = _
    rw [avx2_block p g E state middle q.output q.challenge q.point q.scalar
      hregs.output hregs.challenge hregs.point hregs.scalar hcall]
    exact hsuffix


theorem dispatch_tail_of_contracts_under {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (serialReady avx2Ready : BackendReadyPredicate)
    (hserial : DoubleBaseContractUnder serialReady p.serialDoubleBase layout doubleBase)
    (havx2 : DoubleBaseContractUnder avx2Ready p.avx2DoubleBase layout doubleBase)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32) (cacheValue : BitVec 8)
    (hready : BackendsReady serialReady avx2Ready q state)
    (hregs : TailRegisters q E) (hmem : TailMemory q state layout h scalar a r)
    (hcacheFits : Fits state.mem q.cache 8)
    (hcache : state.mem.readAt q.cache 8 = cacheValue) :
    ∃ after, (program p g).runFrom E 7 state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  rw [dispatch_block p g E state q.cache cacheValue hregs.cache hregs.one hcacheFits hcache]
  simpa using
    backend_tail_of_contracts_under p g layout doubleBase compress serialReady avx2Ready hserial havx2 hcompress hcompare
      (decide (cacheValue = 1)) q _ state h scalar a r hready (TailRegisters.dispatch q E hregs cacheValue) hmem


theorem initialized_tail_of_contracts_under {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (serialReady avx2Ready : BackendReadyPredicate)
    (hserial : DoubleBaseContractUnder serialReady p.serialDoubleBase layout doubleBase)
    (havx2 : DoubleBaseContractUnder avx2Ready p.avx2DoubleBase layout doubleBase)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (hinit : CacheContract p.initializeAvx2Cache q.cache)
    (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hready : ∀ after returned, p.initializeAvx2Cache .nil state =
      .value (.cons (.value returned) .nil, after) → OutputFrame state after q.cache 1 → BackendsReady serialReady avx2Ready q after)
    (hregs : TailRegisters q E) (hmem : TailMemory q state layout h scalar a r)
    (hcache : ReadBytes state q.cache 1 255) (hd : CacheDisjoint q) :
    ∃ after, (program p g).runFrom E 6 state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  obtain ⟨middle, returned, hcall, hframe⟩ :=
    hinit state hmem.wellFormed hcache
  rw [initialize_cache_block p g E state middle returned hcall]
  exact dispatch_tail_of_contracts_under p g layout doubleBase compress serialReady avx2Ready
    hserial havx2 hcompress hcompare q _ middle h scalar a r
    (middle.mem.readAt q.cache 8) (hready middle returned hcall hframe) (TailRegisters.initialize q E hregs returned)
    (TailMemory.cache_frame q state middle layout h scalar a r hmem hframe hd)
    (hframe.live q.cache 1 hcache.1).fits rfl


end Agave.Ed25519.Verifier.Execution.Dalek
