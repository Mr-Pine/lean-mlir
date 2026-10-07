import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionControl

/-!
The runtime-selected backend suffix of the exact imported verifier, composed
from single-call contracts. The initial state may contain arbitrary signature
R bytes; canonicality of R is not an input requirement. This module starts at
block 7, after the prefix has parsed S and prepared its stack copy.
-/

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

structure TailPointers where
  output : Pointer
  compressed : Pointer
  challenge : Pointer
  point : Pointer
  scalar : Pointer
  signature : Pointer
  cache : Pointer

structure TailRegisters (q : TailPointers) (E : Env program.Γ) : Prop where
  output : E.read (%25) = .value q.output
  compressed : E.read (%26) = .value q.compressed
  challenge : E.read (%32) = .value q.challenge
  point : E.read (%33) = .value q.point
  scalar : E.read (%27) = .value q.scalar
  signature : E.read (%arg1) = .value q.signature
  cache : E.read (%18) = .value q.cache
  length : E.read (%1) = .value (32 : BitVec 64)
  zero : E.read (%19) = .value (0 : BitVec 32)
  one : E.read (%14) = .value (1 : BitVec 8)
  ok : E.read (%13) = .value (255 : BitVec 8)
  error : E.read (%8) = .value (2 : BitVec 8)

/-- Only live-range, byte-layout, and caller-owned output disjointness facts.
The signature bytes themselves have no validity restriction. -/
structure TailMemory (q : TailPointers) (state : GlobalState)
    (layout : Layout Point Scalar Result) (h scalar : Scalar) (a : Point) (r : Bytes32) : Prop where
  wellFormed : state.WF
  output : SmallRange state.mem q.output 160
  compressed : SmallRange state.mem q.compressed 32
  challenge : ReadBytes state q.challenge 32 (layout.scalar h)
  point : ReadBytes state q.point 160 (layout.point a)
  scalar : ReadBytes state q.scalar 32 (layout.scalar scalar)
  signature : ReadBytes state q.signature 32 r
  outputChallenge : (Range.of q.output 1280).Disjoint (Range.of q.challenge 256)
  outputPoint : (Range.of q.output 1280).Disjoint (Range.of q.point 1280)
  outputScalar : (Range.of q.output 1280).Disjoint (Range.of q.scalar 256)
  signatureOutput : (Range.of q.signature 256).Disjoint (Range.of q.output 1280)
  compressedOutput : (Range.of q.compressed 256).Disjoint (Range.of q.output 1280)
  signatureCompressed : (Range.of q.signature 256).Disjoint (Range.of q.compressed 256)

/-- Both actual call sites, through actual compression/comparison and cleanup,
implement the same compressed double-base observation. -/
theorem backend_tail_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (hserial : DoubleBaseContract p.serialDoubleBase layout doubleBase)
    (havx2 : DoubleBaseContract p.avx2DoubleBase layout doubleBase)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (vector : Bool) (q : TailPointers) (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hregs : TailRegisters q E) (hmem : TailMemory q state layout h scalar a r) :
    ∃ after, (program p g).runFrom E (if vector then 9 else 8) state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  have hc : DoubleBaseContract
      (if vector then p.avx2DoubleBase else p.serialDoubleBase) layout doubleBase := by
    cases vector <;> assumption
  obtain ⟨middle, encoded, hcall, hframe, hresult, hencoded⟩ := hc q.output q.challenge q.point q.scalar
    state h scalar a hmem.wellFormed hmem.output hmem.challenge hmem.point hmem.scalar
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
  cases vector with
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

/-- Register writes performed by the dispatch block preserve every backend
argument, the comparison constants, and the signature argument. -/
theorem TailRegisters.dispatch (q : TailPointers) (E : Env program.Γ)
    (hregs : TailRegisters q E) (value : BitVec 8) :
    TailRegisters q
      (E[%65 := .value value, %66 := .value (BitVec.ofBool (value == 1))]) := by
  rcases hregs with ⟨ho, hc, hh, ha, hs, hr, hk, hl, hz, h1, hok, he⟩
  change E.args 1 = .value q.signature at hr
  constructor <;> simp [mlir_env, *]

/-- Runtime dispatch is proved for every cache byte. The prefix initializes
only on 255; other non-one values select the serial branch directly. -/
theorem dispatch_tail_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (hserial : DoubleBaseContract p.serialDoubleBase layout doubleBase)
    (havx2 : DoubleBaseContract p.avx2DoubleBase layout doubleBase)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32) (cacheValue : BitVec 8)
    (hregs : TailRegisters q E) (hmem : TailMemory q state layout h scalar a r)
    (hcacheFits : Fits state.mem q.cache 8)
    (hcache : state.mem.readAt q.cache 8 = cacheValue) :
    ∃ after, (program p g).runFrom E 7 state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  rw [dispatch_block p g E state q.cache cacheValue hregs.cache hregs.one hcacheFits hcache]
  simpa using
    backend_tail_of_contracts p g layout doubleBase compress hserial havx2 hcompress hcompare
      (decide (cacheValue = 1)) q _ state h scalar a r (TailRegisters.dispatch q E hregs cacheValue) hmem

/-- Cache initialization preserves the immutable backend inputs and original
R bytes. The cache can share an allocation with other data provided its byte
range is disjoint; requiring distinct allocation IDs is unnecessary. -/
structure CacheDisjoint (q : TailPointers) : Prop where
  challenge : (Range.of q.challenge 256).Disjoint (Range.of q.cache 8)
  point : (Range.of q.point 1280).Disjoint (Range.of q.cache 8)
  scalar : (Range.of q.scalar 256).Disjoint (Range.of q.cache 8)
  signature : (Range.of q.signature 256).Disjoint (Range.of q.cache 8)

theorem TailMemory.cache_frame (q : TailPointers) (state after : GlobalState)
    (layout : Layout Point Scalar Result) (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hmem : TailMemory q state layout h scalar a r)
    (hframe : OutputFrame state after q.cache 1) (hd : CacheDisjoint q) :
    TailMemory q after layout h scalar a r := by
  refine ⟨hframe.wellFormed, hframe.live _ _ hmem.output,
    hframe.live _ _ hmem.compressed, ?_, ?_, ?_, ?_,
    hmem.outputChallenge, hmem.outputPoint, hmem.outputScalar,
    hmem.signatureOutput, hmem.compressedOutput, hmem.signatureCompressed⟩
  · exact ⟨hframe.live _ _ hmem.challenge.1,
      (hframe.read _ _ hd.challenge).trans hmem.challenge.2⟩
  · exact ⟨hframe.live _ _ hmem.point.1,
      (hframe.read _ _ hd.point).trans hmem.point.2⟩
  · exact ⟨hframe.live _ _ hmem.scalar.1,
      (hframe.read _ _ hd.scalar).trans hmem.scalar.2⟩
  · exact ⟨hframe.live _ _ hmem.signature.1,
      (hframe.read _ _ hd.signature).trans hmem.signature.2⟩

theorem TailRegisters.initialize (q : TailPointers) (E : Env program.Γ)
    (hregs : TailRegisters q E) (returned : BitVec 1) :
    TailRegisters q (E[%64 := .value returned]) := by
  rcases hregs with ⟨ho, hc, hh, ha, hs, hr, hk, hl, hz, h1, hok, he⟩
  change E.args 1 = .value q.signature at hr
  constructor <;> simp [mlir_env, *]

/-- Initialization, reloaded-byte dispatch, selected backend, compression, byte
comparison, and cleanup all execute in sequence in the generated CFG. -/
theorem initialized_tail_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (hserial : DoubleBaseContract p.serialDoubleBase layout doubleBase)
    (havx2 : DoubleBaseContract p.avx2DoubleBase layout doubleBase)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (hinit : CacheContract p.initializeAvx2Cache q.cache)
    (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hregs : TailRegisters q E) (hmem : TailMemory q state layout h scalar a r)
    (hcache : ReadBytes state q.cache 1 255) (hd : CacheDisjoint q) :
    ∃ after, (program p g).runFrom E 6 state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil,
        after) := by
  obtain ⟨middle, returned, hcall, hframe⟩ :=
    hinit state hmem.wellFormed hcache
  rw [initialize_cache_block p g E state middle returned hcall]
  exact dispatch_tail_of_contracts p g layout doubleBase compress
    hserial havx2 hcompress hcompare q _ middle h scalar a r
    (middle.mem.readAt q.cache 8) (TailRegisters.initialize q E hregs returned)
    (TailMemory.cache_frame q state middle layout h scalar a r hmem hframe hd)
    (hframe.live q.cache 1 hcache.1).fits rfl

end Agave.Ed25519.Verifier.Execution.Dalek
