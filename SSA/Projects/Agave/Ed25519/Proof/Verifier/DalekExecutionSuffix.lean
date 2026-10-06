import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionScalar
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionCopy
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionTail

/-! Composition of the exact scalar gate, emitted copy, CPUID selection, and
both arithmetic backends. The scalar input bytes are universally quantified. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- Backend input memory before the scalar's uninitialized stack slot is filled. -/
structure TailBeforeCopy (q : TailPointers) (state : GlobalState)
    (layout : Layout Point Scalar Result) (h : Scalar) (a : Point) (r : Bytes32) : Prop where
  wellFormed : state.WF
  output : SmallRange state.mem q.output 160
  compressed : SmallRange state.mem q.compressed 32
  challenge : ReadBytes state q.challenge 32 (layout.scalar h)
  point : ReadBytes state q.point 160 (layout.point a)
  scalar : SmallRange state.mem q.scalar 32
  signature : ReadBytes state q.signature 32 r
  outputChallenge : (Range.of q.output 1280).Disjoint (Range.of q.challenge 256)
  outputPoint : (Range.of q.output 1280).Disjoint (Range.of q.point 1280)
  outputScalar : (Range.of q.output 1280).Disjoint (Range.of q.scalar 256)
  signatureOutput : (Range.of q.signature 256).Disjoint (Range.of q.output 1280)
  compressedOutput : (Range.of q.compressed 256).Disjoint (Range.of q.output 1280)
  signatureCompressed : (Range.of q.signature 256).Disjoint (Range.of q.compressed 256)
  challengeScalar : (Range.of q.challenge 256).Disjoint (Range.of q.scalar 256)
  pointScalar : (Range.of q.point 1280).Disjoint (Range.of q.scalar 256)
  signatureScalar : (Range.of q.signature 256).Disjoint (Range.of q.scalar 256)

theorem TailBeforeCopy.frame (hm : TailBeforeCopy q state layout h a r)
    (hf : OutputFrame state after out bytes)
    (hc : (Range.of q.challenge 256).Disjoint (Range.of out (8 * bytes)))
    (ha : (Range.of q.point 1280).Disjoint (Range.of out (8 * bytes)))
    (hr : (Range.of q.signature 256).Disjoint (Range.of out (8 * bytes))) :
    TailBeforeCopy q after layout h a r := by
  refine ⟨hf.wellFormed, hf.live _ _ hm.output, hf.live _ _ hm.compressed,
    ?_, ?_, hf.live _ _ hm.scalar, ?_, hm.outputChallenge, hm.outputPoint,
    hm.outputScalar, hm.signatureOutput, hm.compressedOutput, hm.signatureCompressed,
    hm.challengeScalar, hm.pointScalar, hm.signatureScalar⟩
  · exact ⟨hf.live _ _ hm.challenge.1, (hf.read _ _ hc).trans hm.challenge.2⟩
  · exact ⟨hf.live _ _ hm.point.1, (hf.read _ _ ha).trans hm.point.2⟩
  · exact ⟨hf.live _ _ hm.signature.1, (hf.read _ _ hr).trans hm.signature.2⟩

theorem TailBeforeCopy.finish {Point Scalar Result : Type}
    {q : TailPointers} {state : GlobalState}
    {layout : Layout Point Scalar Result} {h scalar : Scalar} {a : Point} {r : Bytes32}
    (hm : TailBeforeCopy q state layout h a r)
    (hs : ReadBytes state q.scalar 32 (layout.scalar scalar)) :
    TailMemory q state layout h scalar a r :=
  ⟨hm.wellFormed, hm.output, hm.compressed, hm.challenge, hm.point, hs,
    hm.signature, hm.outputChallenge, hm.outputPoint, hm.outputScalar,
    hm.signatureOutput, hm.compressedOutput, hm.signatureCompressed⟩

theorem TailRegisters.scalarCopy (q : TailPointers) (E : Env program.Γ)
    (hr : TailRegisters q E) (cached : BitVec 8) :
    TailRegisters q (scalarCopyEnv E q.signature q.scalar cached) := by
  rcases hr with ⟨ho, hc, hh, ha, hs, hr, hk, hl, hz, h1, hok, he⟩
  change E.args 1 = .value q.signature at hr
  constructor <;> simp [scalarCopyEnv, mlir_env, *]

theorem TailRegisters.scalarCheck (q : TailPointers) (E : Env program.Γ)
    (hr : TailRegisters q E) (first last : BitVec 8) (equal : Bool) :
    TailRegisters q (scalarBlockEnv E q.signature first last equal) := by
  rcases hr with ⟨ho, hc, hh, ha, hs, hr, hk, hl, hz, h1, hok, he⟩
  change E.args 1 = .value q.signature at hr
  constructor <;> simp [scalarBlockEnv, mlir_env, *]

/-- Block 5 is joined to both CPUID paths and the final comparison. The source
scalar's first byte was loaded by block 4; its remaining bytes are read now. -/
theorem copy_tail_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (hserial : DoubleBaseContract p.serialDoubleBase layout doubleBase)
    (havx2 : DoubleBaseContract p.avx2DoubleBase layout doubleBase)
    (hcompress : CompressContract p.compressPoint layout compress)
    (hcompare : CompareContract p.compareBytes)
    (q : TailPointers) (hinit : CacheContract p.initializeAvx2Cache q.cache)
    (E : Env program.Γ) (state : GlobalState)
    (h scalar : Scalar) (a : Point) (r : Bytes32)
    (hregs : TailRegisters q E) (hmem : TailBeforeCopy q state layout h a r)
    (hfirst : E.read (%50) = .value ((layout.scalar scalar).extractLsb' 0 8))
    (h33 : E.read (%15) = .value 33#64) (h1 : E.read (%16) = .value 1#64)
    (h31 : E.read (%17) = .value 31#64)
    (hsig : SmallRange state.mem q.signature 64)
    (hbytes : ReadBytes state (q.signature.add 32#64) 32 (layout.scalar scalar))
    (hds : (Range.of q.signature 512).Disjoint (Range.of q.scalar 256))
    (hc : SmallRange state.mem q.cache 1) (hdc : CacheDisjoint q) :
    ∃ after, (program p g).runFrom E 5 state =
      .value (.cons (.value (code (decide (compress (doubleBase h a scalar) = r)))) .nil, after) := by
  let first := (layout.scalar scalar).extractLsb' 0 8
  let copied := scalarCopyState state q.signature q.scalar first
  let cached := copied.mem.readAt q.cache 8
  have hhigh := scalar_signature_subread state q.signature (layout.scalar scalar) hbytes 1 31 (by decide)
  change state.mem.readAt (q.signature.add 33#64) 248 = (layout.scalar scalar).extractLsb' 8 248 at hhigh
  have hread := scalar_copy_readback state q.signature q.scalar first (layout.scalar scalar)
    hmem.scalar hhigh rfl
  have hframe := scalar_copy_frame state q.signature q.scalar first hmem.wellFormed hmem.scalar
  have htail := (hmem.frame hframe hmem.challengeScalar hmem.pointScalar hmem.signatureScalar).finish hread
  have hregsc := TailRegisters.scalarCopy q E hregs cached
  have hfc := hframe.live q.cache 1 hc
  have hdhigh := disjoint_add_subrange hsig hds.symm (k := 33) (count := 31) (by decide)
  have hdcopy := (disjoint_add_subrange hmem.scalar hdhigh.symm (k := 1) (count := 31) (by decide)).symm
  rw [scalar_copy_block p g E state q.signature q.scalar q.cache first cached
    hregs.signature hregs.scalar hregs.cache hfirst h33 h1 h31 hregs.ok
    hsig hmem.scalar hdcopy hc.fits rfl]
  by_cases heq : cached = 255#8
  · simp only [heq, ↓reduceIte]
    have hi := initialized_tail_of_contracts p g layout doubleBase compress hserial havx2 hcompress
      hcompare q hinit _ copied h scalar a r hregsc htail ⟨hfc, heq⟩ hdc
    simpa only [heq] using hi
  · simp only [heq, ↓reduceIte]
    exact dispatch_tail_of_contracts p g layout doubleBase compress hserial havx2 hcompress
      hcompare q _ copied h scalar a r cached hregsc htail hfc.fits rfl

/-- Pure observation at the scalar-parser entry: failed parsing rejects;
successful parsing proceeds to byte-for-byte comparison with the original R. -/
def scalarSuffix (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (h : Scalar) (a : Point) (r bytes : Bytes32) : Bool :=
  match shared.parseScalar bytes with
  | none => false
  | some scalar => decide (compress (doubleBase h a scalar) = r)

/-- Blocks 4 through 13 implement the scalar parser and compressed-point
comparison from individual primitive contracts, for arbitrary scalar bytes. -/
theorem scalar_tail_of_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (challenge : Bytes32 → Bytes32 → List (BitVec 8) → Scalar)
    (contracts : PrimitiveContracts p g layout shared doubleBase compress challenge)
    (q : TailPointers) (hqcache : q.cache = g.address1)
    (E : Env program.Γ) (state : GlobalState)
    (h : Scalar) (a : Point) (r bytes : Bytes32) (scratch : Pointer)
    (hregs : TailRegisters q E) (hmem : TailBeforeCopy q state layout h a r)
    (hscratch : E.read (%20) = .value scratch) (h63 : E.read (%12) = .value 63#64)
    (h33 : E.read (%15) = .value 33#64) (h1 : E.read (%16) = .value 1#64)
    (h31 : E.read (%17) = .value 31#64)
    (hsig : SmallRange state.mem q.signature 64)
    (hbytes : ReadBytes state (q.signature.add 32#64) 32 bytes)
    (hfit : SmallRange state.mem scratch 32)
    (hdScratchSig : (Range.of scratch 256).Disjoint (Range.of q.signature 512))
    (hdScratchChallenge : (Range.of q.challenge 256).Disjoint (Range.of scratch 256))
    (hdScratchPoint : (Range.of q.point 1280).Disjoint (Range.of scratch 256))
    (hds : (Range.of q.signature 512).Disjoint (Range.of q.scalar 256))
    (hc : SmallRange state.mem q.cache 1) (hdc : CacheDisjoint q) :
    ∃ after, (program p g).runFrom E 4 state =
      .value (.cons (.value (code (scalarSuffix shared doubleBase compress h a r bytes))) .nil, after) := by
  have hdscratchS := disjoint_add_subrange hsig hdScratchSig (k := 32) (count := 32) (by decide)
  obtain ⟨middle, hframe, hrun⟩ := scalar_check_of_contracts p g layout contracts.scalarReduce
    contracts.bytesConstantTimeEq contracts.blackBoxByte E state q.signature scratch bytes
    hregs.signature hscratch hregs.length h63 hregs.ok hregs.one hmem.wellFormed hsig hfit hbytes hdscratchS
  let checked := scalarBlockEnv E q.signature (bytes.extractLsb' 0 8) (bytes.extractLsb' 248 8)
    (decide (bytes = layout.reduce bytes))
  have hregsm : TailRegisters q checked := TailRegisters.scalarCheck q E hregs _ _ _
  have hdSigScratch := disjoint_add_subrange hsig hdScratchSig (k := 0) (count := 32) (by decide)
  simp only [Pointer.add_zero] at hdSigScratch
  have hm := hmem.frame hframe hdScratchChallenge hdScratchPoint hdSigScratch.symm
  cases hs : shared.parseScalar bytes with
  | none =>
    have hgate : scalarGate layout bytes = false := by
      cases hg : scalarGate layout bytes with
      | false => rfl
      | true =>
        obtain ⟨scalar, hparse⟩ := contracts.scalarComplete bytes hg
        rw [hs] at hparse
        cases hparse
    refine ⟨middle, ?_⟩
    rw [hrun, hgate]
    simpa [scalarSuffix, hs, code, checked] using
      (scalar_rejection p g checked middle hregsm.error)
  | some scalar =>
    obtain ⟨hgate, hencoded⟩ := (contracts.scalarParse bytes scalar).mp hs
    have hbm := OutputFrame.readBytes state middle scratch (q.signature.add 32#64) 32 32 bytes
      hframe hbytes hdscratchS.symm
    rw [← hencoded] at hbm
    have hinit : CacheContract p.initializeAvx2Cache q.cache := by
      simpa only [hqcache] using contracts.initializeAvx2Cache
    have hf : checked.read (%50) = .value ((layout.scalar scalar).extractLsb' 0 8) := by
      simp [checked, scalarBlockEnv, mlir_env, hencoded]
    have h33m : checked.read (%15) = .value 33#64 := by simp [checked, scalarBlockEnv, mlir_env, h33]
    have h1m : checked.read (%16) = .value 1#64 := by simp [checked, scalarBlockEnv, mlir_env, h1]
    have h31m : checked.read (%17) = .value 31#64 := by simp [checked, scalarBlockEnv, mlir_env, h31]
    obtain ⟨after, htail⟩ := copy_tail_of_contracts p g layout doubleBase compress contracts.serialDoubleBase
      contracts.avx2DoubleBase contracts.compressPoint contracts.compareBytes q hinit checked middle
      h scalar a r hregsm hm hf h33m h1m h31m (hframe.live _ _ hsig) hbm hds
      (hframe.live _ _ hc) hdc
    refine ⟨after, ?_⟩
    rw [hrun, hgate]
    simpa only [scalarSuffix, hs, ↓reduceIte] using htail

end Agave.Ed25519.Verifier.Execution.Dalek
