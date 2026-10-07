import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekDecompressContractUnder
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Ready

/-! The decoder's fixed constants are required at its actual call state.
The scalar/backend suffix has no decoder call and needs no decoder contract. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000
namespace Agave.Ed25519.Verifier.Execution.Dalek
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

/-- The remaining named Dalek leaves, excluding the linked challenge and contextual decoder bodies.
These contracts remain explicit implementation-refinement obligations. -/
structure NonDecoderLeafContracts (p : Primitives) (g : Globals)
    (layout : Layout Point Scalar Result) (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    : Prop where
  pointMulByPow2 : CofactorContract p.pointMulByPow2 layout
  pointConstantTimeEq : SmallOrderEqContract p.pointConstantTimeEq layout shared
  blackBoxByte : BlackBoxContract p.blackBoxByte
  scalarReduce : ScalarReduceContract p.scalarReduce layout
  bytesConstantTimeEq : BytesEqContract p.bytesConstantTimeEq
  initializeAvx2Cache : CacheContract p.initializeAvx2Cache g.address1
  serialDoubleBase : DoubleBaseContract p.serialDoubleBase layout doubleBase
  avx2DoubleBase : DoubleBaseContract p.avx2DoubleBase layout doubleBase
  compressPoint : CompressContract p.compressPoint layout compress
  compareBytes : CompareContract p.compareBytes
  scalarParse : ScalarParseContract layout shared
  scalarComplete : ScalarParseComplete layout shared


theorem scalar_tail_of_nondecoder_contracts {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (contracts : NonDecoderLeafContracts p g layout shared doubleBase compress)
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


theorem body_of_decoder_contract_under {Point Scalar Result : Type}
    (p : Primitives) (g : Globals) (layout : Layout Point Scalar Result)
    (shared : Shared Point Scalar)
    (doubleBase : Scalar → Point → Scalar → Result) (compress : Result → Bytes32)
    (contracts : NonDecoderLeafContracts p g layout shared doubleBase compress)
    (ready : GlobalState → Prop)
    (hdecode : DecompressContractUnder ready p.decompress layout shared)
    (hidentity : layout.identity = identityBytes)
    (q : TailPointers) (z : PointPointers) (scratch : Pointer) (hqcache : q.cache = g.address1)
    (E : Env program.Γ) (state : GlobalState)
    (h : Scalar) (a : Point) (r bytes : Bytes32)
    (hregs : BodyRegisters q z scratch E)
    (hmem : BodyMemory q z scratch state layout h a r bytes)
    (hd : BodyDisjoint q z scratch) (hready : ready state) :
    ∃ after, (program p g).runFrom E 1 state =
      .value (.cons (.value (code (bodySuffix shared doubleBase compress h a r bytes))) .nil, after) := by
  have hdsig : (Range.of z.option 1344).Disjoint (Range.of q.signature 256) :=
    (Range.disjoint_of_id_ne (hd.inputOutput q.signature (by simp [bodyReaders])
      z.option (by simp))).symm
  obtain ⟨decoded, hdcall, hdframe, htag⟩ := hdecode z.option q.signature state r
    hmem.tail.wellFormed hready hmem.option hmem.tail.signature hdsig
  have hfits : Fits decoded.mem z.option 64 :=
    Fits.mono (by decide) (hdframe.live _ _ hmem.option).fits
  cases hdec : shared.decompress r with
  | none =>
    simp only [hdec] at htag
    refine ⟨decoded, ?_⟩
    rw [decompress_block p g E state decoded z.option q.signature false
      hregs.point.option hregs.tail.signature hdcall hfits htag]
    simpa [bodySuffix, hdec, code] using
      (decompression_rejection p g _ decoded (hregs.decompress false).tail.error)
  | some point =>
    simp only [hdec] at htag
    let decodedEnv := E[%39 := .value (1#64), %40 := .value (1#1)]
    have hrdec : BodyRegisters q z scratch decodedEnv := hregs.decompress true
    have hmdec := hmem.decompressFrame hdframe hd
    obtain ⟨checked, hpframe, hprun⟩ := point_check_of_contracts p g layout shared hidentity
      contracts.pointMulByPow2 contracts.pointConstantTimeEq z decodedEnv decoded point
      hrdec.point hmdec.tail.wellFormed hmdec.option hmdec.slot29 hmdec.slot30 hmdec.point
      hmdec.cofactor hmdec.identity htag.2 hmdec.one hd.point
    have hrpoint := hrdec.pointCheck (shared.smallOrder point)
    have hmpoint := hmdec.pointFrame hpframe hd
    by_cases hsmall : shared.smallOrder point = true
    · refine ⟨checked, ?_⟩
      rw [decompress_block p g E state decoded z.option q.signature true
        hregs.point.option hregs.tail.signature hdcall hfits htag.1]
      change (program p g).runFrom decodedEnv 2 decoded = _
      rw [hprun, hsmall]
      have hclean := cleanup_blocks p g (pointBlockEnv decodedEnv z true) checked 2#8
        (by simp [pointBlockEnv, mlir_env])
      simpa [bodySuffix, hdec, hsmall, code] using hclean
    · have hfalse : shared.smallOrder point = false := by
        cases hb : shared.smallOrder point with
        | false => rfl
        | true => exact False.elim (hsmall hb)
      obtain ⟨after, htail⟩ := scalar_tail_of_nondecoder_contracts p g layout shared doubleBase compress
        contracts q hqcache _ checked h a r bytes scratch hrpoint.tail hmpoint.tail
        hrpoint.scratch hrpoint.sixtyThree hrpoint.thirtyThree hrpoint.one hrpoint.thirtyOne
        hmpoint.signature hmpoint.scalarBytes hmpoint.scratch
        (Range.disjoint_of_id_ne hd.scratchSignature) (Range.disjoint_of_id_ne hd.challengeScratch)
        (Range.disjoint_of_id_ne hd.pointScratch) (Range.disjoint_of_id_ne hd.signatureScalar)
        hmpoint.cache hd.cache
      refine ⟨after, ?_⟩
      rw [decompress_block p g E state decoded z.option q.signature true
        hregs.point.option hregs.tail.signature hdcall hfits htag.1]
      change (program p g).runFrom decodedEnv 2 decoded = _
      rw [hprun, hfalse]
      simpa [bodySuffix, hdec, hfalse] using htail


end Agave.Ed25519.Verifier.Execution.Dalek
