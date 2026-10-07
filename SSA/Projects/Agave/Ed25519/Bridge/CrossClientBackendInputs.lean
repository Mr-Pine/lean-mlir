import SSA.Projects.Agave.Ed25519.Bridge.CrossClientAvx2Cold
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionSerialVerifier
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekSerialPrefixShape
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedSerialBackendReady
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedColdLeavesGuarded

/-! Both concrete backends receive their loaded globals from the original
caller. The only prefix obligation left is the finite boundary at the reached R
decoder; challenge and global-length effects are constructed from proved calls. -/
namespace Agave.Ed25519.Verifier.Execution.BackendReadiness
open LeanMLIR.RIR
open Dalek.SerialBackendReadiness (Ready Separate LinkedPrefix)
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

/-- The sole remaining shape-related premise is the exact reached R decoder
finite prefix after the public-key small-order check continues; challenge execution and all allocation lengths are derived. -/
def DecoderPrefix (kp : Key.Primitives) (dp : Dalek.Primitives)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint)
    (i : Invocation) (initial : GlobalState) (a r : Bytes32) (message : List (BitVec 8)) : Prop :=
  ∀ decoded x t,
    Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (decode a).isSome →
    ∀ A, decode a = some A →
    (ValidPoint.shared decode).smallOrder A.negate = false →
    let entry := LinkedLeaves.afterSignature i initial decoded x t (decode a).isSome
    ∀ challenged multiplied compared,
      Dalek.ColdCallTrace dp entry (Wrapper.keySlot initial) (Wrapper.signatureSlot initial)
        i.message message.length challenged multiplied compared →
      Encoding.Decompress.Execution.Decode.Semantic.PrefixBoundary ddg dsg
        (Dalek.stackSlot entry 8) (Wrapper.signatureSlot initial) compared r

theorem avxShaSeparate (hr : DoubleBase.ExecutionAvx2.GlobalsReady ag initial)
    (hc : SHA512Finalization.CompressionReady scg initial) : ag.address2.id ≠ scg.cache := by
  obtain ⟨value, _, hcache⟩ := hc.cache
  intro hi
  have hp := hr.basePresent
  rw [hi] at hp
  have he := congrArg (fun block : Option MemoryBlock => block.map MemoryBlock.length)
    (hp.symm.trans hcache)
  have hn : (10240 : Nat) = 1 := Option.some.inj he
  omega

/-- Caller memory and loaded backend globals supply all backend readiness.
There is no constructor, arithmetic-block, or arbitrary readiness premise. -/
theorem inputs
    (dp : Dalek.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (hardware : Dalek.Avx2Cache.Instructions.HardwareInstructions)
    (laws : Dalek.Avx2Cache.Instructions.InstructionContracts hardware)
    (hlink : LinkedPrefix dp hardware dg.address1)
    (g : DoubleBase.SerialCFG.Globals) (d2 : Tables.SerialConstructor.Globals)
    (ag : DoubleBase.Avx2CFG.Globals)
    (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compression : Agave.Ed25519.SHA512.Compression)
    (hchallengeLink : dp.challengeScalar =
      (Challenge.program (LinkedColdLeaves.challengePrimitives compressCall sg) cg).call)
    (hdecoderLink : dp.decompress = (Encoding.Decompress.Execution.linkedProgram ddg dsg).call)
    (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
    (hdecode : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
      (ValidPoint.layout timesEight) (ValidPoint.shared decode))
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8))
    (hcaller : ColdInput.CallerMemory i initial a r s message)
    (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
    (hframe : ∀ decoded,
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
        (Key.args (Key.optionSlot (Wrapper.allocated initial)) i.publicKey)
        ((Wrapper.allocated initial).alloca 168) = .value (.nil, decoded) →
      ColdInput.CallerBlocks (Wrapper.allocated initial) decoded)
    (hserial : Ready g d2 initial) (havx : DoubleBase.ExecutionAvx2.GlobalsReady ag initial)
    (hseparate : Separate g d2 dg.address1)
    (havxSeparate : ag.address2.id ≠ dg.address1.id)
    (hprefix : DecoderPrefix (LinkedColdLeaves.keyPrimitives ddg dsg) dp ddg dsg decode i initial a r message) :
    LinkedColdLeavesGuarded.BackendInputs (LinkedColdLeaves.keyPrimitives ddg dsg) dp dg scg
      (DoubleBase.RIR.serialLinkedReady g d2) (Dalek.Avx2BackendReadiness.ready ag)
      decode i initial a s message := by
  obtain ⟨_, known, knownX, knownT, hk, hmemory⟩ :=
    ColdInput.inputs_of_linked_decoder dg cg sg scg ddg dsg decode timesEight hdecode
      i initial a r s message hcaller hglobals hframe
  intro decoded x t hd A hA hsmall
  have hkeyState := Dalek.returnedState_eq_of_call
    (Key.call_of_decoder _ _ _ _ _ _ _ _ hd)
    (Key.call_of_decoder _ _ _ _ _ _ _ _ hk)
  have hentry : LinkedLeaves.afterSignature i initial decoded x t (decode a).isSome =
      LinkedLeaves.afterSignature i initial known knownX knownT (decode a).isSome :=
    congrArg (fun state => Signature.copied (Wrapper.copiedKey initial state)
      (Wrapper.signatureSlot initial) i.signature) hkeyState
  rw [hentry]
  obtain ⟨hx, ht, hy, hz, hm, hready, _⟩ := hmemory A hA
  subst knownX knownT
  have hk' : Key.DecoderCall (LinkedColdLeaves.keyPrimitives ddg dsg) (Wrapper.allocated initial) known
      (Wrapper.keyResultSlot initial) i.publicKey A.words.X A.words.T true := by simpa [hA] using hk
  have hm' : LinkedConcretePayload.SignatureMemoryExceptPoint dg cg (ValidPoint.layout timesEight)
      i initial known A.words.X A.words.T true a r s A.negate message := by simpa [hA] using hm
  have hsignature := LinkedValidPayload.signatureMemory_of_decoder _ dg cg timesEight
    i initial known A a r s message hk' hy hz hm'
  have hmem : Dalek.EntryMemory dg cg (ValidPoint.layout timesEight)
      (LinkedLeaves.afterSignature i initial known A.words.X A.words.T (decode a).isSome)
      (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message a r s A.negate message := by
    simpa [hA] using (hsignature.continuation Signature.program.call rfl).memory
  have hb := ColdInput.afterSignature_blocks (i := i) (x := A.words.X) (t := A.words.T)
    (valid := (decode a).isSome) hcaller.wellFormed (hframe known hk.call)
  have hs := Dalek.SerialBackendReadiness.coldReady_of_decoder_prefix dp dg g d2
    compressCall compression cg sg scg ddg dsg timesEight hchallengeLink hdecoderLink hcompress
    _ _ _ _ a r s A.negate message hmem hready
    (LinkedColdLeavesUnder.serialShaSeparate hserial hglobals.compression)
    (hprefix known A.words.X A.words.T hk A hA hsmall) hardware laws hlink
    (Dalek.serialGlobals_afterSignature g d2 initial known i A.words.X A.words.T _
      hcaller.wellFormed (hframe known hk.call) hserial.1 hserial.2) hseparate
  have hsha := avxShaSeparate havx hglobals.compression
  have hshape : Dalek.Avx2BackendReadiness.ShapeAt dp ag
      (LinkedLeaves.afterSignature i initial known A.words.X A.words.T (decode a).isSome)
      (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message message.length := by
    constructor
    · intro challenged hc
      exact Dalek.SerialBackendReadiness.challenge_allocationShape_at dp dg ag.address2.id
        compressCall compression cg sg scg ddg dsg timesEight hchallengeLink hcompress
        _ _ _ _ a r s A.negate message hmem hready hsha challenged hc
    · intro challenged multiplied compared trace after hc
      rw [hdecoderLink] at hc
      exact Dalek.SerialBackendReadiness.decoder_allocationShape_of_prefix ddg dsg _ _ compared after r
        (hprefix known A.words.X A.words.T hk A hA hsmall challenged multiplied compared trace) hc ag.address2.id
  have ha := Dalek.Avx2BackendReadiness.coldReady dp hardware laws dg hlink ag scg
    _ _ _ _ _ s hmem.wellFormed hmem.keyRange hmem.signatureRange hmem.cache
    ⟨havx.baseAddress, hb.present hcaller.wellFormed havx.basePresent⟩ havxSeparate hsha
    (hready.stackCache hmem.wellFormed) hready.keyCache hready.signatureCache hready.dalekCache hshape
  exact Dalek.ColdBackendsReady.combine hs ha

end Agave.Ed25519.Verifier.Execution.BackendReadiness
