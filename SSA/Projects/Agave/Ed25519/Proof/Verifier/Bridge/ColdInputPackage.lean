import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputDecoder
import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputCopies

/-! The cold endpoint's intermediate `Inputs` package follows from concrete
caller memory, external initialized globals, and one framed public-key decode.
No post-constructor, post-copy, or challenge-stack premise is retained. -/
namespace Agave.Ed25519.Verifier.Execution.ColdInput
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- The immutable Montgomery initializers, without an invocation-specific
output pointer. Separation from the actual challenge stack is derived below. -/
structure ReductionGlobals (g : ScalarWide.Globals) (state : GlobalState) : Prop where
  rAddress : g.address0 = ScalarWide.montgomeryR.address g.address0.id
  rrAddress : g.address1 = ScalarWide.montgomeryRR.address g.address1.id
  rPresent : ScalarWide.montgomeryR.Present g.address0.id state.mem
  rrPresent : ScalarWide.montgomeryRR.Present g.address1.id state.mem
  separate : g.address0.id ≠ g.address1.id

/-- True external initialization and mutable-cache separation at the caller
boundary. Fresh wrapper/constructor/Dalek stack disjointness is not assumed. -/
structure InitializedGlobals (dg : Dalek.Globals) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (initial : GlobalState) (message : Pointer) : Prop where
  identity : Dalek.ReadBytes initial dg.address0 40 (1#320)
  dalekCache : SmallRange initial.mem dg.address1 1
  shaIV : Dalek.ReadBytes initial cg.address0 64 Challenge.initialWords
  compression : SHA512Finalization.CompressionReady scg initial
  reduction : ReductionGlobals sg initial
  decoder : Encoding.Decompress.Execution.Ready ddg dsg initial
  messageCache : message.id ≠ scg.cache
  reduceRCache : sg.address0.id ≠ scg.cache
  reduceRRCache : sg.address1.id ≠ scg.cache
  identityCache : dg.address0.id ≠ scg.cache
  dalekCacheCache : dg.address1.id ≠ scg.cache
  curveDCache : ddg.address0.id ≠ scg.cache
  sqrtM1Cache : dsg.address0.id ≠ scg.cache

theorem CallerBlocks.compressionReady (hf : CallerBlocks before after) (hwf : before.WF)
    (h : SHA512Finalization.CompressionReady g before) :
    SHA512Finalization.CompressionReady g after := by
  obtain ⟨value, hv, hp⟩ := h.cache
  exact ⟨hf.present hwf h.constants, ⟨value, hv, hf.present hwf hp⟩, h.separate⟩

theorem CallerBlocks.reductionGlobals (hf : CallerBlocks before after) (hwf : before.WF)
    (h : ReductionGlobals g before) : ReductionGlobals g after :=
  ⟨h.rAddress, h.rrAddress, hf.present hwf h.rPresent,
    hf.present hwf h.rrPresent, h.separate⟩

theorem CallerBlocks.decoderReady (hf : CallerBlocks before after) (hwf : before.WF)
    (h : Encoding.Decompress.Execution.Ready dg sg before) :
    Encoding.Decompress.Execution.Ready dg sg after :=
  ⟨hf.readBytes hwf h.curveD, hf.readBytes hwf h.sqrtM1⟩

theorem present_stack {g : ByteGlobal} {id : BlockId} (hwf : state.WF)
    (h : g.Present id state.mem) (n : Nat) : g.Present id (Dalek.stackState state n).mem := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.alloca (Dalek.stackState_wf state hwf n)

theorem ReductionGlobals.ready (h : ReductionGlobals g state) (hwf : state.WF) :
    ScalarWide.Ready g (Dalek.allocated state) (Dalek.stackSlot state 12) := by
  have hr : SmallRange state.mem g.address0 40 := by
    rw [h.rAddress]
    exact ⟨_, h.rPresent, by decide, by simp [ByteGlobal.address, ScalarWide.montgomeryR]⟩
  have hrr : SmallRange state.mem g.address1 40 := by
    rw [h.rrAddress]
    exact ⟨_, h.rrPresent, by decide, by simp [ByteGlobal.address, ScalarWide.montgomeryRR]⟩
  exact ⟨h.rAddress, h.rrAddress, present_stack hwf h.rPresent 13,
    present_stack hwf h.rrPresent 13, h.separate,
    Dalek.stackSlot_ne_caller state hwf 12 hr,
    Dalek.stackSlot_ne_caller state hwf 12 hrr⟩

theorem coldReady
    (h : InitializedGlobals dg cg sg scg ddg dsg initial i.message)
    (hwf : initial.WF) (hw : decoded.WF)
    (hd : CallerBlocks (Wrapper.allocated initial) decoded) :
    Dalek.ColdEntryReady scg sg dg ddg dsg
      (LinkedLeaves.afterSignature i initial decoded x t valid)
      (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message := by
  have hf := afterSignature_blocks (i := i) (x := x) (t := t) (valid := valid) hwf hd
  exact ⟨hf.compressionReady hwf h.compression,
    (hf.reductionGlobals hwf h.reduction).ready (afterSignature_wf hw),
    fresh_ne hwf h.compression.cache_range (key_fresh initial),
    fresh_ne hwf h.compression.cache_range (signature_fresh initial),
    h.messageCache, h.reduceRCache, h.reduceRRCache, h.identityCache,
    h.dalekCacheCache, h.curveDCache, h.sqrtM1Cache⟩

/-- Constructor for every field of the previous cold invocation package.
The decoder's full successful payload derives the six overlapping X/T loads
and the Y/Z copies; malformed keys need no successful continuation. -/
theorem inputs_of_decoder
    (kp : Key.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (i : Invocation) (initial decoded : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : CallerMemory i initial a r s message)
    (hg : InitializedGlobals dg cg sg scg ddg dsg initial i.message)
    (hd : DecoderResult kp decode initial decoded i a) :
    LinkedColdLeaves.Inputs kp dg cg sg scg ddg dsg decode timesEight
      i initial a r s message := by
  obtain ⟨x, t, hk, hcoords⟩ := decoderCall h.wellFormed h.publicKey.1 hd
  refine ⟨h.length, decoded, x, t, hk, ?_⟩
  intro A hA
  obtain ⟨hx, ht, hy, hz⟩ := hcoords A hA
  refine ⟨hx, ht, hy, hz, ?_, ?_, ?_⟩
  · simpa [hA] using signatureMemory dg cg (ValidPoint.layout timesEight) A.negate
      (x := x) (t := t) h hd.callerBlocks hd.wellFormed hg.identity hg.dalekCache hg.shaIV
  · exact coldReady hg h.wellFormed hd.wellFormed hd.callerBlocks
  · exact (afterSignature_blocks h.wellFormed hd.callerBlocks).decoderReady h.wellFormed hg.decoder

/-- The actual linked decoder contract is invoked on the caller's public-key
bytes. Its exact block frame is the sole extra decoder-memory premise beyond
the pre-existing contextual decoder contract. -/
theorem inputs_of_linked_decoder
    (dg : Dalek.Globals) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (hdecode : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
      (ValidPoint.layout timesEight) (ValidPoint.shared decode))
    (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : CallerMemory i initial a r s message)
    (hg : InitializedGlobals dg cg sg scg ddg dsg initial i.message)
    (hframe : ∀ decoded,
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
        (Key.args (Key.optionSlot (Wrapper.allocated initial)) i.publicKey)
        ((Wrapper.allocated initial).alloca 168) = .value (.nil, decoded) →
      CallerBlocks (Wrapper.allocated initial) decoded) :
    LinkedColdLeaves.Inputs (LinkedColdLeaves.keyPrimitives ddg dsg)
      dg cg sg scg ddg dsg decode timesEight i initial a r s message := by
  obtain ⟨decoded, hd⟩ := decoderResult_of_contract ddg dsg decode timesEight hdecode
    initial i a h.wellFormed h.publicKey hg.decoder hframe
  exact inputs_of_decoder _ dg cg sg scg ddg dsg decode timesEight
    i initial decoded a r s message h hg hd

end Agave.Ed25519.Verifier.Execution.ColdInput
