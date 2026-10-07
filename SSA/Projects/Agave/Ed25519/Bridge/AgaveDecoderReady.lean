import SSA.Projects.Agave.Ed25519.Bridge.CrossClientBackendInputs
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.DecoderSemanticReady

/-! The concrete decoder supplies its exact caller frame and the finite
R-decoder prefix at the states returned by the verifier's actual prefix calls. -/
namespace Agave.Ed25519.Verifier.Execution
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 24000
set_option maxHeartbeats 8000000

namespace ColdInput

theorem linked_decoder_callerBlocks
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (initial : GlobalState) (i : Invocation) (a : Bytes32)
    (hwf : initial.WF) (hkey : Dalek.ReadBytes initial i.publicKey 32 a)
    (hready : Encoding.Decompress.Execution.Ready ddg dsg initial)
    (decoded : GlobalState)
    (hcall : (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
      (Key.args (Key.optionSlot (Wrapper.allocated initial)) i.publicKey)
      ((Wrapper.allocated initial).alloca 168) = .value (.nil, decoded)) :
    CallerBlocks (Wrapper.allocated initial) decoded := by
  have hw := allocated_wf hwf
  have hk := (allocated_blocks initial).readBytes hwf hkey
  have hr := ((hready.alloca hwf 64).alloca hwf.alloca 200).alloca hwf.alloca.alloca 192
  have hout := fresh_range (Wrapper.allocated initial) 168 (by decide)
  have hin : Dalek.ReadBytes ((Wrapper.allocated initial).alloca 168) i.publicKey 32 a :=
    ⟨Dalek.smallRange_alloca _ hw hk.1 _, (MemoryState.readAt_alloca hw hk.1.fits).trans hk.2⟩
  have hf := Encoding.Decompress.Execution.Decode.ReadySemantic.call_callerBlocks ddg dsg
    (Key.optionSlot (Wrapper.allocated initial)) i.publicKey
    ((Wrapper.allocated initial).alloca 168) decoded a hw.alloca hin hout
    (hr.alloca hw 168) hcall (Wrapper.allocated initial).alloc.nextFreeBlock (by rfl)
  intro id hi
  exact (hf id hi).trans (alloca_blocks (Wrapper.allocated initial) 168 id hi)

end ColdInput

namespace Dalek

/-- Deterministic exact calls identify every state in the cold-prefix trace. -/
theorem ColdCallTrace.states_eq
    {p : Primitives} {initial c m e c' m' e' : GlobalState}
    {key signature message : Pointer} {length : Nat}
    (hx : ColdCallTrace p initial key signature message length c m e)
    (hy : ColdCallTrace p initial key signature message length c' m' e') :
    c = c' ∧ m = m' ∧ e = e' := by
  have hc := returnedState_eq_of_call hx.1 hy.1
  subst c'
  have hm := returnedState_eq_of_call hx.2.1 hy.2.1
  subst m'
  obtain ⟨v, he⟩ := hx.2.2
  obtain ⟨v', he'⟩ := hy.2.2
  exact ⟨rfl, rfl, returnedState_eq_of_call he he'⟩

/-- The existing cold-prefix proof supplies the exact bytes, live output,
and initialized constants required by the now closed decoder prefix. -/
theorem decoderPrefix_of_cold_trace
    (p : Primitives) (dg : Globals)
    (cp : Challenge.Primitives) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (compression : Agave.Ed25519.SHA512.Compression)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (cofactor : ValidPoint → ValidPoint)
    (hlink : p.challengeScalar = (Challenge.program cp cg).call)
    (hcompress : SHA512Finalization.CompressContractUnder scg cp.sha512Compress compression)
    (hscalar : SHA512Finalization.ScalarFromSha512ColdContract scg sg cp.scalarFromSha512 compression)
    (hmul : CofactorContract p.pointMulByPow2 (ValidPoint.layout cofactor))
    (heq : SmallOrderEqContract p.pointConstantTimeEq (ValidPoint.layout cofactor)
      (ValidPoint.shared Encoding.Decompress.Valid.decode))
    (initial : GlobalState) (key signature message : Pointer)
    (a r bytes : Bytes32) (minusA : ValidPoint) (msg : List (BitVec 8))
    (hmemory : EntryMemory dg cg (ValidPoint.layout cofactor) initial key signature message
      a r bytes minusA msg)
    (hready : ColdEntryReady scg sg dg ddg dsg initial key signature message)
    (hdecoder : Encoding.Decompress.Execution.Ready ddg dsg initial)
    (challenged multiplied compared : GlobalState)
    (htrace : ColdCallTrace p initial key signature message msg.length challenged multiplied compared) :
    Encoding.Decompress.Execution.Decode.Semantic.PrefixBoundary ddg dsg
      (stackSlot initial 8) signature compared r := by
  let sha := Agave.Ed25519.SHA512.model compression
  obtain ⟨c, m, e, ht, hc, _, hm, he, _⟩ := entry_of_sha_contracts_cold_trace
    p dg (ValidPoint.layout cofactor) (ValidPoint.shared Encoding.Decompress.Valid.decode)
    (ResidualLeaves.scalarChallenge sha) cp cg sg scg compression ddg dsg hlink hcompress hscalar
    (ResidualLeaves.scalarChallenge_encoding sha) hmul heq rfl
    (Env.init (inputArgs key signature message msg.length).get) initial key signature message
    a r minusA msg rfl rfl rfl rfl hmemory.wellFormed hmemory.keyRange hmemory.signatureRange
    hmemory.messageRange hmemory.publicKey hmemory.signatureR hmemory.point hmemory.messageBytes
    hmemory.lengthBound hmemory.identity hmemory.shaIV hready
  obtain ⟨hce, hme, hee⟩ := ColdCallTrace.states_eq htrace ht
  subst c m e
  have hstack := hready.stackCache hmemory.wellFormed
  have hid : SmallRange multiplied.mem (stackSlot initial 3) 160 :=
    hm.live _ _ (hc.live _ _ (hstack 3) (stackSlot_live initial hmemory.wellFormed 3 13 (by decide)))
  have hr : ReadBytes initial signature 32 r :=
    ⟨by simpa only [Pointer.add_zero] using smallRange_add hmemory.signatureRange (k := 0) (count := 32) (by decide),
      hmemory.signatureR⟩
  have hin := cold_entry_readBytes scg initial challenged multiplied compared hc hm he hid
    signature 32 r hready.signatureCache (stackState_readBytes initial hmemory.wellFormed 13 hr)
    (stackSlot_disjoint_caller initial hmemory.wellFormed 12 hr.1 256 256).symm
    (stackSlot_disjoint_caller initial hmemory.wellFormed 4 hr.1 1280 256).symm
    (stackSlot_disjoint_caller initial hmemory.wellFormed 3 hr.1 1280 256).symm
  exact Encoding.Decompress.Execution.Decode.ReadySemantic.prefixBoundary_of_ready ddg dsg
    compared (stackSlot initial 8) signature r he.wellFormed hin
    (cold_entry_stack_live scg initial challenged multiplied compared hmemory.wellFormed hc hm he hstack 8 (by decide))
    (cold_entry_decoder_ready scg ddg dsg initial challenged multiplied compared hmemory.wellFormed
      hc hm he hdecoder (hstack 3) hready.curveDCache hready.sqrtM1Cache)

end Dalek
end Agave.Ed25519.Verifier.Execution
