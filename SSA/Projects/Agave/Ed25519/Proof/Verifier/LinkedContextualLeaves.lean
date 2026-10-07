import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedResidualLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionContextual
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.FullCall
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked

/-!
Exact wrapper composition with the imported SHA finalizer and wide reducer
linked. Montgomery globals are required only at the actual challenge call in
this invocation. The finalizer itself is supplied by its execution theorem;
the remaining SHA-side implementation premises are compression and the exact
linked wide-reducer contract under initialized-table readiness.
-/
namespace Agave.Ed25519.Verifier.Execution.LinkedContextualLeaves
open LeanMLIR.RIR

/-- The key constructor and signature-R check use the same exact decoder. -/
noncomputable def keyPrimitives
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals) : Key.Primitives :=
  ⟨(Encoding.Decompress.Execution.linkedProgram ddg dsg).call⟩

noncomputable def challengePrimitives
    (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (sg : ScalarWide.Globals) : Challenge.Primitives where
  sha512Compress := compressCall
  scalarFromSha512 := (SHA512Finalization.program
    ⟨compressCall, (ScalarWide.linkedProgram sg).call⟩).call

noncomputable def primitives (remaining : Dalek.Primitives)
    (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (sg : ScalarWide.Globals) (cg : Challenge.Globals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals) : Dalek.Primitives :=
  ResidualLeaves.decoderPrimitives remaining (challengePrimitives compressCall sg) cg
    (Encoding.Decompress.Execution.linkedProgram ddg dsg).call

/-- Decoder coordinates, remaining ordinary memory, and initialized Montgomery
tables in this invocation's concrete challenge state. Invalid public keys
require none of the successful-branch continuation obligations. -/
def Inputs (kp : Key.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint)
    (timesEight : ValidPoint → ValidPoint) (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8)) : Prop :=
  i.length = BitVec.ofNat 64 message.length ∧
  ∃ decoded x t,
    Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (decode a).isSome ∧
    ∀ A, decode a = some A →
      x = A.words.X ∧ t = A.words.T ∧
      decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 48#64) 320 =
        Key.coordinatePayload A.words.Y ∧
      decoded.mem.readAt ((Key.optionSlot (Wrapper.allocated initial)).add 88#64) 320 =
        Key.coordinatePayload A.words.Z ∧
      LinkedConcretePayload.SignatureMemoryExceptPoint dg cg (ValidPoint.layout timesEight)
        i initial decoded x t (decode a).isSome a r s A.negate message ∧
      ScalarWide.Ready sg
        (Dalek.allocated (LinkedLeaves.afterSignature i initial decoded x t (decode a).isSome))
        (Dalek.stackSlot (LinkedLeaves.afterSignature i initial decoded x t (decode a).isSome) 12) ∧
      Encoding.Decompress.Execution.Ready ddg dsg
        (LinkedLeaves.afterSignature i initial decoded x t (decode a).isSome)

section
variable (kp : Key.Primitives) (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Challenge.Globals) (sg : ScalarWide.Globals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
variable (hleaves : ResidualLeaves.NonDecoderContracts remaining dg decode timesEight)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout timesEight) (ValidPoint.shared decode))
variable (hcompress : Challenge.CompressContract compressCall (Agave.Ed25519.SHA512.model compression))
variable (hwide : SHA512Finalization.LinkedReduceWideContract sg)

include hleaves hdecodeRun hcompress hwide

theorem primitive_calls (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : Inputs kp dg cg sg ddg dsg decode timesEight i initial a r s message) :
    Wrapper.PrimitiveCalls
      (linkedWrapper kp (primitives remaining compressCall sg cg ddg dsg) dg Signature.program.call)
      (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress
      (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression))
      i initial a r s message := by
  obtain ⟨hlen, decoded, x, t, hdecoder, hmemory⟩ := h
  let dp := primitives remaining compressCall sg cg ddg dsg
  let cp := challengePrimitives compressCall sg
  let sha := Agave.Ed25519.SHA512.model compression
  have hk := Key.wrapper_keyCall kp (linkedWrapper kp dp dg Signature.program.call)
    (ValidPoint.shared decode) i initial decoded a x t rfl hdecoder
  cases ha : decode a with
  | none =>
    refine ⟨_, decoded, decoded, hk, ?_⟩
    intro A hA
    change decode a = some A at hA
    rw [ha] at hA
    cases hA
  | some A =>
    obtain ⟨hx, ht, hy, hz, hm, hready, hdecoderReady⟩ := hmemory A ha
    subst x t
    have hd : Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
        i.publicKey A.words.X A.words.T true := by simpa [ha] using hdecoder
    have hmem : LinkedConcretePayload.SignatureMemoryExceptPoint dg cg (ValidPoint.layout timesEight)
        i initial decoded A.words.X A.words.T true a r s A.negate message := by
      simpa [ha] using hm
    have hsignature : LinkedLeaves.SignatureMemory dg cg (ValidPoint.layout timesEight)
        i initial decoded A.words.X A.words.T (decode a).isSome a r s A.negate message := by
      simpa [ha] using LinkedValidPayload.signatureMemory_of_decoder kp dg cg timesEight
        i initial decoded A a r s message hd hy hz hmem
    have hs := hsignature.continuation Signature.program.call rfl
    have hscalar : SHA512Finalization.ScalarFromSha512ContractUnder (ScalarWide.Ready sg)
        cp.scalarFromSha512 sha :=
      SHA512Finalization.linked_finalizer_contract compression compressCall sg
        (SHA512Finalization.oneBlock_of_compress compressCall compression hcompress) hwide
    obtain ⟨afterDalek, hdcall⟩ := Dalek.program_call_of_leaf_contracts_under dp dg
      (ValidPoint.layout timesEight) (ValidPoint.shared decode) ValidPoint.doubleBase
      Bridge.compress (ResidualLeaves.scalarChallenge sha)
      (ResidualLeaves.NonDecoderContracts.complete remaining dg cp cg
        (Encoding.Decompress.Execution.linkedProgram ddg dsg).call decode timesEight hleaves)
      ddg dsg hdecodeRun cp cg sha sg rfl hcompress hscalar (ResidualLeaves.scalarChallenge_encoding sha) rfl
      (LinkedLeaves.afterSignature i initial decoded A.words.X A.words.T (decode a).isSome)
      (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message a r s A.negate message
      hs.memory hready hdecoderReady
    refine ⟨_, LinkedLeaves.afterSignature i initial decoded A.words.X A.words.T
      (decode a).isSome, afterDalek, hk, ?_⟩
    intro B hB
    change decode a = some B at hB
    have hBA : B = A := Option.some.inj (hB.symm.trans ha)
    subst B
    refine ⟨WrapperKeyLink.key_memory hdecoder.outputRange hs.destinationFits, hs.signature, ?_⟩
    change (Dalek.program dp dg).call
      (Wrapper.dalekArgs (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message i.length)
      (LinkedLeaves.afterSignature i initial decoded A.words.X A.words.T (decode a).isSome) =
      .value (.cons (.value (Dalek.code (prehashed (ValidPoint.shared decode)
        ValidPoint.doubleBase Bridge.compress A.negate r s
        (ResidualLeaves.scalarChallenge sha r a message)))) .nil, afterDalek)
    simpa only [Wrapper.dalekArgs, Dalek.inputArgs, hlen] using hdcall

/-- All imported wrapper/constructor/Dalek/challenge/finalizer code is composed
with local initialized globals. No unrestricted finalizer or whole-verifier
execution hypothesis occurs in this statement. -/
theorem observe (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : Inputs kp dg cg sg ddg dsg decode timesEight i initial a r s message) :
    Execution.observe
      (linkedWrapper kp (primitives remaining compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      some (verify (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress a r s
        (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression) r a message)) :=
  Wrapper.observe_of_primitive_calls
    (linkedWrapper kp (primitives remaining compressCall sg cg ddg dsg) dg Signature.program.call)
    (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress
    (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression)) i initial a r s message
    (primitive_calls kp remaining dg compressCall compression cg sg ddg dsg decode timesEight
      hleaves hdecodeRun hcompress hwide i initial a r s message h)

end
end Agave.Ed25519.Verifier.Execution.LinkedContextualLeaves
