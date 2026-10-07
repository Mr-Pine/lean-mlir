import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedColdLeaves
import SSA.Projects.Agave.Ed25519.Proof.Verifier.LinkedResidualLeavesUnder
import SSA.Projects.Agave.Ed25519.Proof.Verifier.DalekExecutionColdUnder

/-! The linked wrapper with backend readiness at this invocation's pointers.
Earlier universal endpoints remain available as compatibility interfaces. -/
namespace Agave.Ed25519.Verifier.Execution.LinkedColdLeavesUnder
open LeanMLIR.RIR

noncomputable abbrev keyPrimitives := LinkedColdLeaves.keyPrimitives
noncomputable abbrev challengePrimitives := LinkedColdLeaves.challengePrimitives
noncomputable abbrev primitives := LinkedColdLeaves.primitives

/-- Environment readiness is needed only after a successful public-key decode.
The decoded state and concrete verifier stack pointers are fixed by this call. -/
def BackendInputs (kp : Key.Primitives) (dp : Dalek.Primitives) (dg : Dalek.Globals)
    (scg : SHA512Finalization.CompressionGlobals)
    (serialReady avx2Ready : Dalek.BackendReadyPredicate)
    (decode : Bytes32 → Option ValidPoint) (i : Invocation) (initial : GlobalState)
    (a s : Bytes32) (message : List (BitVec 8)) : Prop :=
  ∀ decoded x t,
    Key.DecoderCall kp (Wrapper.allocated initial) decoded (Wrapper.keyResultSlot initial)
      i.publicKey x t (decode a).isSome →
    ∀ A, decode a = some A →
    Dalek.ColdBackendsReady dp serialReady avx2Ready scg dg
      (LinkedLeaves.afterSignature i initial decoded x t (decode a).isSome)
      (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message message.length s

def Inputs (kp : Key.Primitives) (dp : Dalek.Primitives) (dg : Dalek.Globals) (cg : Challenge.Globals)
    (sg : ScalarWide.Globals) (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (serialReady avx2Ready : Dalek.BackendReadyPredicate)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (i : Invocation) (initial : GlobalState) (a r s : Bytes32) (message : List (BitVec 8)) : Prop :=
  LinkedColdLeaves.Inputs kp dg cg sg scg ddg dsg decode timesEight i initial a r s message ∧
  BackendInputs kp dp dg scg serialReady avx2Ready decode i initial a s message

section
variable (kp : Key.Primitives) (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
variable (serialReady avx2Ready : Dalek.BackendReadyPredicate)
variable (hleaves : ResidualLeaves.NonDecoderContractsUnder remaining dg serialReady avx2Ready decode timesEight)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout timesEight) (ValidPoint.shared decode))
variable (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
variable (hwide : ScalarWide.ExecutionObligation sg)

include hleaves hdecodeRun hcompress hwide

theorem primitive_calls (i : Invocation) (initial : GlobalState)
    (a r s : Bytes32) (message : List (BitVec 8))
    (h : Inputs kp (primitives remaining compressCall sg cg ddg dsg) dg cg sg scg ddg dsg serialReady avx2Ready decode timesEight i initial a r s message) :
    Wrapper.PrimitiveCalls
      (linkedWrapper kp (primitives remaining compressCall sg cg ddg dsg) dg Signature.program.call)
      (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress
      (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression))
      i initial a r s message := by
  obtain ⟨h, hbackend⟩ := h
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
    have hscalar : SHA512Finalization.ScalarFromSha512ColdContract scg sg
        cp.scalarFromSha512 compression :=
      Challenge.coldLinked_finalizer_contract scg sg compression compressCall hcompress hwide
    obtain ⟨afterDalek, hdcall⟩ := Dalek.program_call_of_leaf_contracts_cold_under dp dg
      (ValidPoint.layout timesEight) (ValidPoint.shared decode) ValidPoint.doubleBase
      Bridge.compress (ResidualLeaves.scalarChallenge sha) serialReady avx2Ready
      (ResidualLeaves.NonDecoderContractsUnder.complete remaining dg serialReady avx2Ready cp cg
        (Encoding.Decompress.Execution.linkedProgram ddg dsg).call decode timesEight hleaves)
      ddg dsg hdecodeRun cp cg sg scg compression rfl hcompress hscalar (ResidualLeaves.scalarChallenge_encoding sha) rfl
      (LinkedLeaves.afterSignature i initial decoded A.words.X A.words.T (decode a).isSome)
      (Wrapper.keySlot initial) (Wrapper.signatureSlot initial) i.message a r s A.negate message
      hs.memory hready hdecoderReady
      (hbackend decoded A.words.X A.words.T hdecoder A ha)
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
    (h : Inputs kp (primitives remaining compressCall sg cg ddg dsg) dg cg sg scg ddg dsg serialReady avx2Ready decode timesEight i initial a r s message) :
    Execution.observe
      (linkedWrapper kp (primitives remaining compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      some (verify (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress a r s
        (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression) r a message)) :=
  Wrapper.observe_of_primitive_calls
    (linkedWrapper kp (primitives remaining compressCall sg cg ddg dsg) dg Signature.program.call)
    (ValidPoint.shared decode) ValidPoint.doubleBase Bridge.compress
    (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression)) i initial a r s message
    (primitive_calls kp remaining dg compressCall compression cg sg scg ddg dsg decode timesEight serialReady avx2Ready
      hleaves hdecodeRun hcompress hwide i initial a r s message h)

end
end Agave.Ed25519.Verifier.Execution.LinkedColdLeavesUnder
