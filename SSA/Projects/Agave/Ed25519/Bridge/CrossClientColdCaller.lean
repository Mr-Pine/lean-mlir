import SSA.Projects.Agave.Ed25519.Bridge.CrossClientCold
import SSA.Projects.Agave.Ed25519.Proof.Verifier.Bridge.ColdInputPackage

/-! Cold cross-client observation from caller bytes and initialized globals.
The public-key decoder's exact caller-block frame remains explicit: its existing
`OutputFrame` contract alone does not establish exact allocation lengths. -/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
attribute [local instance] Classical.propDecidable

section
variable (remaining : Dalek.Primitives) (dg : Dalek.Globals)
variable (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
variable (compression : Agave.Ed25519.SHA512.Compression)
variable (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
variable (scg : SHA512Finalization.CompressionGlobals)
variable (ddg : Encoding.Decompress.Execution.Decode.Globals)
variable (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
variable (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
variable (hdecode : ValidPoint.DecoderCorrect decode)
variable (hleaves : ResidualLeaves.NonDecoderContracts remaining dg decode timesEight)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout timesEight) (ValidPoint.shared decode))
variable (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
variable (hwide : ScalarWide.ExecutionObligation sg)
variable (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
variable (a r s : Bytes32) (message : List (BitVec 8))
variable (hinput : ColdInput.CallerMemory i initial a r s message)
variable (hglobals : ColdInput.InitializedGlobals dg cg sg scg ddg dsg initial i.message)
variable (hframe : ∀ decoded,
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
    (Key.args (Key.optionSlot (Wrapper.allocated initial)) i.publicKey)
    ((Wrapper.allocated initial).alloca 168) = .value (.nil, decoded) →
  ColdInput.CallerBlocks (Wrapper.allocated initial) decoded)
variable (fdPrograms : FiredancerShaPrograms)
variable (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
variable (fdSignature fdPublicKey fdSha : LeanMLIR.Pointer) (fdState : LeanMLIR.GlobalState)
variable (fdChallenge : Nat)
variable (hfd : FiredancerExecutionRefines fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha
  fdState a r s fdChallenge)
variable (hchallenge : (ResidualLeaves.scalarChallenge
  (Agave.Ed25519.SHA512.model compression) r a message).val = fdChallenge)


include hdecode hleaves hdecodeRun hcompress hwide hinput hglobals hframe hfd hchallenge

/-- All intermediate constructor/copy/entry memory is derived. The remaining
frame premise is scoped to the actual public-key decoder call in this invocation. -/
theorem cold_caller_crossClient_observations :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives remaining compressCall sg cg ddg dsg)
        dg Signature.program.call) i initial =
      (firedancerObserve fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY r)) := by
  exact cold_crossClient_observations (LinkedColdLeaves.keyPrimitives ddg dsg) remaining dg
    compressCall compression cg sg scg ddg dsg decode timesEight hdecode hleaves hdecodeRun
    hcompress hwide i initial a r s message
    (ColdInput.inputs_of_linked_decoder dg cg sg scg ddg dsg decode timesEight hdecodeRun
      i initial a r s message hinput hglobals hframe)
    fdPrograms fdMessage fdSize fdSignature fdPublicKey fdSha fdState fdChallenge hfd hchallenge

end
end Agave.Ed25519.Bridge
