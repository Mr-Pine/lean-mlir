import SSA.Projects.Agave.Ed25519.Bridge.CrossClientContextual
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerExistingProof

/-!
Final composition with the original FD conformance proof supplied directly.
This endpoint retains that proof's three explicit legacy SHA bindings. Its
separate audit rejects native certificates and permits exactly those three
bindings plus Lean's three standard foundations.
The standard-foundation composition remains in the separate module.
-/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
attribute [local instance] Classical.propDecidable

/-- The existing FD proof discharges the complete FD run. Agave's remaining
machine leaves, initialized memory and local hash/reduction agreement remain
transparent. The original R/A bytes are read directly from FD's input buffers. -/
theorem existingProof_crossClient_observations
    (remaining : Dalek.Primitives) (dg : Dalek.Globals)
    (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compression : Agave.Ed25519.SHA512.Compression)
    (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (hdecode : ValidPoint.DecoderCorrect decode)
    (hleaves : ResidualLeaves.NonDecoderContracts remaining dg decode timesEight)
    (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
      (ValidPoint.layout timesEight) (ValidPoint.shared decode))
    (hcompress : Execution.Challenge.CompressContract compressCall
      (Agave.Ed25519.SHA512.model compression))
    (hwide : SHA512Finalization.LinkedReduceWideContract sg)
    (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
    (fd : FiredancerProofInvocation)
    (hinput : LinkedContextualLeaves.Inputs (LinkedContextualLeaves.keyPrimitives ddg dsg)
      dg cg sg ddg dsg decode timesEight i initial
      fd.a fd.r fd.s fd.messageBytes)
    (hchallenge : (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression)
      fd.r fd.a fd.messageBytes).val = fd.challenge) :
    Execution.observe
      (linkedWrapper (LinkedContextualLeaves.keyPrimitives ddg dsg)
        (LinkedContextualLeaves.primitives remaining compressCall sg cg ddg dsg)
        dg Signature.program.call)
      i initial =
      (firedancerObserve FiredancerProofInvocation.programs fd.message fd.size fd.signature
        fd.publicKey fd.sha fd.state).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY fd.r)) :=
  contextual_crossClient_observations (LinkedContextualLeaves.keyPrimitives ddg dsg) remaining dg
    compressCall compression cg sg ddg dsg decode timesEight
    hdecode hleaves hdecodeRun hcompress hwide i initial fd.a fd.r fd.s fd.messageBytes hinput
    FiredancerProofInvocation.programs fd.message fd.size fd.signature fd.publicKey fd.sha
    fd.state fd.challenge fd.executionRefines hchallenge

end Agave.Ed25519.Bridge
