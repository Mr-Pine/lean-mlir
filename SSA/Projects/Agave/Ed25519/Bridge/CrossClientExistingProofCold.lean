import SSA.Projects.Agave.Ed25519.Bridge.CrossClientCold
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerExistingProof
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FullCall

/-!
Final composition with the original FD conformance proof and the actual
linked scalar-wide execution theorem supplied directly.
This endpoint retains that proof's three explicit legacy SHA bindings. Its
separate audit rejects native certificates and permits exactly those three
bindings plus Lean's three standard foundations.
The standard-foundation composition remains in the separate module.
The scalar-wide theorem and this endpoint have passed their exact audits
against the completed reducer dependency closure.
-/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer.Common
open LeanMLIR.RIR (Vals EffectM)
attribute [local instance] Classical.propDecidable

/-- The existing FD proof discharges the complete FD run. Agave's remaining
machine leaves, initialized memory and local hash/reduction agreement remain
transparent. The linked scalar-wide execution theorem discharges `hwide`.
The original R/A bytes are read directly from FD's input buffers. -/
theorem existingProof_cold_crossClient_observations
    (remaining : Dalek.Primitives) (dg : Dalek.Globals)
    (compressCall : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (compression : Agave.Ed25519.SHA512.Compression)
    (cg : Execution.Challenge.Globals) (sg : ScalarWide.Globals)
    (scg : SHA512Finalization.CompressionGlobals)
    (ddg : Encoding.Decompress.Execution.Decode.Globals)
    (dsg : Encoding.Decompress.Execution.SqrtRatio.Globals)
    (decode : Bytes32 → Option ValidPoint) (timesEight : ValidPoint → ValidPoint)
    (hdecode : ValidPoint.DecoderCorrect decode)
    (hleaves : ResidualLeaves.NonDecoderContracts remaining dg decode timesEight)
    (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
      (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
      (ValidPoint.layout timesEight) (ValidPoint.shared decode))
    (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
    (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
    (fd : FiredancerProofInvocation)
    (hinput : LinkedColdLeaves.Inputs (LinkedColdLeaves.keyPrimitives ddg dsg)
      dg cg sg scg ddg dsg decode timesEight i initial
      fd.a fd.r fd.s fd.messageBytes)
    (hchallenge : (ResidualLeaves.scalarChallenge (Agave.Ed25519.SHA512.model compression)
      fd.r fd.a fd.messageBytes).val = fd.challenge) :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives remaining compressCall sg cg ddg dsg)
        dg Signature.program.call)
      i initial =
      (firedancerObserve FiredancerProofInvocation.programs fd.message fd.size fd.signature
        fd.publicKey fd.sha fd.state).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) && decide (CanonicalY fd.r)) :=
  cold_crossClient_observations (LinkedColdLeaves.keyPrimitives ddg dsg) remaining dg
    compressCall compression cg sg scg ddg dsg decode timesEight
    hdecode hleaves hdecodeRun hcompress (ScalarWide.execution_obligation sg)
    i initial fd.a fd.r fd.s fd.messageBytes hinput
    FiredancerProofInvocation.programs fd.message fd.size fd.signature fd.publicKey fd.sha
    fd.state fd.challenge fd.executionRefines hchallenge

end Agave.Ed25519.Bridge
