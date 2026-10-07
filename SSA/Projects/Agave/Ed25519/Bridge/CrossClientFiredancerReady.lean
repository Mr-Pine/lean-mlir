import SSA.Projects.Agave.Ed25519.Bridge.CrossClientCold
import SSA.Projects.Agave.Ed25519.Bridge.CrossClientChallengeValue
import SSA.Projects.Agave.Ed25519.Bridge.FiredancerInvocationChallenge

/-!
Reusable cold cross-client composition with the original Firedancer proof,
loader readiness and the separate hash/reduction boundaries. This layer
supplies FD scalar determinism, table values, digest returns, the full FD run
and challenge equality. Its Agave leaf proofs are supplied by callers;
`CrossClientReady` instantiates the available linked proof witnesses.
-/
namespace Agave.Ed25519.Bridge
open Verifier Verifier.Execution Firedancer Firedancer.Common
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
variable (hleaves : ResidualLeaves.NonDecoderContracts remaining dg
  decode timesEight)
variable (hdecodeRun : Dalek.DecompressContractUnder (Encoding.Decompress.Execution.Ready ddg dsg)
  (Encoding.Decompress.Execution.linkedProgram ddg dsg).call
  (ValidPoint.layout timesEight) (ValidPoint.shared decode))
variable (hcompress : SHA512Finalization.CompressContractUnder scg compressCall compression)
variable (hwide : ScalarWide.ExecutionObligation sg)
variable (i : Invocation) (initial : LeanMLIR.RIR.GlobalState)
variable (fdState : LeanMLIR.GlobalState) (fdMessage : LeanMLIR.Pointer) (fdSize : BitVec 64)
variable (fdSignature fdPublicKey : LeanMLIR.Pointer) (kbits : BitVec (80 * 64))
variable (input : FiredancerInputReady fdState fdMessage fdSize fdSignature fdPublicKey)
variable (fdGlobals : FiredancerGlobalsReady fdState kbits)
variable (calls : FiredancerHashCalls)
variable (finishBlock : Option LeanMLIR.LiveBlock → BitVec 64 →
  Option LeanMLIR.LiveBlock → BitVec 64 → Option LeanMLIR.LiveBlock)
variable (hinit : Sha512InitBy calls.init)
variable (happend : Sha512AppendBy kbits calls.append)
variable (hfinish : Sha512FiniBy kbits calls.finish finishBlock)
variable (hinput : LinkedColdLeaves.Inputs (LinkedColdLeaves.keyPrimitives ddg dsg)
  dg cg sg scg ddg dsg decode timesEight i initial
  (readBuf (input.args fdGlobals.reference.wf).pkBuf)
  (readBuf (input.args fdGlobals.reference.wf).sigBuf)
  (readBuf (input.args fdGlobals.reference.wf).sBuf)
  (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))
variable (hhash : Challenge.DigestBy calls
  ((firedancerWithSha fdState).mem.live? (firedancerFreshSha fdState).id) 0
  (Agave.Ed25519.SHA512.model compression).digest)
variable (hreturns : ∃ words, firedancerSourceReduce
  ((Agave.Ed25519.SHA512.model compression).digest (hashTranscript
    (readBuf (input.args fdGlobals.reference.wf).sigBuf)
    (readBuf (input.args fdGlobals.reference.wf).pkBuf)
    (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))) = some words)
variable (hvalue : ∀ words, firedancerSourceReduce
  ((Agave.Ed25519.SHA512.model compression).digest (hashTranscript
    (readBuf (input.args fdGlobals.reference.wf).sigBuf)
    (readBuf (input.args fdGlobals.reference.wf).pkBuf)
    (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))) = some words →
  (packWords words).toNat = hashToScalar
    ((Agave.Ed25519.SHA512.model compression).digest (hashTranscript
      (readBuf (input.args fdGlobals.reference.wf).sigBuf)
      (readBuf (input.args fdGlobals.reference.wf).pkBuf)
      (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)))))

include hdecode hleaves hdecodeRun hcompress hwide hinit happend hfinish hinput hhash hreturns hvalue

/-- Prepared FD execution composes with any caller-supplied Agave leaf proofs.
All FD execution and challenge-equality witnesses are constructed. -/
theorem prepared_cold_crossClient_observations :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives remaining
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve FiredancerProofInvocation.programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS) &&
          decide (CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf))) := by
  exact cold_crossClient_observations (LinkedColdLeaves.keyPrimitives ddg dsg)
    remaining dg compressCall compression cg sg scg ddg dsg
    decode timesEight hdecode hleaves hdecodeRun hcompress hwide i initial
    (readBuf (input.args fdGlobals.reference.wf).pkBuf)
    (readBuf (input.args fdGlobals.reference.wf).sigBuf)
    (readBuf (input.args fdGlobals.reference.wf).sBuf)
    (bytesOf (readWord (input.args fdGlobals.reference.wf).msgFits)) hinput
    FiredancerProofInvocation.programs fdMessage fdSize fdSignature fdPublicKey
    (firedancerFreshSha fdState) (firedancerWithSha fdState) _
    (FiredancerProofInvocation.ready_executionRefines_of_digestBy_local fdState fdMessage fdSize
      fdSignature fdPublicKey kbits input fdGlobals calls finishBlock hinit happend hfinish
      (Agave.Ed25519.SHA512.model compression).digest hhash hreturns hvalue)
    (agave_scalarChallenge_eq_messageChallenge _ _ _ _)

/-- On canonical R, compare only Agave's Boolean with FD's success code. -/
theorem prepared_cold_crossClient_of_canonical
    (hcanonical : CanonicalY (readBuf (input.args fdGlobals.reference.wf).sigBuf)) :
    Execution.observe
      (linkedWrapper (LinkedColdLeaves.keyPrimitives ddg dsg)
        (LinkedColdLeaves.primitives remaining
          compressCall sg cg ddg dsg) dg Signature.program.call)
      i initial =
      (firedancerObserve FiredancerProofInvocation.programs fdMessage fdSize fdSignature
        fdPublicKey (firedancerFreshSha fdState) (firedancerWithSha fdState)).map
        (fun ret => decide (ret = FD_ED25519_SUCCESS)) := by
  simpa only [hcanonical, decide_true, Bool.and_true] using
    prepared_cold_crossClient_observations remaining dg compressCall compression cg sg scg ddg dsg
      decode timesEight hdecode hleaves hdecodeRun hcompress hwide i initial fdState fdMessage fdSize fdSignature
      fdPublicKey kbits input fdGlobals calls finishBlock hinit happend hfinish hinput
      hhash hreturns hvalue

end
end Agave.Ed25519.Bridge
