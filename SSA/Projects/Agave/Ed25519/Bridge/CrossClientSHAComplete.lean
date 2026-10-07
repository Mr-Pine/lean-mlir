import SSA.Projects.Agave.Ed25519.Bridge.CrossClientBackendInputs
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.FinalizationDispatchComplete

/-! Connect the actual SHA dispatcher to verifier backend readiness. The
compression function and its correctness premise are fixed to the checked RIR
implementation. Decoder and backend readiness conditions retain their original
invocation-local interfaces. -/
namespace Agave.Ed25519.Verifier.Execution.BackendReadiness

open LeanMLIR.RIR
open Dalek.SerialBackendReadiness (Ready Separate LinkedPrefix)
open Agave.Ed25519.SHA512.Execution.Dispatch

set_option maxRecDepth 16384

/-- The backend-readiness bridge now receives its SHA contract from the
actual scalar/AVX2 dispatcher proof, for every reached block count. -/
theorem inputs_of_linked_sha
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
    (hchallengeLink : dp.challengeScalar =
      (Challenge.program
        (LinkedColdLeaves.challengePrimitives (Finalization.linkedCall hardware scg) sg) cg).call)
    (hdecoderLink : dp.decompress = (Encoding.Decompress.Execution.linkedProgram ddg dsg).call)
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
    (hprefix : DecoderPrefix (LinkedColdLeaves.keyPrimitives ddg dsg) dp ddg dsg decode
      i initial a r message) :
    LinkedColdLeavesGuarded.BackendInputs (LinkedColdLeaves.keyPrimitives ddg dsg) dp dg scg
      (DoubleBase.RIR.serialLinkedReady g d2) (Dalek.Avx2BackendReadiness.ready ag)
      decode i initial a s message :=
  inputs dp dg cg sg scg ddg dsg decode timesEight hardware laws hlink g d2 ag
    (Finalization.linkedCall hardware scg) Agave.Ed25519.SHA512.Spec.compression
    hchallengeLink hdecoderLink (Finalization.Complete.linked_compress_contract hardware laws scg)
    hdecode i initial a r s message hcaller hglobals hframe hserial havx hseparate havxSeparate hprefix

end Agave.Ed25519.Verifier.Execution.BackendReadiness
