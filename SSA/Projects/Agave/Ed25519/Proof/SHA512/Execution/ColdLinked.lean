import SSA.Projects.Agave.Ed25519.Proof.SHA512.Execution.ColdChallengeCall
import SSA.Projects.Agave.Ed25519.Proof.ScalarWide.FullCall

/-! Discharge the imported wide reducer's local execution obligation in the
cold finalizer adapter. The compression ABI remains the sole execution premise. -/
namespace Agave.Ed25519.Verifier.Execution.Challenge

open LeanMLIR.RIR
open SHA512Finalization (CompressionGlobals ScalarFromSha512ColdContract)

/-- The actual linked finalizer, using the proved complete wide-reduction
call rather than assuming its execution obligation. -/
theorem coldLinked_finalizer_contract_proved (cg : CompressionGlobals) (rg : ScalarWide.Globals)
    (compress : Agave.Ed25519.SHA512.Compression)
    (call : Vals [.ptr, .ptr, .bv 64] → EffectM (Vals []))
    (hcompress : SHA512Finalization.CompressContractUnder cg call compress) :
    ScalarFromSha512ColdContract cg rg (coldLinkedPrimitives rg call).scalarFromSha512 compress :=
  coldLinked_finalizer_contract cg rg compress call hcompress (ScalarWide.execution_obligation rg)

end Agave.Ed25519.Verifier.Execution.Challenge
