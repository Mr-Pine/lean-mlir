import SSA.Projects.Agave.Ed25519.Proof.Encoding.CompressExecution.Program
import SSA.Projects.Agave.Ed25519.Proof.Encoding.DecompressExecution.Linked
import SSA.Projects.Agave.Ed25519.Proof.Verifier.ExecutionProgram

/-! Link the exact verifier-tail compression symbol to its actual imported
body, and close its lower call graph with the imported field and subtle bodies.
This establishes code identity only; prefix execution refinement is separate. -/
namespace Agave.Ed25519.Encoding.Compress.Execution
open LeanMLIR.RIR

noncomputable def linkedPrimitives : Primitives where
  pow22501 := (Decompress.Execution.Pow22501.program
    Decompress.Execution.pow22501Primitives).call
  pow2k := Decompress.Execution.Pow2k.program.call
  mul := SerialFieldMul.kernel.call
  blackBoxByte := Decompress.Execution.BlackBox.program.call

noncomputable def linkedProgram : Func := program linkedPrimitives

/-- The verifier's exact `EdwardsPoint8compress` external call is replaced by
this imported body; no mathematical compressor is installed as an oracle. -/
noncomputable def linkVerifier (p : Verifier.Execution.Dalek.Primitives) :
    Verifier.Execution.Dalek.Primitives :=
  {p with compressPoint := linkedProgram.call}

theorem verifier_compression_is_imported (p : Verifier.Execution.Dalek.Primitives) :
    (linkVerifier p).compressPoint = (program linkedPrimitives).call := rfl

end Agave.Ed25519.Encoding.Compress.Execution
