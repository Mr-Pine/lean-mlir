import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionColumns
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionReduction

namespace Agave.Ed25519.Avx2SquareNegateD.Execution

/-- Compose the separately checked convolution and carry/packing stages. -/
theorem wordTrace_eq_packedOutput (a : Blocks) :
    wordTrace a = Reduce64.Execution.packedOutput (signedColumns4 a) := by
  rw [wordTrace_eq_stages, columnTrace_eq_columns, reductionTrace_eq_packedOutput]

end Agave.Ed25519.Avx2SquareNegateD.Execution
