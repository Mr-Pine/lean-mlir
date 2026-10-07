import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionColumns
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionReduction

namespace Agave.Ed25519.Avx2FieldMul.Execution

/-- Compose the separately checked convolution and carry/packing stages. -/
theorem wordTrace_eq_packedOutput (a b : Blocks) :
    wordTrace a b = Reduce64.Execution.packedOutput (rawColumns4 a b) := by
  rw [wordTrace_eq_stages, columnTrace_eq_columns, reductionTrace_eq_packedOutput]

end Agave.Ed25519.Avx2FieldMul.Execution
