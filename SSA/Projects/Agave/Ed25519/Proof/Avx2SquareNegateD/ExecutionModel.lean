import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionMachine
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.Machine
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.Reduction
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionMachine
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Packing

namespace Agave.Ed25519.Avx2SquareNegateD.Execution
open LeanMLIR.RIR

/-- The D lane alone selects the exact wrapping subtraction before reduce64. -/
def signedColumns4 (a : Blocks) : Reduce64.Execution.Columns4 :=
  fun k => Vector.ofFn fun lane =>
    machineSignedColumns (Avx2FieldMul.Execution.unpackBlocks a lane)
      (decide (lane = 3)) k

def inputNat (a : Blocks) (lane : Fin 4) : Limbs :=
  fun i => (Avx2FieldMul.Execution.unpackBlocks a lane i).toNat

theorem signedColumns4_toNat (a : Blocks) (lane : Fin 4)
    (ha : Bounded (inputNat a lane)) (k : Fin 10) :
    ((signedColumns4 a k)[lane]).toNat = signedColumns (inputNat a lane)
      (decide (lane = 3)) k := by
  have h := machineSignedColumns_toNat ha (decide (lane = 3)) k
  simpa [signedColumns4, inputNat] using h

theorem signedColumns4_bound (a : Blocks) (lane : Fin 4)
    (ha : Bounded (inputNat a lane)) :
    Reduce64.ColumnsBound (fun k => ((signedColumns4 a k)[lane]).toNat) := by
  intro k
  change ((signedColumns4 a k)[lane]).toNat < 2^63
  rw [signedColumns4_toNat a lane ha]
  exact signedColumns_lt_u63 ha _ k

end Agave.Ed25519.Avx2SquareNegateD.Execution
