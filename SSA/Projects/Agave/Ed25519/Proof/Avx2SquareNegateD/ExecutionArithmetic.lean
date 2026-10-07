import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionModel
import SSA.Projects.Agave.Ed25519.Proof.Avx2SquareNegateD.ExecutionMemory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Output

namespace Agave.Ed25519.Avx2SquareNegateD.Execution
open LeanMLIR.RIR
open Reduce64.Execution

/-- The caller's input reader and the stored-output reader use the same
physical lane layout. This identity has no field-size premise. -/
theorem inputNat_readBlocks_eq_outputWord (m : MemoryState) (p : Pointer)
    (lane : Fin 4) (limb : Fin 10) :
    inputNat (readBlocks m p) lane limb = (outputWord m p limb lane).toNat := by
  fin_cases lane <;> fin_cases limb <;>
    simp [inputNat, readBlocks, Avx2FieldMul.Execution.unpackBlocks, outputWord,
      physicalLane, Ty.extractVecElem]

/-- Reading back the complete stored object recovers its five packed vectors. -/
theorem readBlocks_storeOutputs (m : MemoryState) (p : Pointer) (z : Columns4)
    (hp : SmallRange m p 160) :
    readBlocks (storeOutputs m p z) p = packedOutput z := by
  funext k
  simp only [readBlocks, storeOutputs_readAt m p z hp,
    Ty.extractVecElem_packLanes]
  ext j hj
  simp

theorem outputWord_square (m : MemoryState) (r : Pointer) (a : Blocks)
    (hr : SmallRange m r 160) (lane : Fin 4)
    (ha : Bounded (inputNat a lane)) (limb : Fin 10) :
    (outputWord (storeOutputs m r (signedColumns4 a)) r limb lane).toNat =
      output (inputNat a lane) (decide (lane = 3)) limb := by
  rw [outputWord_toNat m r _ hr lane (signedColumns4_bound a lane ha)]
  simp only [signedColumns4_toNat a lane ha]
  rfl

end Agave.Ed25519.Avx2SquareNegateD.Execution
