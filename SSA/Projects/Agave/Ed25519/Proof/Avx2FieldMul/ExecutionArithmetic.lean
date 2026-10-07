import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionModel
import SSA.Projects.Agave.Ed25519.Proof.Avx2FieldMul.ExecutionMemory
import SSA.Projects.Agave.Ed25519.Proof.Reduce64.Execution.Output

namespace Agave.Ed25519.Avx2FieldMul.Execution
open LeanMLIR.RIR
open Reduce64.Execution

/-- The caller's input reader and the stored-output reader use the same
physical lane layout. This identity has no field-size premise. -/
theorem inputNat_readBlocks_eq_outputWord (m : MemoryState) (p : Pointer)
    (lane : Fin 4) (limb : Fin 10) :
    inputNat (readBlocks m p) lane limb = (outputWord m p limb lane).toNat := by
  fin_cases lane <;> fin_cases limb <;>
    simp [inputNat, readBlocks, unpackBlocks, outputWord,
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

/-- Every stored limb is the integer product specification, with all narrowing
and carry bounds discharged from the caller's original asymmetric invariant. -/
theorem outputWord_product (m : MemoryState) (r : Pointer) (a b : Blocks)
    (hr : SmallRange m r 160) (lane : Fin 4)
    (ha : LeftBound (inputNat a lane)) (hb : RightBound (inputNat b lane))
    (limb : Fin 10) :
    (outputWord (storeOutputs m r (rawColumns4 a b)) r limb lane).toNat =
      product (inputNat a lane) (inputNat b lane) limb := by
  rw [outputWord_toNat m r _ hr lane (rawColumns4_bound a b lane ha hb)]
  simp only [rawColumns4_toNat a b lane ha hb]
  rfl

end Agave.Ed25519.Avx2FieldMul.Execution
