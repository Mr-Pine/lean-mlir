import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceMemory
import SSA.Projects.Agave.LatticeHash.MLIR.PortableInPlaceTail
namespace AgaveLatticeHash.MLIR.PortableInPlace
open LeanMLIR SLLVM Firedancer Blake3Compression
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem cvMemory_read (m : MemoryState) (cvp : Pointer) (x : State Word)
    (hfit : Fits m cvp 256) (hwrap : cvp.offset.toNat + 32 ≤ 2^64) (i : Fin 8) :
    readWord? (cvp.withOffset (BitVec.ofNat 64 (4*i.val))) 32 (cvMemory m cvp x) =
      some (x (i.castAdd 8)) := by
  exact outputMem_read_cv cvp x m hfit hwrap 8 (by omega) (i.castAdd 8) i.isLt

end AgaveLatticeHash.MLIR.PortableInPlace
