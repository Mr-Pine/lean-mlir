/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead
import SSA.Projects.Agave.LatticeHash.MLIR.PortableMemory

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression CompressionExit

theorem packBits_singleton (x : Word) : packBits (#v[x]) = x := by
  have h := extract_packBits (#v[x]) (0 : Fin 1)
  simpa using h

/-- The portable store chain has the same byte layout as one SIMD lane. -/
theorem portableCompressionMemory_eq_outputMem (m : MemoryState) (out : Pointer)
    (v : State Word) :
    portableCompressionMemory m out v = outputMem out (fun i => #v[v i]) 16 m := by
  cases out
  have hcast : @Nat.cast (Fin 16) (Fin.NatCast.instNatCast 16) 1 = (1 : Fin 16) := by decide
  simp [portableCompressionMemory, outputMem, packBits_singleton, Pointer.withOffset, hcast]

/-- Observe any word stored by the compiled portable compression contract. -/
theorem portableCompressionMemory_read_word (m : MemoryState) (out : Pointer)
    (v : State Word) (hfit : Fits m out 512)
    (hwrap : out.offset.toNat + 64 ≤ 2^64) (i : Fin 16) :
    readWord? (out.withOffset (BitVec.ofNat 64 (4*i.val))) 32
      (portableCompressionMemory m out v) = some (v i) := by
  rw [portableCompressionMemory_eq_outputMem]
  simpa using outputMem_read_lane out (fun i => #v[v i]) m hfit hwrap i (0 : Fin 1)

end AgaveLatticeHash.MLIR
