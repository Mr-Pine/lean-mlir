/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.Memory
import SSA.Projects.Agave.LatticeHash.Compression

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer
open Blake3Compression

/-- Memory inputs accepted by the Rust `compress_pre` observation wrapper.
The canonical conformance theorem instantiates `initial` with `laneInit`, so
these require the actual BLAKE3 IV and counter halves, not an arbitrary IV. -/
structure CompressionInputs {n : Nat} (mem : MemoryState)
    (cv iv lo hi len flags : Pointer) (initial : State (Vector Word n)) : Prop where
  cvFits : Fits mem cv (32*n*8)
  ivFits : Fits mem iv (32*n*4)
  loFits : Fits mem lo (32*n)
  hiFits : Fits mem hi (32*n)
  lenFits : Fits mem len (32*n)
  flagsFits : Fits mem flags (32*n)
  cvRead : ∀ i : Fin 8,
    readWord? (cv.withOffset (BitVec.ofNat 64 (4*n*i.val))) (32*n) mem =
      some (packBits (initial (i.castAdd 8)))
  ivRead : ∀ i : Fin 4,
    readWord? (iv.withOffset (BitVec.ofNat 64 (4*n*i.val))) (32*n) mem =
      some (packBits (initial ⟨8+i.val, by omega⟩))
  loRead : readWord? lo (32*n) mem = some (packBits (initial 12))
  hiRead : readWord? hi (32*n) mem = some (packBits (initial 13))
  lenRead : readWord? len (32*n) mem = some (packBits (initial 14))
  flagsRead : readWord? flags (32*n) mem = some (packBits (initial 15))

/-- Message vectors are laid out word-major, with every SIMD lane present. -/
structure CompressionMessage {n : Nat} (mem : MemoryState) (p : Pointer)
    (m : State (Vector Word n)) : Prop where
  fits : Fits mem p (32*n*16)
  read : ∀ i : Fin 16,
    readWord? (p.withOffset (BitVec.ofNat 64 (4*n*i.val))) (32*n) mem =
      some (packBits (m i))

/-- One bounds fact for the whole output/message buffer suffices for all
sixteen accesses of the eight-lane kernel. -/
theorem compressionSlotFits8 {mem : MemoryState} {p : Pointer}
    (hp : Fits mem p 4096) (k : Nat) (hk : k < 16) :
    Fits mem (p.withOffset (BitVec.ofNat 64 (32*k))) 256 := by
  have hn : (BitVec.ofNat 64 (32*k)).toNat = 32*k := by simp [BitVec.toNat_ofNat]; omega
  have h := remainingFits mem p hp (BitVec.ofNat 64 (32*k)) (by rw [hn]; omega)
  exact Fits.mono h (by rw [hn]; omega)

/-- Sixteen-lane version of the same buffer bounds rule. -/
theorem compressionSlotFits16 {mem : MemoryState} {p : Pointer}
    (hp : Fits mem p 8192) (k : Nat) (hk : k < 16) :
    Fits mem (p.withOffset (BitVec.ofNat 64 (64*k))) 512 := by
  have hn : (BitVec.ofNat 64 (64*k)).toNat = 64*k := by simp [BitVec.toNat_ofNat]; omega
  have h := remainingFits mem p hp (BitVec.ofNat 64 (64*k)) (by rw [hn]; omega)
  exact Fits.mono h (by rw [hn]; omega)

end AgaveLatticeHash.MLIR
