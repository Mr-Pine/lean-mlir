/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead
import SSA.Projects.Agave.LatticeHash.MLIR.BatchXofLoop16

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer

/-- Observing any u16 cell inside a completed actual 512-bit output store
returns exactly the corresponding packed halfword, at its physical address. -/
theorem readOutputChunk16 (mem : MemoryState) (out : Pointer)
    (hfit : Fits mem out 16384) (hz : out.offset = 0)
    (counter half : Fin 32) (chunk : Vector (BitVec 16) 32)
    (hr : readWord? (BatchXofLoop16.outputPtr out counter.val) 512 mem = some (packBits chunk)) :
    readWord? (out.withOffset (BitVec.ofNat 64 (2*(32*counter.val+half.val)))) 16 mem =
      some chunk[half] := by
  have hc := counter.isLt
  have hh := half.isLt
  have hmod : (BitVec.ofNat 64 (64*counter.val)).toNat = 64*counter.val := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  have hchunk : Fits mem (BatchXofLoop16.outputPtr out counter.val) 512 := by
    apply Fits.mono (remainingFits mem out hfit (BitVec.ofNat 64 (64*counter.val)) ?_)
    · rw [hmod]; omega
    · rw [hmod]; omega
  have hp : (BatchXofLoop16.outputPtr out counter.val).offsetInBits = out.offsetInBits + 512*counter.val := by
    unfold BatchXofLoop16.outputPtr
    rw [offsetInBits_withOffset_nat out (64*counter.val) (by rw [hz]; change 0+64*counter.val < 2^64; omega)]
    omega
  have hq : (out.withOffset (BitVec.ofNat 64 (2*(32*counter.val+half.val)))).offsetInBits =
      (BatchXofLoop16.outputPtr out counter.val).offsetInBits + 16*half.val := by
    rw [offsetInBits_withOffset_nat out (2*(32*counter.val+half.val))
      (by rw [hz]; change 0+2*(32*counter.val+half.val) < 2^64; omega), hp]
    omega
  have h := readWord?_extract (q := out.withOffset (BitVec.ofNat 64 (2*(32*counter.val+half.val))))
    (packBits chunk) hchunk hr rfl hq (show 16*half.val+16 ≤ 512 by omega)
  rw [show 16*half.val = half.val*16 by omega, extract_packBits] at h
  exact h

end AgaveLatticeHash.MLIR
