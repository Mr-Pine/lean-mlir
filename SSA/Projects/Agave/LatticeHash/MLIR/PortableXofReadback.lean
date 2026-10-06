/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.PortableOutputRead
import SSA.Projects.Agave.LatticeHash.Blake3Reference

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit

/-- Physical byte reads of the sixteen stored little-endian words agree with
    the independent portable reference serializer. -/
theorem portableCompressionMemory_read_byte (m : MemoryState) (out : Pointer)
    (v : State Word) (hfit : Fits m out 512)
    (hwrap : out.offset.toNat + 64 ≤ 2^64) (i : Fin 64) :
    readWord? (out.withOffset (BitVec.ofNat 64 i.val)) 8
      (portableCompressionMemory m out v) = some (AgaveBlake3Reference.serialize v i) := by
  let j : Fin 16 := ⟨i.val / 4, by omega⟩
  have hwo := offsetInBits_withOffset_nat out (4*j.val) (by dsimp [j]; omega)
  have hbo := offsetInBits_withOffset_nat out i.val (by omega)
  have hjfit : Fits m (out.withOffset (BitVec.ofNat 64 (4*j.val))) 32 := by
    obtain ⟨b, hb, hlen⟩ := hfit
    refine ⟨b, hb, ?_⟩
    rw [hwo]
    dsimp [j]
    omega
  have hjfit' : Fits (portableCompressionMemory m out v)
      (out.withOffset (BitVec.ofNat 64 (4*j.val))) 32 := by
    rw [portableCompressionMemory_eq_outputMem]
    exact fits_outputMem out (fun k => #v[v k]) 16 hjfit
  have hoff : (out.withOffset (BitVec.ofNat 64 i.val)).offsetInBits =
      (out.withOffset (BitVec.ofNat 64 (4*j.val))).offsetInBits + 8*(i.val%4) := by
    rw [hbo, hwo]
    dsimp [j]
    omega
  exact readWord?_extract (v j) hjfit'
    (portableCompressionMemory_read_word m out v hfit hwrap j) rfl hoff (by omega)

end AgaveLatticeHash.MLIR
