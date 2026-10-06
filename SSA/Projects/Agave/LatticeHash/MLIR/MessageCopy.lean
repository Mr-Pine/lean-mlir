/- Released under Apache 2.0 license as described in the file LICENSE. -/
import SSA.Projects.Agave.LatticeHash.MLIR.CompressionSpec
import SSA.Projects.Agave.LatticeHash.MLIR.OutputRead

namespace AgaveLatticeHash.MLIR
open LeanMLIR SLLVM Firedancer Blake3Compression

/-- A full byte-backed copy retains every word-major SIMD message row. -/
theorem CompressionMessage.copy {n : Nat} {mem : MemoryState} {src dst : Pointer}
    {v : State (Vector Word n)} (hmsg : CompressionMessage mem src v)
    (hdst : Fits mem dst (512*n))
    (hsrcWrap : src.offset.toNat + 64*n ≤ 2^64)
    (hdstWrap : dst.offset.toNat + 64*n ≤ 2^64)
    (bytes : BitVec (512*n)) (hr : readWord? src (512*n) mem = some bytes) :
    CompressionMessage (mem.splice dst bytes) dst v := by
  have hw : 32*n*16 = 512*n := by omega
  constructor
  · rw [hw]
    exact fits_splice hdst
  · intro i
    have hk : 32*n*i.val + 32*n ≤ 512*n := by
      have h := Nat.mul_le_mul_left (32*n) (show i.val+1 ≤ 16 from i.isLt)
      simpa only [Nat.mul_add, Nat.mul_one, hw] using h
    have hs := readWord?_extract (q := src.withOffset (BitVec.ofNat 64 (4*n*i.val))) bytes (hw ▸ hmsg.fits) hr rfl (outputRow_offset src hsrcWrap i) hk
    have hd := readWord?_extract (q := dst.withOffset (BitVec.ofNat 64 (4*n*i.val))) bytes (fits_splice hdst)
      (readWord?_splice_self bytes hdst) rfl (outputRow_offset dst hdstWrap i) hk
    exact hd.trans (hs.symm.trans (hmsg.read i))

end AgaveLatticeHash.MLIR
