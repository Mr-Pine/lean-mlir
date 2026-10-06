import SSA.Projects.Agave.LatticeHash.MLIR.PortableStores
namespace AgaveLatticeHash.MLIR.PortableInPlace
open LeanMLIR SLLVM Firedancer Blake3Compression CompressionExit

/-- Readback for the first eight scalar stores, requiring only the actual32-byte CV allocation. -/
theorem outputMem_read_cv (out : Pointer) (v : State Word)
    (m : MemoryState) (hfit : Fits m out 256)
    (hwrap : out.offset.toNat + 32 ≤ 2^64)
    (count : Nat) (hc : count ≤ 8) (i : Fin 16) (hi : i.val < count) :
    readWord? (out.withOffset (BitVec.ofNat 64 (4*i.val))) 32
      (outputMem out (fun j => #v[v j]) count m) = some (v i) := by
  induction count with
  | zero => omega
  | succ k ih =>
    have hk : k < 16 := by omega
    have hko := offsetInBits_withOffset_nat out (4*k) (by omega)
    have hio := offsetInBits_withOffset_nat out (4*i.val) (by omega)
    simp only [outputMem, packBits_singleton]
    by_cases he : i.val = k
    · have heq : Fin.ofNat 16 k = i := by
        apply Fin.ext
        simp only [Fin.ofNat, Nat.mod_eq_of_lt hk]
        exact he.symm
      rw [heq, ← he]
      apply readWord?_splice_self
      apply fits_outputMem out (fun j => #v[v j]) i.val
      obtain ⟨b, hb, hlen⟩ := hfit
      refine ⟨b, hb, ?_⟩
      rw [hio]
      omega
    · rw [readWord?_splice_disjoint]
      · exact ih (by omega) (by omega)
      · right
        rw [hko, hio]
        omega

end AgaveLatticeHash.MLIR.PortableInPlace
