import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory

namespace Agave.Ed25519.Avx2PointAdd.Phases
open LeanMLIR.RIR Reduce64.Execution

/-- Both signed-digit tables contain at most 64 cached 160-byte objects. -/
def tableRow (table : Pointer) (index : Fin 64) : Pointer :=
  table.add (BitVec.ofNat 64 (160 * index.val))

theorem tableIndex_scale (index : Fin 64) :
    Operation.gepInboundsIndex 160 (.value (BitVec.ofNat 64 index.val)) =
      .value ((160 * index.val : Nat) : Int) := by
  fin_cases index <;> decide

theorem smallRange_slice {m : MemoryState} {p : Pointer} {bytes : Nat}
    (h : SmallRange m p bytes) (offset count : Nat) (ho : offset + count ≤ bytes) :
    SmallRange m (p.add (BitVec.ofNat 64 offset)) count := by
  have hov := h.no_wrap (k := offset) (by omega)
  have ho64 : offset < 2 ^ 64 := by have := h.offset_lt; norm_num at *; omega
  obtain ⟨block, hlive, hsmall, hsize⟩ := h
  refine ⟨block, hlive, hsmall, ?_⟩
  change (p.offset + BitVec.ofNat 64 offset).toNat + count ≤ block.length
  rw [BitVec.toNat_add_of_not_uaddOverflow hov, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho64]
  omega

theorem tableRow_live {m : MemoryState} {table : Pointer} {bytes : Nat}
    (h : SmallRange m table bytes) (index : Fin 64)
    (hi : 160 * index.val + 160 ≤ bytes) : SmallRange m (tableRow table index) 160 :=
  smallRange_slice h _ _ hi

end Agave.Ed25519.Avx2PointAdd.Phases
