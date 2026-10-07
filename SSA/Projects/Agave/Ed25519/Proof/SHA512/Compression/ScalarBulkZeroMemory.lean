import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarBulkMemory

/-! The empty fold's chain-store postcondition is literally a memory no-op. -/
namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
open LeanMLIR.RIR

theorem splice_read_self (bytes : BitVec n) (off w : Nat) :
    Memory.spliceBits bytes off (bytes.extractLsb' off w) = bytes := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  simp only [Memory.getLsbD_spliceBits, BitVec.getLsbD_extractLsb']
  split_ifs with h
  · simp [show i - off < w by omega, show off + (i - off) = i by omega]
  · simp

theorem store_read_self (mem : MemoryState) (p : Pointer) (w : Nat) :
    mem.storeAt p (mem.readAt p w) = mem := by
  apply MemoryState.ext
  apply Std.ExtHashMap.ext_getElem?
  intro id
  change (mem.storeAt p (mem.readAt p w))[id]? = mem[id]?
  by_cases hid : id = p.id
  · subst id
    cases hmem : mem[p.id]? with
    | none => simp [MemoryState.storeAt, hmem]
    | some block =>
      rw [MemoryState.getElem?_storeAt_self hmem]
      simp only [MemoryState.readAt, hmem, splice_read_self]
  · exact MemoryState.getElem?_storeAt_ne (q := ⟨id, 0⟩) hid

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarBulk
