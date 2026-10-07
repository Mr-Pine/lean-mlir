import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhaseMemory
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! Exact byte stores and readback for the constructor's eight initial records. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Broadcast
open LeanMLIR.RIR
open Avx2FieldMul.Execution (Blocks readBlocks)
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-- Numbered physical 32-byte stores in original source order. -/
def memory (m : MemoryState) (table : Pointer) (v : Blocks) : Nat → MemoryState
  | 0 => m
  | n+1 => (memory m table v n).storeAt (table.add (BitVec.ofNat 64 (32*n)))
      (BitVec.packLanes (v ⟨n % 5, Nat.mod_lt _ (by decide)⟩))

def state (s : GlobalState) (table : Pointer) (v : Blocks) (n : Nat) : GlobalState :=
  {s with mem := memory s.mem table v n}

theorem memory_live (h : SmallRange m q bytes) (table : Pointer) (v : Blocks) (n : Nat) :
    SmallRange (memory m table v n) q bytes := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.storeAt _ _

theorem state_wf (h : s.WF) (table : Pointer) (v : Blocks) (n : Nat) :
    (state s table v n).WF := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.storeAt

theorem memory_shape (m : MemoryState) (table : Pointer) (v : Blocks) (n : Nat) (id : BlockId) :
    ((memory m table v n)[id]?).map MemoryBlock.length = (m[id]?).map MemoryBlock.length := by
  induction n with
  | zero => rfl
  | succ n ih => rw [memory, SerialPoint.Execution.storeAt_allocationShape, ih]

theorem memory_read_ne (m : MemoryState) (table : Pointer) (v : Blocks)
    (n : Nat) (q : Pointer) (width : Nat) (hne : table.id ≠ q.id) :
    (memory m table v n).readAt q width = m.readAt q width := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [memory, MemoryState.readAt_storeAt_disjoint
      (Range.disjoint_of_id_ne (by simpa only [Pointer.add_id] using hne)), ih]

/-- Later vector stores cannot overwrite an earlier physical vector. -/
theorem memory_word (m : MemoryState) (table : Pointer) (v : Blocks)
    (h : SmallRange m table 1280) (n k : Nat) (hn : n ≤ 40) (hk : k < n) :
    (memory m table v n).readAt (table.add (BitVec.ofNat 64 (32*k))) 256 =
      BitVec.packLanes (v ⟨k % 5, Nat.mod_lt _ (by decide)⟩) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : k = n
    · subst k
      rw [memory]
      exact MemoryState.readAt_storeAt_self
        ((memory_live h table v n).fits_add (k := 32*n) (count := 32) (by omega)) _
    · rw [memory, MemoryState.readAt_storeAt_disjoint
        (h.disjoint_chunks (i := n) (j := k) (by omega) (by omega) (by omega))]
      exact ih (by omega) (by omega)

/-- All eight logical records read exactly the same five input vectors. -/
theorem readback (m : MemoryState) (table : Pointer) (v : Blocks)
    (h : SmallRange m table 1280) (i : Fin 8) :
    readBlocks (memory m table v 40) (table.add (BitVec.ofNat 64 (160*i.val))) = v := by
  funext k
  apply Vector.ext
  intro j hj
  have hword := memory_word m table v h 40 (5*i.val+k.val) (by decide)
    (by have := i.isLt; have := k.isLt; omega)
  have hmod : (5*i.val+k.val) % 5 = k.val := by omega
  have hindex : (⟨(5*i.val+k.val) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = k := Fin.ext hmod
  have hoff : 32*(5*i.val+k.val) = 160*i.val+32*k.val := by omega
  rw [hindex, hoff] at hword
  simp [readBlocks, Pointer.add_add, ← BitVec.ofNat_add, hword, Ty.extractVecElem_packLanes]

end Agave.Ed25519.Tables.Avx2Constructor.Broadcast
