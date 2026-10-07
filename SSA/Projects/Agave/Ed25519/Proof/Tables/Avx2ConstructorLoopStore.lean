import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorLoopTail
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorState
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! Memory invariants for the unchanged successor-record stores. The earlier
records remain intact inside the same table allocation. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.LoopStore
open LeanMLIR.RIR
open Avx2FieldMul.Execution (Blocks readBlocks)
open Reduce64.Execution (SmallRange)
open State (Slots Ready Frame)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def record (table : Pointer) (n : Nat) : Pointer :=
  table.add (BitVec.ofNat 64 (160*n))

theorem record_next (table : Pointer) (n : Nat) :
    (record table n).add 160#64 = record table (n+1) := by
  simp [record, Pointer.add_add, Nat.mul_add, BitVec.ofNat_add]

def result (s : GlobalState) (table : Pointer) (i : Fin 7) (v : Blocks) : GlobalState :=
  {s with mem := LoopTail.stores s.mem (record table i.val) v}

theorem allocationShape (s : GlobalState) (table : Pointer) (i : Fin 7) (v : Blocks)
    (id : BlockId) :
    ((result s table i v).mem[id]?).map MemoryBlock.length =
      (s.mem[id]?).map MemoryBlock.length := by
  simp [result, LoopTail.stores, SerialPoint.Execution.storeAt_allocationShape]

theorem frame (s : GlobalState) (slots : Slots) (table : Pointer) (i : Fin 7) (v : Blocks)
    (h : Ready slots table s) : Frame slots table s (result s table i v) := by
  refine ⟨(LoopTail.frame s (record table i.val) v h.wf).1, le_refl _,
    allocationShape s table i v, ?_⟩
  intro ptr width _ ht
  exact LoopTail.read_frame s.mem (record table i.val) ptr v width
    (LoopTail.records h.tableBuffer i) (Or.inl ht)

theorem ready (s : GlobalState) (slots : Slots) (table : Pointer) (i : Fin 7) (v : Blocks)
    (h : Ready slots table s) : Ready slots table (result s table i v) :=
  h.preserve (frame s slots table i v h)

theorem fixed_readAt (s : GlobalState) (slots : Slots) (table : Pointer) (i : Fin 7) (v : Blocks)
    (h : Ready slots table s) (off : BitVec 64) (width : Nat) :
    (result s table i v).mem.readAt ((slots 7).add off) width =
      s.mem.readAt ((slots 7).add off) width :=
  LoopTail.read_frame s.mem (record table i.val) ((slots 7).add off) v width
    (LoopTail.records h.tableBuffer i) (Or.inl (h.separateTable 7).symm)

theorem fixed_readBlocks (s : GlobalState) (slots : Slots) (table : Pointer) (i : Fin 7) (v : Blocks)
    (h : Ready slots table s) :
    readBlocks (result s table i v).mem (slots 7) = readBlocks s.mem (slots 7) := by
  funext k
  simp only [readBlocks, fixed_readAt s slots table i v h]

/-- The next record is exactly the five cache vectors passed to the original stores. -/
theorem next_readBlocks (s : GlobalState) (table : Pointer) (i : Fin 7) (v : Blocks)
    (ht : SmallRange s.mem table 1280) :
    readBlocks (result s table i v).mem (record table (i.val+1)) = v := by
  rw [← record_next]
  exact LoopTail.readback s.mem (record table i.val) v (LoopTail.records ht i)

/-- Earlier table records are disjoint byte ranges, despite sharing one block id. -/
theorem prior_disjoint (m : MemoryState) (table : Pointer) (i : Fin 7) (j : Fin 8)
    (ht : SmallRange m table 1280) (hj : j.val ≤ i.val) :
    (Range.of ((record table i.val).add 160#64) 1280).Disjoint
      (Range.of (record table j.val) 1280) := by
  rw [record_next]
  have hi64 : 160*(i.val+1) < 2^64 := by have := i.isLt; omega
  have hj64 : 160*j.val < 2^64 := by have := j.isLt; omega
  have hi := Pointer.offsetInBits_add (ht.no_wrap (k := 160*(i.val+1)) (by have := i.isLt; omega))
  have hj' := Pointer.offsetInBits_add (ht.no_wrap (k := 160*j.val) (by have := j.isLt; omega))
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64] at hi
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj64] at hj'
  simp only [record, Range.Disjoint, Range.of, Pointer.add_id]
  exact Or.inr (Or.inr (by rw [hi, hj']; omega))

/-- Every byte of each earlier record remains unchanged by the five stores. -/
theorem prior_readAt (s : GlobalState) (table : Pointer) (i : Fin 7) (v : Blocks)
    (ht : SmallRange s.mem table 1280) (j : Fin 8) (hj : j.val ≤ i.val)
    (offset count : Nat) (hc : offset + count ≤ 160) :
    (result s table i v).mem.readAt
        ((record table j.val).add (BitVec.ofNat 64 offset)) (8*count) =
      s.mem.readAt ((record table j.val).add (BitVec.ofNat 64 offset)) (8*count) := by
  have hrecord : SmallRange s.mem (record table j.val) 160 :=
    NAF.Memory.Buffer.slice ht (160*j.val) 160 (by have := j.isLt; omega)
  exact LoopTail.read_frame s.mem (record table i.val) _ v _ (LoopTail.records ht i)
    (DoubleBase.RIR.range_disjoint_subrange hrecord (prior_disjoint s.mem table i j ht hj) hc)

theorem prior_readBlocks (s : GlobalState) (table : Pointer) (i : Fin 7) (v : Blocks)
    (ht : SmallRange s.mem table 1280) (j : Fin 8) (hj : j.val ≤ i.val) :
    readBlocks (result s table i v).mem (record table j.val) =
      readBlocks s.mem (record table j.val) := by
  funext k
  have hr := prior_readAt s table i v ht j hj (32*k.val) 32 (by have := k.isLt; omega)
  simp only [readBlocks, hr]

end Agave.Ed25519.Tables.Avx2Constructor.LoopStore

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.LoopStore.frame,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopStore.ready,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopStore.fixed_readBlocks,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopStore.next_readBlocks,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopStore.prior_disjoint,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopStore.prior_readAt,
      `Agave.Ed25519.Tables.Avx2Constructor.LoopStore.prior_readBlocks] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"
    logInfo m!"standard-three audit passed: {endpoint}"
