import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAdd
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorState
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! The checked positive-add state specialized to the constructor's eight
scratch allocations. The complete table and the fixed doubled point survive. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.AddState
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2FieldMul.Execution (readBlocks storeBlocks)
open State (Slots Ready Frame)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Pointer assignment in the unchanged constructor. -/
def q (slots : Slots) : Scratch :=
  ⟨slots 6, slots 3, slots 2, slots 1, slots 0, slots 4⟩

def scratchIndex : Fin 6 → Fin 8 := ![6, 3, 2, 1, 0, 4]

theorem written_eq (slots : Slots) (i : Fin 6) :
    (q slots).written i = slots (scratchIndex i) := by
  fin_cases i <;> rfl

def index (i : Fin 7) : Fin 64 := ⟨i.val, by have := i.isLt; omega⟩

theorem memoryReady (slots : Slots) (table : Pointer) (s : GlobalState)
    (h : Ready slots table s) (i : Fin 7) :
    MemoryReady s (q slots) (tableRow table (index i)) := by
  refine ⟨h.wf, ?_, ?_⟩
  · intro j
    fin_cases j
    · exact h.scratch 6
    · exact h.scratch 3
    · exact h.scratch 2
    · exact h.scratch 1
    · exact h.scratch 0
    · exact h.scratch 4
    · exact h.tableBuffer.slice (160*i.val) 160 (by have := i.isLt; omega)
  · intro j k he
    fin_cases j <;> fin_cases k
    · rfl
    · exact False.elim (h.separate 6 3 (by decide) he)
    · exact False.elim (h.separate 6 2 (by decide) he)
    · exact False.elim (h.separate 6 1 (by decide) he)
    · exact False.elim (h.separate 6 0 (by decide) he)
    · exact False.elim (h.separate 6 4 (by decide) he)
    · exact False.elim (h.separateTable 6 he)
    · exact False.elim (h.separate 3 6 (by decide) he)
    · rfl
    · exact False.elim (h.separate 3 2 (by decide) he)
    · exact False.elim (h.separate 3 1 (by decide) he)
    · exact False.elim (h.separate 3 0 (by decide) he)
    · exact False.elim (h.separate 3 4 (by decide) he)
    · exact False.elim (h.separateTable 3 he)
    · exact False.elim (h.separate 2 6 (by decide) he)
    · exact False.elim (h.separate 2 3 (by decide) he)
    · rfl
    · exact False.elim (h.separate 2 1 (by decide) he)
    · exact False.elim (h.separate 2 0 (by decide) he)
    · exact False.elim (h.separate 2 4 (by decide) he)
    · exact False.elim (h.separateTable 2 he)
    · exact False.elim (h.separate 1 6 (by decide) he)
    · exact False.elim (h.separate 1 3 (by decide) he)
    · exact False.elim (h.separate 1 2 (by decide) he)
    · rfl
    · exact False.elim (h.separate 1 0 (by decide) he)
    · exact False.elim (h.separate 1 4 (by decide) he)
    · exact False.elim (h.separateTable 1 he)
    · exact False.elim (h.separate 0 6 (by decide) he)
    · exact False.elim (h.separate 0 3 (by decide) he)
    · exact False.elim (h.separate 0 2 (by decide) he)
    · exact False.elim (h.separate 0 1 (by decide) he)
    · rfl
    · exact False.elim (h.separate 0 4 (by decide) he)
    · exact False.elim (h.separateTable 0 he)
    · exact False.elim (h.separate 4 6 (by decide) he)
    · exact False.elim (h.separate 4 3 (by decide) he)
    · exact False.elim (h.separate 4 2 (by decide) he)
    · exact False.elim (h.separate 4 1 (by decide) he)
    · exact False.elim (h.separate 4 0 (by decide) he)
    · rfl
    · exact False.elim (h.separateTable 4 he)
    · exact False.elim (h.separateTable 6 he.symm)
    · exact False.elim (h.separateTable 3 he.symm)
    · exact False.elim (h.separateTable 2 he.symm)
    · exact False.elim (h.separateTable 1 he.symm)
    · exact False.elim (h.separateTable 0 he.symm)
    · exact False.elim (h.separateTable 4 he.symm)
    · rfl

def result (s : GlobalState) (slots : Slots) (P C : Point) : GlobalState :=
  Add.resultState s (q slots) (slots 7) P C

/-- Store-only state transformations preserve every allocation length, even
for allocation ids that do not name a live object. -/
theorem allocationShape (s : GlobalState) (slots : Slots) (P C : Point) (id : BlockId) :
    ((result s slots P C).mem[id]?).map MemoryBlock.length =
      (s.mem[id]?).map MemoryBlock.length := by
  simp [result, Add.resultState, Add.copyInput, pipelineState, writePoint,
    storeBlocks, copyPointBytes, SerialPoint.Execution.storeAt_allocationShape]

theorem frame (s : GlobalState) (slots : Slots) (table : Pointer) (P C : Point)
    (hwf : s.WF) : Frame slots table s (result s slots P C) := by
  have hf := Add.resultState_frame s (q slots) (slots 7) P C hwf
  refine ⟨hf.wellFormed, ?_, allocationShape s slots P C, ?_⟩
  · change (s.alloc.nextFreeBlock ≤ (Add.resultState s (q slots) (slots 7) P C).alloc.nextFreeBlock)
    rw [hf.allocation]
  · intro ptr width hs _
    apply hf.read
    intro i
    rw [written_eq]
    exact hs (scratchIndex i)

theorem ready (s : GlobalState) (slots : Slots) (table : Pointer) (P C : Point)
    (h : Ready slots table s) : Ready slots table (result s slots P C) :=
  h.preserve (frame s slots table P C h.wf)

theorem result_read (s : GlobalState) (slots : Slots) (table : Pointer) (P C : Point)
    (h : Ready slots table s) :
    readBlocks (result s slots P C).mem (slots 6) = packPoint (add P C) :=
  Add.resultState_read s (q slots) (slots 7) P C (h.scratch 6)

theorem fixed_readAt (s : GlobalState) (slots : Slots) (table : Pointer) (P C : Point)
    (h : Ready slots table s) (off : BitVec 64) (width : Nat) :
    (result s slots P C).mem.readAt ((slots 7).add off) width =
      s.mem.readAt ((slots 7).add off) width := by
  apply (Add.resultState_frame s (q slots) (slots 7) P C h.wf).read
  intro i
  rw [written_eq]
  exact h.separate (scratchIndex i) 7 (by fin_cases i <;> decide)

theorem fixed_readBlocks (s : GlobalState) (slots : Slots) (table : Pointer) (P C : Point)
    (h : Ready slots table s) :
    readBlocks (result s slots P C).mem (slots 7) = readBlocks s.mem (slots 7) := by
  funext i
  simp only [readBlocks, fixed_readAt s slots table P C h]

theorem table_readAt (s : GlobalState) (slots : Slots) (table : Pointer) (P C : Point)
    (h : Ready slots table s) (off : BitVec 64) (width : Nat) :
    (result s slots P C).mem.readAt (table.add off) width = s.mem.readAt (table.add off) width := by
  apply (Add.resultState_frame s (q slots) (slots 7) P C h.wf).read
  intro i
  rw [written_eq]
  exact h.separateTable (scratchIndex i)

/-- Every record survives addition, including the current cache and records
that have not yet been overwritten by a successor iteration. -/
theorem table_readBlocks (s : GlobalState) (slots : Slots) (table : Pointer) (P C : Point)
    (h : Ready slots table s) (k : Fin 8) :
    readBlocks (result s slots P C).mem (table.add (BitVec.ofNat 64 (160*k.val))) =
      readBlocks s.mem (table.add (BitVec.ofNat 64 (160*k.val))) := by
  funext j
  simp only [readBlocks, Pointer.add_add, table_readAt s slots table P C h]

end Agave.Ed25519.Tables.Avx2Constructor.AddState

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.AddState.memoryReady,
      `Agave.Ed25519.Tables.Avx2Constructor.AddState.frame,
      `Agave.Ed25519.Tables.Avx2Constructor.AddState.ready,
      `Agave.Ed25519.Tables.Avx2Constructor.AddState.result_read,
      `Agave.Ed25519.Tables.Avx2Constructor.AddState.fixed_readBlocks,
      `Agave.Ed25519.Tables.Avx2Constructor.AddState.table_readBlocks] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"
    logInfo m!"standard-three audit passed: {endpoint}"
