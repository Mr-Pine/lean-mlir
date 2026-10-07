import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorAddState
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorLoopStore
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorArithmetic

/-! The invariant after one exact positive-add and successor-record store. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.StepState
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2FieldMul.Execution (readBlocks)
open State (Slots Ready Frame)
open Avx2PointDouble (doublePoint)
open Arithmetic (entries)
open LoopStore (record)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def added (s : GlobalState) (slots : Slots) (P : Point) (i : Fin 7) : GlobalState :=
  AddState.result s slots (doublePoint P) (entries P i.val)

def result (s : GlobalState) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7) : GlobalState :=
  LoopStore.result (added s slots P i) table i (packPoint (entries P (i.val+1)))

theorem frame (s : GlobalState) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7)
    (hs : Ready slots table s) : Frame slots table s (result s slots table P i) :=
  (AddState.frame s slots table _ _ hs.wf).trans
    (LoopStore.frame _ slots table i _ (AddState.ready s slots table _ _ hs))

theorem ready (s : GlobalState) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7)
    (hs : Ready slots table s) : Ready slots table (result s slots table P i) :=
  hs.preserve (frame s slots table P i hs)

theorem fixed (s : GlobalState) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7)
    (hs : Ready slots table s)
    (hd : readBlocks s.mem (slots 7) = packPoint (doublePoint P)) :
    readBlocks (result s slots table P i).mem (slots 7) = packPoint (doublePoint P) := by
  rw [result, added, LoopStore.fixed_readBlocks _ slots table i _ (AddState.ready s slots table _ _ hs),
    AddState.fixed_readBlocks s slots table _ _ hs, hd]

theorem completed (s : GlobalState) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7)
    (hs : Ready slots table s)
    (he : ∀ j : Fin 8, j.val ≤ i.val → readBlocks s.mem (record table j.val) =
      packPoint (entries P j.val)) :
    ∀ j : Fin 8, j.val ≤ i.val+1 →
      readBlocks (result s slots table P i).mem (record table j.val) =
        packPoint (entries P j.val) := by
  have ha := AddState.ready s slots table (doublePoint P) (entries P i.val) hs
  intro j hj
  by_cases hn : j.val = i.val+1
  · rw [hn]
    exact LoopStore.next_readBlocks _ table i _ ha.tableBuffer
  · have hj' : j.val ≤ i.val := by omega
    rw [result, added, LoopStore.prior_readBlocks _ table i _ ha.tableBuffer j hj']
    exact (AddState.table_readBlocks s slots table _ _ hs j).trans (he j hj')

end Agave.Ed25519.Tables.Avx2Constructor.StepState
