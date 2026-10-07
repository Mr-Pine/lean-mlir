import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorState
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorBroadcast
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorDouble
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorArithmetic

/-! Memory invariant established by the exact initial broadcast and doubling. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.PrefixState
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2FieldMul.Execution (readBlocks)
open State (Slots Frame Ready)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def result (s : GlobalState) (slots : Slots) (table : Pointer) (P : Point) : GlobalState :=
  Double.finalState (Broadcast.state s table (packPoint (CacheArithmetic.cache P)) 40) slots P

theorem broadcast_frame (s : GlobalState) (slots : Slots) (table : Pointer)
    (P : Point) (hwf : s.WF) :
    Frame slots table s (Broadcast.state s table (packPoint (CacheArithmetic.cache P)) 40) :=
  ⟨Broadcast.state_wf hwf _ _ _, le_refl _, Broadcast.memory_shape _ _ _ _,
    fun q bits _ ht => Broadcast.memory_read_ne _ _ _ _ q bits ht⟩

theorem double_frame (s : GlobalState) (slots : Slots) (table : Pointer)
    (P : Point) (hwf : s.WF) : Frame slots table s (Double.finalState s slots P) := by
  refine ⟨Double.finalState_wf s slots P hwf, ?_, Double.finalState_shape s slots P, ?_⟩
  · rw [Double.finalState_counter]
  · intro q bits hs _
    exact Double.finalState_read s slots P q bits (hs 5) (hs 4) (hs 7)

theorem frame (s : GlobalState) (slots : Slots) (table : Pointer)
    (P : Point) (hwf : s.WF) : Frame slots table s (result s slots table P) :=
  (broadcast_frame s slots table P hwf).trans
    (double_frame _ slots table P (Broadcast.state_wf hwf _ _ _))

theorem ready (s : GlobalState) (slots : Slots) (table : Pointer)
    (P : Point) (hs : Ready slots table s) : Ready slots table (result s slots table P) :=
  hs.preserve (frame s slots table P hs.wf)

theorem fixed (s : GlobalState) (slots : Slots) (table : Pointer)
    (P : Point) (hs : Ready slots table s) :
    readBlocks (result s slots table P).mem (slots 7) = packPoint (Avx2PointDouble.doublePoint P) :=
  Double.finalState_readback _ slots P (Broadcast.memory_live (hs.scratch 7) _ _ _)

theorem entries (s : GlobalState) (slots : Slots) (table : Pointer)
    (P : Point) (hs : Ready slots table s) (k : Fin 8) :
    readBlocks (result s slots table P).mem (table.add (BitVec.ofNat 64 (160*k.val))) =
      packPoint (Arithmetic.entries P 0) := by
  have hread (q : Pointer) (bits : Nat) (hq : q.id = table.id) :
      (result s slots table P).mem.readAt q bits =
        (Broadcast.state s table (packPoint (CacheArithmetic.cache P)) 40).mem.readAt q bits :=
    Double.finalState_read _ slots P q bits
      (by simpa [hq] using hs.separateTable 5)
      (by simpa [hq] using hs.separateTable 4)
      (by simpa [hq] using hs.separateTable 7)
  have hr : readBlocks (result s slots table P).mem
      (table.add (BitVec.ofNat 64 (160*k.val))) =
      readBlocks (Broadcast.state s table (packPoint (CacheArithmetic.cache P)) 40).mem
        (table.add (BitVec.ofNat 64 (160*k.val))) := by
    funext i
    unfold readBlocks
    rw [hread _ 256 (by rfl)]
  rw [hr]
  exact Broadcast.readback s.mem table _ hs.tableBuffer k

end Agave.Ed25519.Tables.Avx2Constructor.PrefixState
