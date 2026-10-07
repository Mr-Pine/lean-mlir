import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2DalekAdapterFrame
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointAdd.PhasePipeline
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.CFGExecution

/-! The arithmetic loop writes only the first twenty-seven private stack
objects. Caller objects, the cached table, and both NAF arrays retain their
actual bytes throughout each concrete addition and doubling store trace. -/
namespace Agave.Ed25519.DoubleBase.ExecutionAvx2
open LeanMLIR.RIR
open Reduce64.Execution (SmallRange)

structure LoopPrivateFrame (initial before after : GlobalState) : Prop where
  wellFormed : after.WF
  live : ∀ (q : Pointer) (bytes : Nat),
    SmallRange before.mem q bytes → SmallRange after.mem q bytes
  read : ∀ (q : Pointer) (width : Nat),
    (q.id.id < initial.alloc.nextFreeBlock ∨
      initial.alloc.nextFreeBlock + 27 ≤ q.id.id) →
    after.mem.readAt q width = before.mem.readAt q width

theorem LoopPrivateFrame.refl (hwf : state.WF) : LoopPrivateFrame initial state state :=
  ⟨hwf, fun _ _ h => h, fun _ _ _ => rfl⟩

theorem LoopPrivateFrame.trans (h : LoopPrivateFrame initial before middle)
    (h' : LoopPrivateFrame initial middle after) : LoopPrivateFrame initial before after :=
  ⟨h'.wellFormed, fun q bytes hq => h'.live q bytes (h.live q bytes hq),
    fun q width hq => (h'.read q width hq).trans (h.read q width hq)⟩

private theorem private_ne_protected {initial : GlobalState} {p q : Pointer}
    (hp : initial.alloc.nextFreeBlock ≤ p.id.id ∧
      p.id.id < initial.alloc.nextFreeBlock + 27)
    (hq : q.id.id < initial.alloc.nextFreeBlock ∨
      initial.alloc.nextFreeBlock + 27 ≤ q.id.id) : p.id ≠ q.id := by
  intro he
  have hid := congrArg (fun id => id.id) he
  omega

/-- The complete point-add store frame writes only arithmetic scratch. -/
theorem LoopPrivateFrame.of_pointAdd
    (hf : Avx2PointAdd.Phases.OutputFrame scratch before after)
    (hprivate : ∀ k, initial.alloc.nextFreeBlock ≤ (scratch.written k).id.id ∧
      (scratch.written k).id.id < initial.alloc.nextFreeBlock + 27) :
    LoopPrivateFrame initial before after := by
  refine ⟨hf.wellFormed, hf.live, ?_⟩
  intro q width hq
  exact hf.read q width (fun k => private_ne_protected (hprivate k) hq)

/-- All seven stages of the actual addition trace preserve the same protected objects. -/
theorem pipelineState_loopPrivateFrame (initial before : GlobalState)
    (scratch : Avx2PointAdd.Phases.Scratch) (negative : Bool)
    (P C : Avx2PointAdd.Point) (stage : Fin 8) (hwf : before.WF)
    (hprivate : ∀ k, initial.alloc.nextFreeBlock ≤ (scratch.written k).id.id ∧
      (scratch.written k).id.id < initial.alloc.nextFreeBlock + 27) :
    LoopPrivateFrame initial before
      (Avx2PointAdd.Phases.pipelineState before scratch negative P C stage) :=
  LoopPrivateFrame.of_pointAdd
    (Avx2PointAdd.Phases.pipelineState_frame before scratch negative P C hwf stage) hprivate

/-- The doubling block's real scratch objects are stack slots 19, 18 and 26. -/
theorem resultState_loopPrivateFrame (initial before : GlobalState)
    (P : Avx2PointAdd.Point) (hwf : before.WF) :
    LoopPrivateFrame initial before
      (Avx2PointDouble.CFG.resultState before (avx2StackPtr initial 19)
        (avx2StackPtr initial 18) (avx2StackPtr initial 26) P) := by
  refine ⟨Avx2PointDouble.CFG.resultState_wf before _ _ _ P hwf,
    fun q bytes hq => Avx2PointDouble.CFG.resultState_live before _ _ _ P hq, ?_⟩
  intro q width hq
  apply Avx2PointDouble.CFG.resultState_read
  all_goals apply private_ne_protected (initial := initial) ?_ hq
  all_goals
    simp only [avx2StackPtr, GlobalState.allocaPtr_id_id, avx2Stack_nextFreeBlock]
    omega

/-- An arithmetic scratch frame transports the already established caller frame. -/
theorem CallerFrame.of_loopPrivateFrame (h : CallerFrame initial before out)
    (hf : LoopPrivateFrame initial before after) : CallerFrame initial after out := by
  refine ⟨hf.wellFormed, fun q bytes hq => hf.live q bytes (h.live q bytes hq), ?_⟩
  intro q width hq hd
  exact (hf.read q width (Or.inl hq)).trans (h.read q width hq hd)

/-- Exact SIMD readback is preserved for every protected allocation. -/
theorem LoopPrivateFrame.readBlocks (h : LoopPrivateFrame initial before after)
    (hp : ptr.id.id < initial.alloc.nextFreeBlock ∨
      initial.alloc.nextFreeBlock + 27 ≤ ptr.id.id) :
    Avx2FieldMul.Execution.readBlocks after.mem ptr =
      Avx2FieldMul.Execution.readBlocks before.mem ptr := by
  funext i
  unfold Avx2FieldMul.Execution.readBlocks
  rw [h.read _ 256 (by simpa using hp)]

theorem LoopPrivateFrame.packedPoint (h : LoopPrivateFrame initial before after)
    (hp : ptr.id.id < initial.alloc.nextFreeBlock ∨
      initial.alloc.nextFreeBlock + 27 ≤ ptr.id.id) :
    packedPoint after.mem ptr = packedPoint before.mem ptr := by
  simp only [Agave.Ed25519.DoubleBase.ExecutionAvx2.packedPoint, h.readBlocks hp]

end Agave.Ed25519.DoubleBase.ExecutionAvx2

/-- info: AVX2 private-scratch frame endpoints use only standard Lean axioms. -/
#guard_msgs in
open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let endpoints : List Name := [
    ``Agave.Ed25519.DoubleBase.ExecutionAvx2.LoopPrivateFrame.of_pointAdd,
    ``Agave.Ed25519.DoubleBase.ExecutionAvx2.pipelineState_loopPrivateFrame,
    ``Agave.Ed25519.DoubleBase.ExecutionAvx2.resultState_loopPrivateFrame,
    ``Agave.Ed25519.DoubleBase.ExecutionAvx2.CallerFrame.of_loopPrivateFrame,
    ``Agave.Ed25519.DoubleBase.ExecutionAvx2.LoopPrivateFrame.readBlocks,
    ``Agave.Ed25519.DoubleBase.ExecutionAvx2.LoopPrivateFrame.packedPoint]
  for endpoint in endpoints do
    for dependency in (← collectAxioms endpoint) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {endpoint}"
  logInfo "AVX2 private-scratch frame endpoints use only standard Lean axioms."
