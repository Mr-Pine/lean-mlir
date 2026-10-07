import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorPrefixState
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorLoopRegisters

/-! Composition of the exact constructor entry through its first loop block. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Prefix
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open State (Slots)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def broadcastEnv (E : ⟪kernel.Γ⟫) (table : Pointer) : ⟪kernel.Γ⟫ :=
  Broadcast.resultEnv (CacheCombined.initialResult E) table

def resultEnv (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) : ⟪kernel.Γ⟫ :=
  Double.resultEnv (broadcastEnv E table) slots P

theorem broadcast_frame (E : ⟪kernel.Γ⟫) (table : Pointer) :
    RegisterFrame 505 689 E (broadcastEnv E table) :=
  ((CacheCombined.initial_frame E).weaken (by decide) (by decide)).trans
    ((Broadcast.resultEnv_frame _ table).weaken (by decide) (by decide))

theorem result_frame (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) :
    RegisterFrame 505 kernel.Γ.n E (resultEnv E slots table P) :=
  ((broadcast_frame E table).weaken (by decide) (by decide)).trans
    ((Double.resultEnv_frame _ slots P).weaken (by decide) (by rfl))

theorem result_ready (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point)
    (hr : LoopRegisters.BaseReady slots table E) :
    LoopRegisters.Ready slots table (resultEnv E slots table P) :=
  LoopRegisters.double_ready
    (hr.preserve ((broadcast_frame E table).weaken (by decide) (by decide))) P

theorem body (E : ⟪kernel.Γ⟫) (s : GlobalState) (slots : Slots)
    (table : Pointer) (P : Point) (hP : pointReduced P)
    (hr : LoopRegisters.BaseReady slots table E) (hs : State.Ready slots table s)
    (hin : ∀ k, CacheCombined.initialInputReads E k =
      Ty.wrap (t := .vec 8 32) (packPoint P k)) :
    (kernel.bb0 Double.actual).runBodyFrom E 505 s =
      .value (resultEnv E slots table P, PrefixState.result s slots table P) := by
  have hc := CacheCombined.initial_point E hr.constants.cache hP hin
  have hcr : Broadcast.Reads (CacheCombined.initialResult E) table
      (packPoint (CacheArithmetic.cache P)) :=
    ⟨((CacheCombined.initial_frame E).read (%360) (by decide)).trans hr.tableRead,
      hc 0, hc 1, hc 2, hc 3, hc 4⟩
  have hrb := hr.preserve ((broadcast_frame E table).weaken (by decide) (by decide))
  have hd : Double.inputReads (broadcastEnv E table) (packPoint P) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact ((broadcast_frame E table).read (%504) (by decide)).trans (hin 0)
    · exact ((broadcast_frame E table).read (%485) (by decide)).trans (hin 1)
    · exact ((broadcast_frame E table).read (%489) (by decide)).trans (hin 2)
    · exact ((broadcast_frame E table).read (%493) (by decide)).trans (hin 3)
    · exact ((broadcast_frame E table).read (%497) (by decide)).trans (hin 4)
  rw [CacheCombined.initial_continue, Broadcast.body_continue Double.actual _ s table
    (packPoint (CacheArithmetic.cache P)) hs.tableBuffer hcr]
  exact Double.body_actual _ slots _ P (Broadcast.state_wf hs.wf _ _ _)
    (fun i => Broadcast.memory_live (hs.scratch i) _ _ _)
    (hs.separate 5 4 (by decide)) hP hrb.constants.double hrb.initial hd

/-- Exact entry block and branch, with the verifier's full Tight input bound. -/
theorem entry_run (E : ⟪kernel.Γ⟫) (s : GlobalState) (a : Pointer)
    (hwf : s.WF) (ha : NAF.Memory.Buffer s.mem a 160)
    (htight : DoubleBase.ExecutionAvx2.serialLimbsBounded s a)
    (harg : E.read (%arg1) = .value a) :
    let P := Normalization.normalizedPoint (Loads.point s.mem a)
    ∃ F t,
      (kernel Double.actual).runFrom E 0 s = (kernel Double.actual).runFrom F 2 t ∧
      RegisterFrame 0 kernel.Γ.n E F ∧
      State.Frame (State.slots s) (Stack.pointer s 8) (Stack.state s 9) t ∧
      LoopRegisters.Ready (State.slots s) (Stack.pointer s 8) F ∧
      F.read (%803) = .value 0#64 ∧
      State.Ready (State.slots s) (Stack.pointer s 8) t ∧
      pointReduced P ∧ pointValue P = Conformance.BackendExecution.readPoint s a ∧
      Avx2FieldMul.Execution.readBlocks t.mem ((State.slots s) 7) =
        packPoint (Avx2PointDouble.doublePoint P) ∧
      Avx2FieldMul.Execution.readBlocks t.mem (Stack.pointer s 8) =
        packPoint (Arithmetic.entries P 0) := by
  let P := Normalization.normalizedPoint (Loads.point s.mem a)
  let M := Entry.result E s a
  let B := resultEnv M (State.slots s) (Stack.pointer s 8) P
  let F := LoopRegisters.entryPhi B
  let t := PrefixState.result (Stack.state s 9) (State.slots s) (Stack.pointer s 8) P
  obtain ⟨hprefix,hin,hP,hvalue⟩ := Entry.tight_run Double.actual E s a hwf ha harg htight
  have hr := LoopRegisters.entry_ready E s a
  have hs := State.stack_ready s hwf
  have hb := body M (Stack.state s 9) (State.slots s) (Stack.pointer s 8) P hP hr hs hin
  have hrb := result_ready M (State.slots s) (Stack.pointer s 8) P hr
  have hbody : (kernel.bb0 Double.actual).runBodyFrom E 0 s = .value (B,t) := by
    rw [Entry.continue_run Double.actual E s a hwf ha harg]
    exact hb
  have hblock : (kernel.bb0 Double.actual).run kernel.blockParams E s =
      .value ((F,.inr 2),t) := by
    rw [BasicBlock.run, EffectM.bind_eq]
    change ((kernel.bb0 Double.actual).runBodyFrom E 0 s >>= fun es =>
      (kernel.bb0 Double.actual).exit.run kernel.blockParams es.1 es.2) = _
    rw [hbody, PoisonOr.value_bind]
    exact LoopRegisters.entry_exit Double.actual B t hrb
  have hf : RegisterFrame 0 kernel.Γ.n E F :=
    ((Constants.register_frame E).weaken (by decide) (by decide)).trans
      (((EntryFrames.result_frame E s a).weaken (by decide) (by decide)).trans
        (((result_frame M (State.slots s) (Stack.pointer s 8) P).weaken (by decide) (by rfl)).trans
          ((LoopRegisters.entryPhi_frame B).weaken (by decide) (by rfl))))
  refine ⟨F,t,?_,hf,PrefixState.frame _ _ _ P hs.wf,
    LoopRegisters.entryPhi_ready hrb,LoopRegisters.entryPhi_cursor B,
    PrefixState.ready _ _ _ P hs,hP,hvalue,PrefixState.fixed _ _ _ P hs,?_⟩
  · rw [Func.runFrom_eq,
      show (kernel Double.actual).blocks 0 = kernel.bb0 Double.actual from rfl,hblock]
    rfl
  · simpa using PrefixState.entries (Stack.state s 9) (State.slots s) (Stack.pointer s 8) P hs 0

end Agave.Ed25519.Tables.Avx2Constructor.Prefix
