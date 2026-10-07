import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorStepState
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorLoopRegisters

/-! One complete original loop block, using the actual multiplication helper. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Step
open LeanMLIR.RIR Avx2PointAdd Avx2PointAdd.Phases
open Avx2FieldMul.Execution (readBlocks)
open Avx2PointDouble (doublePoint doublePoint_reduced)
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open State (Slots)
open Arithmetic (entries)
open LoopStore (record)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def addedEnv (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7) : ⟪kernel.Γ⟫ :=
  Add.bodyEnv9 E (AddState.q slots) table (AddState.index i) (doublePoint P) (entries P i.val)

def cachedEnv (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7) : ⟪kernel.Γ⟫ :=
  CacheCombined.successorResult (addedEnv E slots table P i)

def tailEnv (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7) : ⟪kernel.Γ⟫ :=
  LoopTail.result (cachedEnv E slots table P i) (record table i.val)
    (packPoint (entries P (i.val+1))) i

def resultEnv (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7) : ⟪kernel.Γ⟫ :=
  if i.val = 6 then tailEnv E slots table P i
  else (tailEnv E slots table P i)[%803 := .value (BitVec.ofNat 64 (i.val+1))]

theorem cache_frame (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7) :
    RegisterFrame 804 kernel.Γ.n E (cachedEnv E slots table P i) :=
  (Add.body_frame E (AddState.q slots) table (AddState.index i) _ _).trans
    ((CacheCombined.successor_frame _).weaken (by decide) (by decide))

theorem cached_input (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7)
    (hP : pointReduced P) (hr : LoopRegisters.Ready slots table E) :
    LoopTail.input (cachedEnv E slots table P i) (record table i.val)
      (packPoint (entries P (i.val+1))) i = cachedEnv E slots table P i := by
  have hr1 := hr.preserve ((Add.body_frame E (AddState.q slots) table (AddState.index i)
    (doublePoint P) (entries P i.val)).weaken (by decide) (by rfl))
  have hr2 := hr.preserve ((cache_frame E slots table P i).weaken (by decide) (by rfl))
  have hv : ∀ k, CacheCombined.successorInputReads (addedEnv E slots table P i) k =
      Ty.wrap (t := .vec 8 32) (packPoint (add (doublePoint P) (entries P i.val)) k) := by
    have hp := Add.body_packed E (AddState.q slots) table (AddState.index i)
      (doublePoint P) (entries P i.val)
    intro k
    fin_cases k
    · exact hp.1
    · exact hp.2.1
    · exact hp.2.2.1
    · exact hp.2.2.2.1
    · exact hp.2.2.2.2
  have hout := CacheCombined.successor_point (addedEnv E slots table P i) hr1.constants.cache
    (add_reduced (doublePoint_reduced hP) (pointReduced_wide (Arithmetic.entries_reduced hP i.val))) hv
  have hcur := Add.body_cursor E (AddState.q slots) table (AddState.index i)
    (doublePoint P) (entries P i.val)
  have h804 : (cachedEnv E slots table P i).read (%804) =
      .value (BitVec.ofNat 64 (i.val+1)) :=
    ((CacheCombined.successor_frame _).read (%804) (by decide)).trans hcur.1
  have h805 : (cachedEnv E slots table P i).read (%805) = .value (record table i.val) :=
    ((CacheCombined.successor_frame _).read (%805) (by decide)).trans hcur.2
  exact hr2.tail_input i h804 h805 hout

theorem result_frame (E : ⟪kernel.Γ⟫) (slots : Slots) (table : Pointer) (P : Point) (i : Fin 7)
    (hP : pointReduced P) (hr : LoopRegisters.Ready slots table E) :
    RegisterFrame 803 kernel.Γ.n E (resultEnv E slots table P i) := by
  have ht : RegisterFrame 1026 kernel.Γ.n (cachedEnv E slots table P i)
      (tailEnv E slots table P i) := by
    unfold tailEnv LoopTail.result
    rw [cached_input E slots table P i hP hr]
    iterate 6 apply RegisterFrame.write (hd := by decide)
    exact RegisterFrame.refl _ _ _
  have hf := ((cache_frame E slots table P i).weaken (lo' := 803) (hi' := kernel.Γ.n)
    (by decide) (by rfl)).trans (ht.weaken (by decide) (by rfl))
  unfold resultEnv
  split
  · exact hf
  · exact hf.write _ _ (by decide)

theorem body (E : ⟪kernel.Γ⟫) (s : GlobalState) (slots : Slots) (table : Pointer)
    (P : Point) (i : Fin 7) (hP : pointReduced P)
    (hr : LoopRegisters.Ready slots table E)
    (hi : E.read (%803) = .value (BitVec.ofNat 64 i.val))
    (hs : State.Ready slots table s)
    (hd : readBlocks s.mem (slots 7) = packPoint (doublePoint P))
    (he : readBlocks s.mem (record table i.val) = packPoint (entries P i.val)) :
    (kernel.bb2 Double.actual).runBodyFrom E 0 s =
      .value (tailEnv E slots table P i, StepState.result s slots table P i) := by
  have hadd := Add.body_actual Double.actual.call0 E s (AddState.q slots) (slots 7) table
    (AddState.index i) 1280 (doublePoint P) (entries P i.val) (hr.add_input i hi)
    (AddState.memoryReady slots table s hs i) hs.tableBuffer
    (by have := i.isLt; simp only [AddState.index]; omega) he (hs.scratch 7) hd
    (hs.separate 3 7 (by decide)) (doublePoint_reduced hP) (Arithmetic.entries_reduced hP i.val)
  change (kernel.bb2 Double.actual).runBodyFrom E 0 s =
    (kernel.bb2 Double.actual).runBodyFrom (addedEnv E slots table P i) 105
      (StepState.added s slots P i) at hadd
  rw [hadd, CacheCombined.successor_continue]
  have htail := LoopTail.body Double.actual (cachedEnv E slots table P i) (record table i.val)
    (packPoint (entries P (i.val+1))) i (StepState.added s slots P i)
    (LoopTail.records (AddState.ready s slots table _ _ hs).tableBuffer i)
  rw [cached_input E slots table P i hP hr] at htail
  exact htail

theorem block_step (slots : Slots) (table : Pointer) (P : Point) (hP : pointReduced P)
    (i : Fin 7) (E : ⟪kernel.Γ⟫) (s : GlobalState)
    (hr : LoopRegisters.Ready slots table E)
    (hi : E.read (%803) = .value (BitVec.ofNat 64 i.val))
    (hs : State.Ready slots table s)
    (hd : readBlocks s.mem (slots 7) = packPoint (doublePoint P))
    (he : ∀ j : Fin 8, j.val ≤ i.val →
      readBlocks s.mem (record table j.val) = packPoint (entries P j.val)) :
    ∃ F t,
      (kernel.bb2 Double.actual).run kernel.blockParams E s =
        .value ((F, .inr (if i.val = 6 then 1 else 2)), t) ∧
      RegisterFrame 803 kernel.Γ.n E F ∧ State.Frame slots table s t ∧
      LoopRegisters.Ready slots table F ∧ State.Ready slots table t ∧
      readBlocks t.mem (slots 7) = packPoint (doublePoint P) ∧
      (∀ j : Fin 8, j.val ≤ i.val+1 →
        readBlocks t.mem (record table j.val) = packPoint (entries P j.val)) ∧
      (i.val < 6 → F.read (%803) = .value (BitVec.ofNat 64 (i.val+1))) := by
  have hbody := body E s slots table P i hP hr hi hs hd
    (he ⟨i.val,by have := i.isLt; omega⟩ (le_refl _))
  have hf := result_frame E slots table P i hP hr
  refine ⟨resultEnv E slots table P i, StepState.result s slots table P i, ?_, hf,
    StepState.frame s slots table P i hs, hr.preserve hf,
    StepState.ready s slots table P i hs, StepState.fixed s slots table P i hs hd,
    StepState.completed s slots table P i hs he, ?_⟩
  · rw [BasicBlock.run, EffectM.bind_eq]
    change ((kernel.bb2 Double.actual).runBodyFrom E 0 s >>= fun es =>
      (kernel.bb2 Double.actual).exit.run kernel.blockParams es.1 es.2) = _
    rw [hbody, PoisonOr.value_bind]
    exact LoopTail.exit Double.actual (cachedEnv E slots table P i) (record table i.val)
      (packPoint (entries P (i.val+1))) i _
  · intro hi6
    simp [resultEnv, show i.val ≠ 6 by omega, mlir_env]

end Agave.Ed25519.Tables.Avx2Constructor.Step
