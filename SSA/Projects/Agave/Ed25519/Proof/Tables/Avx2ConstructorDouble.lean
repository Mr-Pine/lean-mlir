import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorDoubleExecution
import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorConstantValues
import SSA.Projects.Agave.Ed25519.Proof.SerialPoint.CallMemory

/-! Exact constructor entry suffix, including its initial double and every
saved loop pointer. The public actual-body endpoint fixes both field callees
to their separately checked imported implementations. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Double
open LeanMLIR.RIR Avx2PointDouble
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
open Avx2PointAdd.Phases (packPoint readBlocks_storeBlocks storeBlocks_live)
open Avx2FieldMul.Execution (readBlocks storeBlocks)
open Reduce64.Execution (SmallRange)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

abbrev Slots := Fin 8 → Pointer

theorem constants_ready (E : ⟪kernel.Γ⟫) :
    Constants (Avx2Constructor.Constants.result E) := by
  exact ⟨Avx2Constructor.Constants.read_4 E, Avx2Constructor.Constants.read_8 E,
    Avx2Constructor.Constants.read_12 E, Avx2Constructor.Constants.read_16 E,
    Avx2Constructor.Constants.read_31 E,
    by simpa [Ty.wrap] using Avx2Constructor.Constants.read_230 E,
    Avx2Constructor.Constants.read_247 E, Avx2Constructor.Constants.read_264 E,
    Avx2Constructor.Constants.read_281 E, Avx2Constructor.Constants.read_298 E,
    Avx2Constructor.Constants.read_315 E⟩

structure InitialPointers (E : ⟪kernel.Γ⟫) (slots : Slots) : Prop where
  r352 : E.read (%352) = .value (slots 0)
  r353 : E.read (%353) = .value (slots 1)
  r354 : E.read (%354) = .value (slots 2)
  r355 : E.read (%355) = .value (slots 3)
  r356 : E.read (%356) = .value (slots 4)
  r357 : E.read (%357) = .value (slots 5)
  r358 : E.read (%358) = .value (slots 6)
  r359 : E.read (%359) = .value (slots 7)

structure SetupPointers (E : ⟪kernel.Γ⟫) (slots : Slots) : Prop where
  r787 : E.read (%787) = .value ((slots 3).add 32#64)
  r788 : E.read (%788) = .value ((slots 3).add 64#64)
  r789 : E.read (%789) = .value ((slots 3).add 96#64)
  r790 : E.read (%790) = .value ((slots 3).add 128#64)
  r791 : E.read (%791) = .value ((slots 1).add 32#64)
  r792 : E.read (%792) = .value ((slots 1).add 64#64)
  r793 : E.read (%793) = .value ((slots 1).add 96#64)
  r794 : E.read (%794) = .value ((slots 1).add 128#64)
  r795 : E.read (%795) = .value ((slots 0).add 32#64)
  r796 : E.read (%796) = .value ((slots 0).add 64#64)
  r797 : E.read (%797) = .value ((slots 0).add 96#64)
  r798 : E.read (%798) = .value ((slots 0).add 128#64)
  r799 : E.read (%799) = .value ((slots 6).add 32#64)
  r800 : E.read (%800) = .value ((slots 6).add 64#64)
  r801 : E.read (%801) = .value ((slots 6).add 96#64)
  r802 : E.read (%802) = .value ((slots 6).add 128#64)

theorem InitialPointers.frame {E F : ⟪kernel.Γ⟫} (h : InitialPointers E slots)
    (hf : RegisterFrame 689 kernel.Γ.n E F) : InitialPointers F slots := by
  exact ⟨(hf.read (%352) (by decide)).trans h.r352,
    (hf.read (%353) (by decide)).trans h.r353,
    (hf.read (%354) (by decide)).trans h.r354,
    (hf.read (%355) (by decide)).trans h.r355,
    (hf.read (%356) (by decide)).trans h.r356,
    (hf.read (%357) (by decide)).trans h.r357,
    (hf.read (%358) (by decide)).trans h.r358,
    (hf.read (%359) (by decide)).trans h.r359⟩

def setupEnv (E : ⟪kernel.Γ⟫) (slots : Slots) : ⟪kernel.Γ⟫ :=
  E[%787 := .value ((slots 3).add 32#64),
    %788 := .value ((slots 3).add 64#64),
    %789 := .value ((slots 3).add 96#64),
    %790 := .value ((slots 3).add 128#64),
    %791 := .value ((slots 1).add 32#64),
    %792 := .value ((slots 1).add 64#64),
    %793 := .value ((slots 1).add 96#64),
    %794 := .value ((slots 1).add 128#64),
    %795 := .value ((slots 0).add 32#64),
    %796 := .value ((slots 0).add 64#64),
    %797 := .value ((slots 0).add 96#64),
    %798 := .value ((slots 0).add 128#64),
    %799 := .value ((slots 6).add 32#64),
    %800 := .value ((slots 6).add 64#64),
    %801 := .value ((slots 6).add 96#64),
    %802 := .value ((slots 6).add 128#64)]

theorem setup_frame (E : ⟪kernel.Γ⟫) (slots : Slots) :
    RegisterFrame 787 kernel.Γ.n E (setupEnv E slots) := by
  unfold setupEnv
  iterate 16 apply RegisterFrame.write (hd := by decide)
  exact RegisterFrame.refl _ _ _

theorem setup_pointers (E : ⟪kernel.Γ⟫) (slots : Slots) :
    SetupPointers (setupEnv E slots) slots := by
  constructor <;> simp [setupEnv, mlir_env]

theorem setup_slice (p : Primitives) (E : ⟪kernel.Γ⟫) (slots : Slots)
    (s : GlobalState) (hs : ∀ i, SmallRange s.mem (slots i) 160)
    (hp : InitialPointers E slots) :
    (kernel.bb0 p).runBodyFrom E 847 s = .value (setupEnv E slots, s) := by
  have h3_0 := (hs 3).gep (k := 32) (by decide)
  have h3_1 := (hs 3).gep (k := 64) (by decide)
  have h3_2 := (hs 3).gep (k := 96) (by decide)
  have h3_3 := (hs 3).gep (k := 128) (by decide)
  have h1_0 := (hs 1).gep (k := 32) (by decide)
  have h1_1 := (hs 1).gep (k := 64) (by decide)
  have h1_2 := (hs 1).gep (k := 96) (by decide)
  have h1_3 := (hs 1).gep (k := 128) (by decide)
  have h0_0 := (hs 0).gep (k := 32) (by decide)
  have h0_1 := (hs 0).gep (k := 64) (by decide)
  have h0_2 := (hs 0).gep (k := 96) (by decide)
  have h0_3 := (hs 0).gep (k := 128) (by decide)
  have h6_0 := (hs 6).gep (k := 32) (by decide)
  have h6_1 := (hs 6).gep (k := 64) (by decide)
  have h6_2 := (hs 6).gep (k := 96) (by decide)
  have h6_3 := (hs 6).gep (k := 128) (by decide)
  norm_num only [Nat.cast_ofNat] at h3_0 h3_1 h3_2 h3_3 h1_0 h1_1 h1_2 h1_3 h0_0 h0_1 h0_2 h0_3 h6_0 h6_1 h6_2 h6_3
  simp [BasicBlock.runBodyFrom, kernel.bb0, setupEnv, List.foldlM_cons, List.foldlM_nil,
    Instr.run, EffectM.bind_eq, EffectM.pure_eq, GepIndex.inboundsOffset, mlir_env,
    hp.r355, hp.r353, hp.r352, hp.r358,
    h3_0, h3_1, h3_2, h3_3, h1_0, h1_1, h1_2, h1_3, h0_0, h0_1, h0_2, h0_3, h6_0, h6_1, h6_2, h6_3]

def resultEnv (E : ⟪kernel.Γ⟫) (slots : Slots) (P : Avx2PointAdd.Point) : ⟪kernel.Γ⟫ :=
  setupEnv (coreResultEnv E (slots 5) (slots 4) P) slots

def finalState (s : GlobalState) (slots : Slots) (P : Avx2PointAdd.Point) : GlobalState :=
  Avx2PointDouble.CFG.resultState s (slots 5) (slots 4) (slots 7) P

theorem resultEnv_frame (E : ⟪kernel.Γ⟫) (slots : Slots) (P : Avx2PointAdd.Point) :
    RegisterFrame 689 kernel.Γ.n E (resultEnv E slots P) :=
  (coreResultEnv_frame E _ _ P).trans ((setup_frame _ slots).weaken (by decide) (by rfl))

theorem resultEnv_pointers (E : ⟪kernel.Γ⟫) (slots : Slots) (P : Avx2PointAdd.Point) :
    SetupPointers (resultEnv E slots P) slots := setup_pointers _ _

theorem finalState_readback (s : GlobalState) (slots : Slots) (P : Avx2PointAdd.Point)
    (hr : SmallRange s.mem (slots 7) 160) :
    readBlocks (finalState s slots P).mem (slots 7) = packPoint (doublePoint P) := by
  apply readBlocks_storeBlocks
  exact storeBlocks_live (storeBlocks_live (storeBlocks_live (storeBlocks_live hr _ _) _ _) _ _) _ _

theorem finalState_wf (s : GlobalState) (slots : Slots) (P : Avx2PointAdd.Point)
    (hwf : s.WF) : (finalState s slots P).WF :=
  Avx2PointDouble.CFG.resultState_wf s _ _ _ P hwf

theorem finalState_live (s : GlobalState) (slots : Slots) (P : Avx2PointAdd.Point)
    (h : SmallRange s.mem q bytes) : SmallRange (finalState s slots P).mem q bytes :=
  Avx2PointDouble.CFG.resultState_live s _ _ _ P h

theorem finalState_read (s : GlobalState) (slots : Slots) (P : Avx2PointAdd.Point)
    (q : Pointer) (width : Nat)
    (ha : (slots 5).id ≠ q.id) (hb : (slots 4).id ≠ q.id) (hr : (slots 7).id ≠ q.id) :
    (finalState s slots P).mem.readAt q width = s.mem.readAt q width :=
  Avx2PointDouble.CFG.resultState_read s _ _ _ q P width ha hb hr

theorem finalState_counter (s : GlobalState) (slots : Slots) (P : Avx2PointAdd.Point) :
    (finalState s slots P).alloc = s.alloc := by
  simp only [finalState, Avx2PointDouble.CFG.resultState, Avx2PointDouble.CFG.leftState,
    Avx2PointDouble.CFG.rightState, Avx2PointDouble.CFG.squaredState,
    Avx2PointDouble.CFG.preparedState]

theorem finalState_shape (s : GlobalState) (slots : Slots) (P : Avx2PointAdd.Point) (id : BlockId) :
    ((finalState s slots P).mem[id]?).map MemoryBlock.length = (s.mem[id]?).map MemoryBlock.length := by
  simp only [finalState, Avx2PointDouble.CFG.resultState, Avx2PointDouble.CFG.leftState,
    Avx2PointDouble.CFG.rightState, Avx2PointDouble.CFG.squaredState,
    Avx2PointDouble.CFG.preparedState, storeBlocks, SerialPoint.Execution.storeAt_allocationShape]

/-- Exact remaining entry body, ending immediately before the original branch. -/
theorem body (p : Primitives) (E : ⟪kernel.Γ⟫) (slots : Slots) (s : GlobalState)
    (P : Avx2PointAdd.Point)
    (hsquare : DoubleBase.ExecutionAvx2.SquareContract p.call0)
    (hmul : DoubleBase.ExecutionAvx2.MulContract p.call1)
    (hwf : s.WF) (hs : ∀ i, SmallRange s.mem (slots i) 160)
    (hab : (slots 5).id ≠ (slots 4).id)
    (hp : Avx2PointAdd.pointReduced P) (hc : Constants E)
    (hptr : InitialPointers E slots) (hinput : inputReads E (packPoint P)) :
    (kernel.bb0 p).runBodyFrom E 729 s = .value (resultEnv E slots P, finalState s slots P) := by
  rw [body_continue p E s (slots 5) (slots 4) (slots 7) P hsquare hmul hwf
    (hs 5) (hs 4) (hs 7) hab hp hc hptr.r357 hptr.r356 hptr.r359 hinput]
  exact setup_slice p _ slots _
    (fun i => Avx2PointDouble.CFG.resultState_live s _ _ _ P (hs i))
    (hptr.frame (coreResultEnv_frame E _ _ P))

noncomputable def actual : Primitives where
  call0 := Avx2SquareNegateD.Execution.program.call
  call1 := Avx2FieldMul.program.call

/-- Actual imported callees: no successful helper execution or helper contract is assumed. -/
theorem body_actual (E : ⟪kernel.Γ⟫) (slots : Slots) (s : GlobalState)
    (P : Avx2PointAdd.Point) (hwf : s.WF) (hs : ∀ i, SmallRange s.mem (slots i) 160)
    (hab : (slots 5).id ≠ (slots 4).id)
    (hp : Avx2PointAdd.pointReduced P) (hc : Constants E)
    (hptr : InitialPointers E slots) (hinput : inputReads E (packPoint P)) :
    (kernel.bb0 actual).runBodyFrom E 729 s = .value (resultEnv E slots P, finalState s slots P) :=
  body actual E slots s P DoubleBase.ExecutionAvx2.imported_square_contract
    DoubleBase.ExecutionAvx2.imported_mul_contract hwf hs hab hp hc hptr hinput

end Agave.Ed25519.Tables.Avx2Constructor.Double

open Lean in
run_cmd do
  for endpoint in [
      `Agave.Ed25519.Tables.Avx2Constructor.Double.body_actual,
      `Agave.Ed25519.Tables.Avx2Constructor.Double.finalState_readback,
      `Agave.Ed25519.Tables.Avx2Constructor.Double.finalState_shape,
      `Agave.Ed25519.Tables.Avx2Constructor.Double.finalState_read,
      `Agave.Ed25519.Tables.Avx2Constructor.Double.resultEnv_frame] do
    for dependency in (← collectAxioms endpoint) do
      unless [`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{endpoint} depends on forbidden axiom {dependency}"

#print axioms Agave.Ed25519.Tables.Avx2Constructor.Double.body_actual
