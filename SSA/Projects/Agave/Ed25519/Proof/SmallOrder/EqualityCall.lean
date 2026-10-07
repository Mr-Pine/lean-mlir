import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityEnvironments
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityCompare
import SSA.Projects.Agave.Ed25519.Proof.SmallOrder.EqualityTail

/-! Whole execution of the original linked equality function. Every phase is
proved here from memory bounds; no phase-execution hypothesis is exposed. -/
namespace Agave.Ed25519.SmallOrder.Execution.EqualityCall
open LeanMLIR.RIR Verifier.Execution.PointConstantTimeEq
open Verifier.Execution.Dalek (ReadOnlyFrame choiceByte)
open Reduce64.Execution (SmallRange)
open EqualityAllocation EqualityPhases EqualityEnvironments
open SerialPoint.Execution
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

def serialPost (s : GlobalState) (r a : Pointer) : GlobalState :=
  {s with mem := Encoding.Decompress.Execution.ToBytes.storeBytes s.mem r (Encoding.Decompress.Execution.ToBytes.machine (SerialFieldMul.readLimbs s a))}

def advance (s : GlobalState) (n : Nat) : GlobalState :=
  {s with alloc := ⟨s.alloc.nextFreeBlock + n⟩}

def xProducts (s : GlobalState) (l r : Pointer) : GlobalState :=
  productXState (allocated s) (slot7 s) (slot6 s) l r

def xLeft (s : GlobalState) (l r : Pointer) : GlobalState :=
  serialPost (xProducts s l r) (slot3 s) (slot7 s)

def xRight (s : GlobalState) (l r : Pointer) : GlobalState :=
  serialPost (xLeft s l r) (slot2 s) (slot6 s)

def xCompared (s : GlobalState) (l r : Pointer) : GlobalState :=
  advance (xRight s l r) 33

def yProducts (s : GlobalState) (l r : Pointer) : GlobalState :=
  productYState (xCompared s l r) (slot5 s) (slot4 s) l r

def yLeft (s : GlobalState) (l r : Pointer) : GlobalState :=
  serialPost (yProducts s l r) (slot1 s) (slot5 s)

def yRight (s : GlobalState) (l r : Pointer) : GlobalState :=
  serialPost (yLeft s l r) (slot0 s) (slot4 s)

def yCompared (s : GlobalState) (l r : Pointer) : GlobalState :=
  advance (yRight s l r) 33

def finished (s : GlobalState) (l r : Pointer) : GlobalState :=
  advance (yCompared s l r) 1

def xEqual (s : GlobalState) (l r : Pointer) : Bool :=
  decide ((xRight s l r).mem.readAt (slot3 s) 256 =
    (xRight s l r).mem.readAt (slot2 s) 256)

def yEqual (s : GlobalState) (l r : Pointer) : Bool :=
  decide ((yRight s l r).mem.readAt (slot1 s) 256 =
    (yRight s l r).mem.readAt (slot0 s) 256)

def result (s : GlobalState) (l r : Pointer) : BitVec 8 :=
  choiceByte (xEqual s l r && yEqual s l r)

def Live (s t : GlobalState) : Prop :=
  ∀ (q : Pointer) (n : Nat), SmallRange s.mem q n → SmallRange t.mem q n

theorem live_refl (s : GlobalState) : Live s s := fun _ _ h => h

theorem live_trans (h : Live s t) (k : Live t u) : Live s u :=
  fun q n hq => k q n (h q n hq)

theorem serial_live (s : GlobalState) (r a : Pointer) : Live s (serialPost s r a) :=
  fun _ _ h => Encoding.Decompress.Execution.ToBytes.smallRange_storeBytes h r _

theorem advance_live (s : GlobalState) (n : Nat) : Live s (advance s n) :=
  live_refl s

theorem productsX_live (s : GlobalState) (xl xr l r : Pointer) :
    Live s (productXState s xl xr l r) :=
  fun q _ h => mulPost_smallRange _ _ _ _ q (mulPost_smallRange _ _ _ _ q h)

theorem productsY_live (s : GlobalState) (yl yr l r : Pointer) :
    Live s (productYState s yl yr l r) :=
  fun q _ h => mulPost_smallRange _ _ _ _ q (mulPost_smallRange _ _ _ _ q h)

theorem serial_wf (h : s.WF) (r a : Pointer) : (serialPost s r a).WF :=
  Encoding.Decompress.Execution.ToBytes.wf_storeBytes h r _

theorem productsX_wf (h : s.WF) (xl xr l r : Pointer) :
    (productXState s xl xr l r).WF := mulPost_wf _ _ _ _ (mulPost_wf _ _ _ _ h)

theorem productsY_wf (h : s.WF) (yl yr l r : Pointer) :
    (productYState s yl yr l r).WF := mulPost_wf _ _ _ _ (mulPost_wf _ _ _ _ h)

theorem serial_private (h : PrivateFrame before s) (r a : Pointer)
    (hr : before.alloc.nextFreeBlock ≤ r.id.id) : PrivateFrame before (serialPost s r a) :=
  h.storeBytes r _ hr

/-- Exact allocation effects of the imported byte comparator. -/
theorem compareX_linked (E : Env program.Γ) (s : GlobalState) (l r : Pointer)
    (hwf : s.WF) (hl : SmallRange s.mem l 32) (hr : SmallRange s.mem r 32)
    (el : E.read (%50) = .value l) (er : E.read (%49) = .value r) :
    (compareX equalityPrimitives).foldlM Instr.run E s =
      .value (E[%361 := .value (choiceByte (decide (s.mem.readAt l 256 = s.mem.readAt r 256)))],
        advance s 33) := by
  apply compareX_run equalityPrimitives E s (advance s 33) l r _ el er
  simpa only [equalityPrimitives, Verifier.Execution.Dalek.args2,
    Encoding.Decompress.Execution.BytesEq.program.args, choiceByte, decide_eq_true_eq,
    advance] using Encoding.Decompress.Execution.BytesEq.program_exact l r s hwf hl hr

theorem compareY_linked (E : Env program.Γ) (s : GlobalState) (l r : Pointer)
    (hwf : s.WF) (hl : SmallRange s.mem l 32) (hr : SmallRange s.mem r 32)
    (el : E.read (%48) = .value l) (er : E.read (%47) = .value r) :
    (compareY equalityPrimitives).foldlM Instr.run E s =
      .value (E[%668 := .value (choiceByte (decide (s.mem.readAt l 256 = s.mem.readAt r 256)))],
        advance s 33) := by
  apply compareY_run equalityPrimitives E s (advance s 33) l r _ el er
  simpa only [equalityPrimitives, Verifier.Execution.Dalek.args2,
    Encoding.Decompress.Execution.BytesEq.program.args, choiceByte, decide_eq_true_eq,
    advance] using Encoding.Decompress.Execution.BytesEq.program_exact l r s hwf hl hr

/-- The original six tail instructions, with the actual volatile black-box call. -/
theorem finish_linked (E : Env program.Γ) (s : GlobalState) (x y : Bool)
    (hwf : s.WF) (hx : E.read (%361) = .value (choiceByte x))
    (hy : E.read (%668) = .value (choiceByte y)) :
    (finish equalityPrimitives).foldlM Instr.run E s =
      .value (E[%669 := .value (choiceByte (x && y)),
        %670 := .value (choiceByte (x && y))], advance s 1) := by
  have hb := Encoding.Decompress.Execution.BlackBox.program_call (choiceByte (x && y)) s hwf
  simp only [Encoding.Decompress.Execution.BlackBox.program.args] at hb
  simp [finish, equalityTail_body_exact, List.foldlM_cons, List.foldlM_nil,
    Instr.run, BinOp.compute, Operation.and, EffectM.bind_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, Regs.read_cons, Regs.read_nil,
    Env.writeMany_cons, Env.writeMany_nil, hx, hy, choice_conjunction,
    equalityPrimitives, hb, advance, GlobalState.alloca]

theorem serializeX_exact (p : Primitives) :
    serializeX p = SerializerXL.inlineBody p ++ SerializerXR.inlineBody p := rfl

theorem serializeY_exact (p : Primitives) :
    serializeY p = SerializerYL.inlineBody p ++ SerializerYR.inlineBody p := rfl

/-- Both X serializers leave all other registers untouched. -/
theorem x_frame (E F G : Env program.Γ) (s t u : GlobalState)
    (hx : (SerializerXL.inlineBody equalityPrimitives).foldlM Instr.run E s = .value (F, t))
    (hy : (SerializerXR.inlineBody equalityPrimitives).foldlM Instr.run F t = .value (G, u))
    (r : Reg program.Γ τ) (hr : EnvironmentFrame.Outside 57 360 r) : G.read r = E.read r := by
  have h1 : EnvironmentFrame.Outside 57 208 r := by
    cases r <;> simp_all [EnvironmentFrame.Outside] <;> omega
  have h2 : EnvironmentFrame.Outside 209 360 r := by
    cases r <;> simp_all [EnvironmentFrame.Outside] <;> omega
  exact (SerializerXR.frame equalityPrimitives r h2 F G t u hy).trans
    (SerializerXL.frame equalityPrimitives r h1 E F s t hx)

/-- Both Y serializers leave all other registers untouched. -/
theorem y_frame (E F G : Env program.Γ) (s t u : GlobalState)
    (hx : (SerializerYL.inlineBody equalityPrimitives).foldlM Instr.run E s = .value (F, t))
    (hy : (SerializerYR.inlineBody equalityPrimitives).foldlM Instr.run F t = .value (G, u))
    (r : Reg program.Γ τ) (hr : EnvironmentFrame.Outside 364 667 r) : G.read r = E.read r := by
  have h1 : EnvironmentFrame.Outside 364 515 r := by
    cases r <;> simp_all [EnvironmentFrame.Outside] <;> omega
  have h2 : EnvironmentFrame.Outside 516 667 r := by
    cases r <;> simp_all [EnvironmentFrame.Outside] <;> omega
  exact (SerializerYR.frame equalityPrimitives r h2 F G t u hy).trans
    (SerializerYL.frame equalityPrimitives r h1 E F s t hx)

theorem finished_private (s : GlobalState) (l r : Pointer) (hwf : s.WF) :
    PrivateFrame s (finished s l r) := by
  have h0 := allocated_frame s hwf
  have h1 := productsX_private h0 (slot7 s) (slot6 s) l r
    (by simp [slot7, state7, state6, state5, state4, state3, state2, state1, GlobalState.alloca, GlobalState.allocaPtr, state0] <;> omega)
    (by simp [slot6, state6, state5, state4, state3, state2, state1, GlobalState.alloca, GlobalState.allocaPtr, state0] <;> omega)
  have h2 := serial_private h1 (slot3 s) (slot7 s)
    (by simp [slot3, state3, state2, state1, GlobalState.alloca, GlobalState.allocaPtr, state0] <;> omega)
  have h3 := serial_private h2 (slot2 s) (slot6 s)
    (by simp [slot2, state2, state1, GlobalState.alloca, GlobalState.allocaPtr, state0] <;> omega)
  have h4 := h3.advance 33
  have h5 := productsY_private h4 (slot5 s) (slot4 s) l r
    (by simp [slot5, state5, state4, state3, state2, state1, GlobalState.alloca, GlobalState.allocaPtr, state0] <;> omega)
    (by simp [slot4, state4, state3, state2, state1, GlobalState.alloca, GlobalState.allocaPtr, state0] <;> omega)
  have h6 := serial_private h5 (slot1 s) (slot5 s)
    (by simp [slot1, state1, GlobalState.alloca, GlobalState.allocaPtr, state0] <;> omega)
  have h7 := serial_private h6 (slot0 s) (slot4 s) (by exact Nat.le_refl _)
  exact (h7.advance 33).advance 1

/-- Execute the complete unchanged equality body and reclaim its private frame.
The inputs may alias and need not represent valid points. -/
theorem call_exact (s : GlobalState) (l r : Pointer) (hwf : s.WF)
    (hl : SmallRange s.mem l 160) (hr : SmallRange s.mem r 160) :
    equalityProgram.call (program.args (.value l) (.value r)) s =
      .value (.cons (.value (result s l r)) .nil,
        {finished s l r with mem := s.mem}) := by
  let E0 := Env.init (program.args (.value l) (.value r)).get
  let E1 := preparedEnv E0 s
  have h0 := prepare_run equalityPrimitives E0 s
  have h1 := productsX_run E1 (allocated s) (slot7 s) (slot6 s) l r
    (state8_wf hwf) (state8_live hwf hl) (state8_live hwf hr)
    (slot7_live s hwf) (slot6_live s hwf) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have wx : (xProducts s l r).WF := productsX_wf (state8_wf hwf) _ _ _ _
  have lx : Live (allocated s) (xProducts s l r) := productsX_live _ _ _ _ _
  have wxl : (xLeft s l r).WF := serial_wf wx _ _
  have lxl : Live (allocated s) (xLeft s l r) := live_trans lx (serial_live _ _ _)
  have wxr : (xRight s l r).WF := serial_wf wxl _ _
  have lxr : Live (allocated s) (xRight s l r) := live_trans lxl (serial_live _ _ _)
  obtain ⟨F1, hx1⟩ := SerializerXL.inline_run equalityPrimitives (firstSerializerEnv s l r)
    (slot3 s) (slot7 s) (xProducts s l r) wx
    (lx _ _ (slot3_live s hwf)) (lx _ _ (slot7_live s hwf)) (firstSerializer_ready s l r)
  have erx : SerializerXR.embedding.pull F1 = _ :=
    (xr_after_xl equalityPrimitives _ _ _ _ hx1).trans (xr_initial s l r)
  obtain ⟨F2, hx2⟩ := SerializerXR.inline_run equalityPrimitives F1
    (slot2 s) (slot6 s) (xLeft s l r) wxl
    (lxl _ _ (slot2_live s hwf)) (lxl _ _ (slot6_live s hwf)) erx
  have xf : ∀ {τ} (q : Reg program.Γ τ), EnvironmentFrame.Outside 57 360 q →
      F2.read q = (firstSerializerEnv s l r).read q :=
    fun q hq => x_frame _ _ _ _ _ _ hx1 hx2 q hq
  have h2 : (serializeX equalityPrimitives).foldlM Instr.run (firstSerializerEnv s l r)
      (xProducts s l r) = .value (F2, xRight s l r) := by
    simp only [serializeX_exact, List.foldlM_append, EffectM.bind_eq, hx1,
      PoisonOr.value_bind]
    exact hx2
  have h3 := compareX_linked F2 (xRight s l r) (slot3 s) (slot2 s) wxr
    (lxr _ _ (slot3_live s hwf)) (lxr _ _ (slot2_live s hwf))
    ((xf (%50) (by simp +decide [EnvironmentFrame.Outside])).trans (by rfl)) ((xf (%49) (by simp +decide [EnvironmentFrame.Outside])).trans (by rfl))
  let E4 := F2[%361 := .value (choiceByte (xEqual s l r))]
  have wy : (yProducts s l r).WF := productsY_wf wxr.add_blocks _ _ _ _
  have ly : Live (allocated s) (yProducts s l r) :=
    live_trans lxr (productsY_live _ _ _ _ _)
  have h4 := productsY_run E4 (xCompared s l r) (slot5 s) (slot4 s) l r
    wxr.add_blocks (lxr _ _ (state8_live hwf hl)) (lxr _ _ (state8_live hwf hr))
    (lxr _ _ (slot5_live s hwf)) (lxr _ _ (slot4_live s hwf))
    (by exact (xf (%arg0) (by simp +decide [EnvironmentFrame.Outside])).trans (by rfl))
    (by exact (xf (%arg1) (by simp +decide [EnvironmentFrame.Outside])).trans (by rfl))
    (by simpa (disch := decide) only [E4, mlir_env] using (xf (%52) (by simp +decide [EnvironmentFrame.Outside])).trans (show (firstSerializerEnv s l r).read (%52) = .value (slot5 s) from rfl))
    (by simpa (disch := decide) only [E4, mlir_env] using (xf (%51) (by simp +decide [EnvironmentFrame.Outside])).trans (show (firstSerializerEnv s l r).read (%51) = .value (slot4 s) from rfl))
    (by simpa (disch := decide) only [E4, mlir_env] using (xf (%56) (by simp +decide [EnvironmentFrame.Outside])).trans (show (firstSerializerEnv s l r).read (%56) = .value (l.add 80#64) from rfl))
    (by simpa (disch := decide) only [E4, mlir_env] using (xf (%55) (by simp +decide [EnvironmentFrame.Outside])).trans (show (firstSerializerEnv s l r).read (%55) = .value (r.add 80#64) from rfl))
    (by simpa (disch := decide) only [E4, mlir_env] using (xf (%13) (by simp +decide [EnvironmentFrame.Outside])).trans (show (firstSerializerEnv s l r).read (%13) = .value 40#64 from rfl))
  let E5 := E4[%362 := .value (l.add 40), %363 := .value (r.add 40)]
  have eyl : SerializerYL.embedding.pull E5 = _ :=
    (yl_writes F2 _ l r).trans ((yl_after_xr equalityPrimitives _ _ _ _ hx2).trans
      ((yl_after_xl equalityPrimitives _ _ _ _ hx1).trans (yl_initial s l r)))
  have wyl : (yLeft s l r).WF := serial_wf wy _ _
  have lyl : Live (allocated s) (yLeft s l r) := live_trans ly (serial_live _ _ _)
  have wyr : (yRight s l r).WF := serial_wf wyl _ _
  have lyr : Live (allocated s) (yRight s l r) := live_trans lyl (serial_live _ _ _)
  obtain ⟨F3, hy1⟩ := SerializerYL.inline_run equalityPrimitives E5
    (slot1 s) (slot5 s) (yProducts s l r) wy
    (ly _ _ (slot1_live s hwf)) (ly _ _ (slot5_live s hwf)) eyl
  have eyr : SerializerYR.embedding.pull F3 = _ :=
    (yr_after_yl equalityPrimitives _ _ _ _ hy1).trans ((yr_writes F2 _ l r).trans
      ((yr_after_xr equalityPrimitives _ _ _ _ hx2).trans
        ((yr_after_xl equalityPrimitives _ _ _ _ hx1).trans (yr_initial s l r))))
  obtain ⟨F4, hy2⟩ := SerializerYR.inline_run equalityPrimitives F3
    (slot0 s) (slot4 s) (yLeft s l r) wyl
    (lyl _ _ (slot0_live s hwf)) (lyl _ _ (slot4_live s hwf)) eyr
  have yf : ∀ {τ} (q : Reg program.Γ τ), EnvironmentFrame.Outside 364 667 q →
      F4.read q = E5.read q := fun q hq => y_frame _ _ _ _ _ _ hy1 hy2 q hq
  have h5 : (serializeY equalityPrimitives).foldlM Instr.run E5
      (yProducts s l r) = .value (F4, yRight s l r) := by
    simp only [serializeY_exact, List.foldlM_append, EffectM.bind_eq, hy1,
      PoisonOr.value_bind]
    exact hy2
  have ey48 : F4.read (%48) = .value (slot1 s) := by
    rw [yf (%48) (by simp +decide [EnvironmentFrame.Outside])]
    simpa (disch := decide) only [E5, E4, mlir_env] using (xf (%48) (by simp +decide [EnvironmentFrame.Outside])).trans
      (show (firstSerializerEnv s l r).read (%48) = .value (slot1 s) from rfl)
  have ey47 : F4.read (%47) = .value (slot0 s) := by
    rw [yf (%47) (by simp +decide [EnvironmentFrame.Outside])]
    simpa (disch := decide) only [E5, E4, mlir_env] using (xf (%47) (by simp +decide [EnvironmentFrame.Outside])).trans
      (show (firstSerializerEnv s l r).read (%47) = .value (slot0 s) from rfl)
  have h6 := compareY_linked F4 (yRight s l r) (slot1 s) (slot0 s) wyr
    (lyr _ _ (slot1_live s hwf)) (lyr _ _ (slot0_live s hwf)) ey48 ey47
  let E7 := F4[%668 := .value (choiceByte (yEqual s l r))]
  have ex : E7.read (%361) = .value (choiceByte (xEqual s l r)) := by
    simp (disch := decide) only [E7, mlir_env]
    rw [yf (%361) (by simp +decide [EnvironmentFrame.Outside])]
    simp (disch := decide) only [E5, E4, mlir_env]
  have h7 := finish_linked E7 (yCompared s l r) (xEqual s l r) (yEqual s l r)
    wyr.add_blocks ex (by simp (disch := decide) only [E7, mlir_env])
  have hc := call_of_phases equalityPrimitives (program.args (.value l) (.value r))
    _ _ _ _ _ _ _ _ s _ _ _ _ _ _ _ _ (result s l r)
    h0 h1 h2 h3 h4 h5 h6 h7 (by simp only [mlir_env]; rfl)
  have hf := finished_private s l r hwf
  change equalityProgram.call (program.args (.value l) (.value r)) s =
    .value (.cons (.value (result s l r)) .nil,
      {finished s l r with mem := (finished s l r).mem.eraseFrom s.alloc.nextFreeBlock}) at hc
  rw [hf.memory] at hc
  exact hc

/-- The complete linked call preserves every caller-visible memory observation. -/
theorem call_contract (s : GlobalState) (l r : Pointer) (hwf : s.WF)
    (hl : SmallRange s.mem l 160) (hr : SmallRange s.mem r 160) :
    ∃ t, equalityProgram.call (program.args (.value l) (.value r)) s =
      .value (.cons (.value (result s l r)) .nil, t) ∧ ReadOnlyFrame s t := by
  refine ⟨{finished s l r with mem := s.mem}, call_exact s l r hwf hl hr, ?_⟩
  have h := finished_private s l r hwf
  simpa only [h.memory] using h.readOnly hwf

end Agave.Ed25519.SmallOrder.Execution.EqualityCall
