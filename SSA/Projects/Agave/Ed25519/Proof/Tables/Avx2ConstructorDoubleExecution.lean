import SSA.Projects.Agave.Ed25519.Proof.Tables.Avx2ConstructorDoublePhases
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.CFGExecution
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Contracts

/-! The original constructor's initial double uses the imported square and
multiply bodies. Exact state, point readback and frames are derived from them. -/
namespace Agave.Ed25519.Tables.Avx2Constructor.Double
open LeanMLIR.RIR Avx2PointDouble
open DoubleBase.ExecutionAvx2 (RegisterFrame)
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
open Avx2PointAdd.Phases (packPoint readBlocks_storeBlocks storeBlocks_wf storeBlocks_live
  readBlocks_storeBlocks_ne)
open Avx2FieldMul.Execution (readBlocks storeBlocks)
open Reduce64.Execution (SmallRange)
open Avx2PointDouble.CFG (preparedState squaredState rightState leftState resultState)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

theorem Constants.frame {E F : ⟪kernel.Γ⟫} (h : Constants E)
    (hf : RegisterFrame 689 kernel.Γ.n E F) : Constants F := by
  exact ⟨(hf.read (%4) (by decide)).trans h.c32,
    (hf.read (%8) (by decide)).trans h.c64,
    (hf.read (%12) (by decide)).trans h.c96,
    (hf.read (%16) (by decide)).trans h.c128,
    (hf.read (%31) (by decide)).trans h.poison,
    (hf.read (%230) (by decide)).trans h.one,
    (hf.read (%247) (by decide)).trans h.prefix,
    (hf.read (%264) (by decide)).trans h.difference,
    (hf.read (%281) (by decide)).trans h.lazy0,
    (hf.read (%298) (by decide)).trans h.lazyN,
    (hf.read (%315) (by decide)).trans h.sum⟩

theorem Pointers.frame {E F : ⟪kernel.Γ⟫} (h : Pointers E a b r)
    (hf : RegisterFrame 717 kernel.Γ.n E F) : Pointers F a b r := by
  exact ⟨(hf.read (%357) (by decide)).trans h.r357,
    (hf.read (%694) (by decide)).trans h.r694,
    (hf.read (%695) (by decide)).trans h.r695,
    (hf.read (%696) (by decide)).trans h.r696,
    (hf.read (%697) (by decide)).trans h.r697,
    (hf.read (%356) (by decide)).trans h.r356,
    (hf.read (%703) (by decide)).trans h.r703,
    (hf.read (%704) (by decide)).trans h.r704,
    (hf.read (%705) (by decide)).trans h.r705,
    (hf.read (%706) (by decide)).trans h.r706,
    (hf.read (%359) (by decide)).trans h.r359⟩

theorem prepare_pointers (E : ⟪kernel.Γ⟫) (a b r : Pointer)
    (hpa : E.read (%357) = .value a) (hpb : E.read (%356) = .value b)
    (hpr : E.read (%359) = .value r) : Pointers (prepareEnv E a b) a b r := by
  constructor <;> simp [prepareEnv, mlir_env, hpa, hpb, hpr]

def coreResultEnv (E : ⟪kernel.Γ⟫) (a b : Pointer) (P : Avx2PointAdd.Point) : ⟪kernel.Γ⟫ :=
  leftEnv (mixEnv (prepareEnv E a b) (packCoordinates (squareStage (coordinates P))))

theorem coreResultEnv_frame (E : ⟪kernel.Γ⟫) (a b : Pointer) (P : Avx2PointAdd.Point) :
    RegisterFrame 689 kernel.Γ.n E (coreResultEnv E a b P) :=
  (prepare_frame E a b).trans (((mix_frame _ _).trans (left_frame _)).weaken (by decide) (by rfl))

theorem square_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (a b : Pointer) (input : Blocks)
    (hcall : DoubleBase.ExecutionAvx2.SquareContract p.call0)
    (hwf : s.WF) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hp : PointBound (blockCoordinates input))
    (hprepare : readBlocks s.mem a = prepareBlocks input)
    (hpa : E.read (%357) = .value a) (hpb : E.read (%356) = .value b) :
    runSlice (kernel.bb0 p) E 765 1 s = .value (E,
      {s with mem := storeBlocks s.mem b (packCoordinates (squareStage (blockCoordinates input)))}) := by
  have h := Avx2PointDouble.Execution.square_packed_state p.call0 hcall b a s hwf hb ha input hp hprepare
  dsimp only [DoubleBase.ExecutionAvx2.args2] at h
  simp [runSlice, kernel.bb0, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpa, hpb, h]

theorem multiply_slice (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (a b r : Pointer) (input : Coordinates)
    (hcall : DoubleBase.ExecutionAvx2.MulContract p.call1)
    (hwf : s.WF) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hr : SmallRange s.mem r 160) (hp : PointBound input)
    (hleft : Avx2PointDouble.Execution.readCoordinates s.mem a = left (squareStage input))
    (hright : Avx2PointDouble.Execution.readCoordinates s.mem b = right (squareStage input))
    (hpa : E.read (%357) = .value a) (hpb : E.read (%356) = .value b)
    (hpr : E.read (%359) = .value r) :
    runSlice (kernel.bb0 p) E 846 1 s = .value (E,
      {s with mem := storeBlocks s.mem r (packCoordinates (output input))}) := by
  have h := Avx2PointDouble.Execution.multiply_packed_state p.call1 hcall r a b s hwf hr ha hb
    input hp hleft hright
  dsimp only [DoubleBase.ExecutionAvx2.args3] at h
  simp [runSlice, kernel.bb0, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpa, hpb, hpr, h]

/-- The 118 actual doubling instructions, rejoined to the unchanged
constructor suffix at instruction 847. -/
theorem body_continue (p : Primitives) (E : ⟪kernel.Γ⟫)
    (s : GlobalState) (a b r : Pointer) (P : Avx2PointAdd.Point)
    (hsquare : DoubleBase.ExecutionAvx2.SquareContract p.call0)
    (hmul : DoubleBase.ExecutionAvx2.MulContract p.call1)
    (hwf : s.WF) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hr : SmallRange s.mem r 160) (hab : a.id ≠ b.id)
    (hp : Avx2PointAdd.pointReduced P) (hc : Constants E)
    (hpa : E.read (%357) = .value a) (hpb : E.read (%356) = .value b)
    (hpr : E.read (%359) = .value r) (hinput : inputReads E (packPoint P)) :
    (kernel.bb0 p).runBodyFrom E 729 s =
      (kernel.bb0 p).runBodyFrom (coreResultEnv E a b P) 847 (resultState s a b r P) := by
  let E1 := prepareEnv E a b
  let Q := squareStage (coordinates P)
  let E2 := mixEnv E1 (packCoordinates Q)
  let E3 := leftEnv E2
  let S1 := preparedState s a P
  let S2 := squaredState s a b P
  let S3 := rightState s a b P
  let S4 := leftState s a b P
  let S5 := resultState s a b r P
  have hP := coordinates_bounded hp
  have hQ : PointBound Q := squareStage_bounded hP
  have hc1 : Constants E1 := hc.frame (prepare_frame E a b)
  have hp1 : Pointers E1 a b r := prepare_pointers E a b r hpa hpb hpr
  have hp2 : Pointers E2 a b r := hp1.frame (mix_frame E1 (packCoordinates Q))
  have hp3 : Pointers E3 a b r := hp2.frame (left_frame E2)
  have ha1 : SmallRange S1.mem a 160 := storeBlocks_live ha _ _
  have hb1 : SmallRange S1.mem b 160 := storeBlocks_live hb _ _
  have hr1 : SmallRange S1.mem r 160 := storeBlocks_live hr _ _
  have ha2 : SmallRange S2.mem a 160 := storeBlocks_live ha1 _ _
  have hb2 : SmallRange S2.mem b 160 := storeBlocks_live hb1 _ _
  have hr2 : SmallRange S2.mem r 160 := storeBlocks_live hr1 _ _
  have ha3 : SmallRange S3.mem a 160 := storeBlocks_live ha2 _ _
  have hb3 : SmallRange S3.mem b 160 := storeBlocks_live hb2 _ _
  have hr3 : SmallRange S3.mem r 160 := storeBlocks_live hr2 _ _
  have ha4 : SmallRange S4.mem a 160 := storeBlocks_live ha3 _ _
  have hb4 : SmallRange S4.mem b 160 := storeBlocks_live hb3 _ _
  have hr4 : SmallRange S4.mem r 160 := storeBlocks_live hr3 _ _
  have hw1 : S1.WF := storeBlocks_wf s a _ hwf
  have hw4 : S4.WF := storeBlocks_wf _ _ _
    (storeBlocks_wf _ _ _ (storeBlocks_wf _ _ _ hw1))
  have hread1 : readBlocks S1.mem a = prepareBlocks (packPoint P) :=
    readBlocks_storeBlocks s.mem a _ ha
  have hread2 : readBlocks S2.mem b = packCoordinates Q :=
    readBlocks_storeBlocks S1.mem b _ hb1
  have hread3 : readBlocks S3.mem b = packCoordinates (right Q) :=
    readBlocks_storeBlocks S2.mem b _ hb2
  have hread4a : readBlocks S4.mem a = packCoordinates (left Q) :=
    readBlocks_storeBlocks S3.mem a _ ha3
  have hread4b : readBlocks S4.mem b = packCoordinates (right Q) := by
    exact (readBlocks_storeBlocks_ne S3.mem a b _ hab).trans hread3
  have hprep := prepared_stores p E1 s a (prepareBlocks (packPoint P)) ha
    hp1.r357 (prepare_field E a b _ hc hinput 0)
    hp1.r694 (prepare_field E a b _ hc hinput 1)
    hp1.r695 (prepare_field E a b _ hc hinput 2)
    hp1.r696 (prepare_field E a b _ hc hinput 3)
    hp1.r697 (prepare_field E a b _ hc hinput 4)
  have hsquare1 : runSlice (kernel.bb0 p) E1 765 1 S1 = .value (E1, S2) := by
    have h := square_slice p E1 S1 a b (packPoint P) hsquare hw1 ha1 hb1
      ((blockCoordinates_packPoint hp).symm ▸ hP) hread1 hp1.r357 hp1.r356
    simpa only [blockCoordinates_packPoint hp, S1, S2, squaredState] using h
  have hmix := mix_slice p E1 S2 b (packCoordinates Q) hb2 hread2
    hp1.r356 hp1.r703 hp1.r704 hp1.r705 hp1.r706
  have hright := right_stores p E2 S2 b (packCoordinates (right Q)) hb2
    hp2.r356 (right_field E1 Q hc1 hQ 0)
    hp2.r703 (right_field E1 Q hc1 hQ 1)
    hp2.r704 (right_field E1 Q hc1 hQ 2)
    hp2.r705 (right_field E1 Q hc1 hQ 3)
    hp2.r706 (right_field E1 Q hc1 hQ 4)
  have hleft := left_stores p E3 S3 a (packCoordinates (left Q)) ha3
    hp3.r357 (left_field E1 Q hc1 hQ 0)
    hp3.r694 (left_field E1 Q hc1 hQ 1)
    hp3.r695 (left_field E1 Q hc1 hQ 2)
    hp3.r696 (left_field E1 Q hc1 hQ 3)
    hp3.r697 (left_field E1 Q hc1 hQ 4)
  have hcoordsA : Avx2PointDouble.Execution.readCoordinates S4.mem a = left Q := by
    change blockCoordinates (readBlocks S4.mem a) = _
    rw [hread4a, Avx2PointDouble.Execution.blockCoordinates_pack_left hQ]
  have hcoordsB : Avx2PointDouble.Execution.readCoordinates S4.mem b = right Q := by
    change blockCoordinates (readBlocks S4.mem b) = _
    rw [hread4b, Avx2PointDouble.Execution.blockCoordinates_pack_right hQ]
  have hmul1 := multiply_slice p E3 S4 a b r (coordinates P) hmul hw4 ha4 hb4 hr4
    hP hcoordsA hcoordsB hp3.r357 hp3.r356 hp3.r359
  calc
    _ = (kernel.bb0 p).runBodyFrom E1 760 s :=
      runBodyFrom_slice _ E E1 729 31 s s (prepare_slice p E s a b ha hb hc hpa hpb)
    _ = (kernel.bb0 p).runBodyFrom E1 765 S1 :=
      runBodyFrom_slice _ E1 E1 760 5 s S1 hprep
    _ = (kernel.bb0 p).runBodyFrom E1 766 S2 :=
      runBodyFrom_slice _ E1 E1 765 1 S1 S2 hsquare1
    _ = (kernel.bb0 p).runBodyFrom E2 831 S2 :=
      runBodyFrom_slice _ E1 E2 766 65 S2 S2 hmix
    _ = (kernel.bb0 p).runBodyFrom E2 836 S3 :=
      runBodyFrom_slice _ E2 E2 831 5 S2 S3 hright
    _ = (kernel.bb0 p).runBodyFrom E3 841 S3 :=
      runBodyFrom_slice _ E2 E3 836 5 S3 S3 (left_slice p E2 S3)
    _ = (kernel.bb0 p).runBodyFrom E3 846 S4 :=
      runBodyFrom_slice _ E3 E3 841 5 S3 S4 hleft
    _ = (kernel.bb0 p).runBodyFrom E3 847 S5 :=
      runBodyFrom_slice _ E3 E3 846 1 S4 S5 hmul1

end Agave.Ed25519.Tables.Avx2Constructor.Double
