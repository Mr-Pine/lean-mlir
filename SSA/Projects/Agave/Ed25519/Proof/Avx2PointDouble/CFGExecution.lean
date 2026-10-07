import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.CFGPhases
import SSA.Projects.Agave.Ed25519.Proof.Avx2PointDouble.HelperContracts
import SSA.Projects.Agave.Ed25519.Proof.DoubleBase.ExecutionAvx2Dispatch

/-! The actual doubling block in the double-base loop. Its result is a
reduced packed point, its only memory writes are the three caller scratch
objects, and every register below 427 is preserved. The digit-A load and the
original signed switch are included; no whole-iteration contract is used. -/
namespace Agave.Ed25519.Avx2PointDouble.CFG
open LeanMLIR.RIR DoubleBase DoubleBase.RIR
open DoubleBase.ExecutionAvx2 (RegisterFrame digitSign digitSign_cmp)
open Avx2PointAdd.CFG (runSlice runBodyFrom_slice)
open Avx2PointAdd.Phases (packPoint readBlocks_storeBlocks storeBlocks_wf storeBlocks_live
  readBlocks_storeBlocks_ne)
open Avx2FieldMul.Execution (readBlocks storeBlocks)
open Reduce64.Execution (SmallRange)
open NAF.Memory (Buffer)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
attribute [local implicit_reducible] Ty.width

theorem Constants.frame {E F : ⟪avx2Kernel.Γ⟫} (h : Constants E)
    (hf : RegisterFrame 427 avx2Kernel.Γ.n E F) : Constants F := by
  exact ⟨(hf.read (%26) (by decide)).trans h.poison,
    (hf.read (%27) (by decide)).trans h.one,
    (hf.read (%45) (by decide)).trans h.prefix,
    (hf.read (%62) (by decide)).trans h.difference,
    (hf.read (%81) (by decide)).trans h.lazy0,
    (hf.read (%99) (by decide)).trans h.lazyN,
    (hf.read (%116) (by decide)).trans h.sum⟩

theorem Pointers.frame {E F : ⟪avx2Kernel.Γ⟫} (h : Pointers E a b r)
    (hf : RegisterFrame 427 avx2Kernel.Γ.n E F) : Pointers F a b r := by
  exact ⟨(hf.read (%256) (by decide)).trans h.r256,
    (hf.read (%327) (by decide)).trans h.r327,
    (hf.read (%328) (by decide)).trans h.r328,
    (hf.read (%329) (by decide)).trans h.r329,
    (hf.read (%330) (by decide)).trans h.r330,
    (hf.read (%255) (by decide)).trans h.r255,
    (hf.read (%331) (by decide)).trans h.r331,
    (hf.read (%332) (by decide)).trans h.r332,
    (hf.read (%333) (by decide)).trans h.r333,
    (hf.read (%334) (by decide)).trans h.r334,
    (hf.read (%263) (by decide)).trans h.r263,
    (hf.read (%335) (by decide)).trans h.r335,
    (hf.read (%336) (by decide)).trans h.r336,
    (hf.read (%337) (by decide)).trans h.r337,
    (hf.read (%338) (by decide)).trans h.r338⟩

def preparedState (s : GlobalState) (a : Pointer) (P : Avx2PointAdd.Point) : GlobalState :=
  {s with mem := storeBlocks s.mem a (prepareBlocks (packPoint P))}
def squaredState (s : GlobalState) (a b : Pointer) (P : Avx2PointAdd.Point) : GlobalState :=
  let t := preparedState s a P
  {t with mem := storeBlocks t.mem b (packCoordinates (squareStage (coordinates P)))}
def rightState (s : GlobalState) (a b : Pointer) (P : Avx2PointAdd.Point) : GlobalState :=
  let t := squaredState s a b P
  {t with mem := storeBlocks t.mem b (packCoordinates (right (squareStage (coordinates P))))}
def leftState (s : GlobalState) (a b : Pointer) (P : Avx2PointAdd.Point) : GlobalState :=
  let t := rightState s a b P
  {t with mem := storeBlocks t.mem a (packCoordinates (left (squareStage (coordinates P))))}
def resultState (s : GlobalState) (a b r : Pointer) (P : Avx2PointAdd.Point) : GlobalState :=
  let t := leftState s a b P
  {t with mem := storeBlocks t.mem r (packPoint (doublePoint P))}

def resultEnv (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point) : ⟪avx2Kernel.Γ⟫ :=
  loadResultEnv
    (leftEnv (mixEnv (prepareEnv E) (packCoordinates (squareStage (coordinates P)))))
    (packPoint (doublePoint P))

theorem resultEnv_frame (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point) :
    RegisterFrame 427 avx2Kernel.Γ.n E (resultEnv E P) :=
  ((prepare_frame E).trans (mix_frame _ _)).trans
    ((left_frame _).trans (loadResult_frame _ _))

theorem resultEnv_reads (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point) :
    (resultEnv E P).read (%517) = Ty.wrap (packPoint (doublePoint P) 0) ∧
    (resultEnv E P).read (%518) = Ty.wrap (packPoint (doublePoint P) 1) ∧
    (resultEnv E P).read (%519) = Ty.wrap (packPoint (doublePoint P) 2) ∧
    (resultEnv E P).read (%520) = Ty.wrap (packPoint (doublePoint P) 3) ∧
    (resultEnv E P).read (%521) = Ty.wrap (packPoint (doublePoint P) 4) := by
  simp [resultEnv, loadResultEnv, mlir_env]

theorem resultState_wf (s : GlobalState) (a b r : Pointer) (P : Avx2PointAdd.Point)
    (h : s.WF) : (resultState s a b r P).WF := by
  exact storeBlocks_wf _ _ _ (storeBlocks_wf _ _ _ (storeBlocks_wf _ _ _
    (storeBlocks_wf _ _ _ (storeBlocks_wf _ _ _ h))))

theorem resultState_live (s : GlobalState) (a b r : Pointer) (P : Avx2PointAdd.Point)
    {q : Pointer} {bytes : Nat} (h : SmallRange s.mem q bytes) :
    SmallRange (resultState s a b r P).mem q bytes := by
  exact storeBlocks_live (storeBlocks_live (storeBlocks_live
    (storeBlocks_live (storeBlocks_live h _ _) _ _) _ _) _ _) _ _

private theorem storeBlocks_read_ne (m : MemoryState) (p q : Pointer) (v : Blocks)
    (width : Nat) (hne : p.id ≠ q.id) :
    (storeBlocks m p v).readAt q width = m.readAt q width := by
  exact Avx2PointAdd.Phases.readAt_storeBlocks_ne m p q v width hne

/-- Fresh scratch identifiers give the byte frame for NAF arrays, static
tables, caller objects, and any unrelated live allocation. -/
theorem resultState_read (s : GlobalState) (a b r q : Pointer)
    (P : Avx2PointAdd.Point) (width : Nat)
    (ha : a.id ≠ q.id) (hb : b.id ≠ q.id) (hr : r.id ≠ q.id) :
    (resultState s a b r P).mem.readAt q width = s.mem.readAt q width := by
  calc
    _ = (leftState s a b P).mem.readAt q width := storeBlocks_read_ne _ r q _ width hr
    _ = (rightState s a b P).mem.readAt q width := storeBlocks_read_ne _ a q _ width ha
    _ = (squaredState s a b P).mem.readAt q width := storeBlocks_read_ne _ b q _ width hb
    _ = (preparedState s a P).mem.readAt q width := storeBlocks_read_ne _ b q _ width hb
    _ = s.mem.readAt q width := storeBlocks_read_ne _ a q _ width ha

theorem square_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (a b : Pointer) (input : Blocks)
    (hcall : DoubleBase.ExecutionAvx2.SquareContract p.call1)
    (hwf : s.WF) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hp : PointBound (blockCoordinates input))
    (hprepare : readBlocks s.mem a = prepareBlocks input)
    (hpa : E.read (%256) = .value a) (hpb : E.read (%255) = .value b) :
    runSlice (avx2Kernel.bb18 p) E 28 1 s = .value (E,
      {s with mem := storeBlocks s.mem b (packCoordinates (squareStage (blockCoordinates input)))}) := by
  have h := Execution.square_packed_state p.call1 hcall b a s hwf hb ha input hp hprepare
  dsimp only [DoubleBase.ExecutionAvx2.args2] at h
  simp [runSlice, avx2Kernel.bb18, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpa, hpb, h]

theorem multiply_slice (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (a b r : Pointer) (input : Coordinates)
    (hcall : DoubleBase.ExecutionAvx2.MulContract p.call2)
    (hwf : s.WF) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hr : SmallRange s.mem r 160) (hp : PointBound input)
    (hleft : Execution.readCoordinates s.mem a = left (squareStage input))
    (hright : Execution.readCoordinates s.mem b = right (squareStage input))
    (hpa : E.read (%256) = .value a) (hpb : E.read (%255) = .value b)
    (hpr : E.read (%263) = .value r) :
    runSlice (avx2Kernel.bb18 p) E 109 1 s = .value (E,
      {s with mem := storeBlocks s.mem r (packCoordinates (output input))}) := by
  have h := Execution.multiply_packed_state p.call2 hcall r a b s hwf hr ha hb
    input hp hleft hright
  dsimp only [DoubleBase.ExecutionAvx2.args3] at h
  simp [runSlice, avx2Kernel.bb18, List.foldlM_cons, List.foldlM_nil,
    Instr.run, Regs.read_cons, Regs.read_nil, Env.writeMany_nil,
    EffectM.bind_eq, EffectM.pure_eq, hpa, hpb, hpr, h]

/-- The 118 actual instructions before the digit-A dispatch, rejoined to
the unchanged suffix at instruction 118. -/
theorem body_continue (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (a b r : Pointer) (P : Avx2PointAdd.Point)
    (hsquare : DoubleBase.ExecutionAvx2.SquareContract p.call1)
    (hmul : DoubleBase.ExecutionAvx2.MulContract p.call2)
    (hwf : s.WF) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hr : SmallRange s.mem r 160) (hab : a.id ≠ b.id)
    (hp : Avx2PointAdd.pointReduced P) (hc : Constants E)
    (hptr : Pointers E a b r) (hinput : inputReads E (packPoint P)) :
    (avx2Kernel.bb18 p).runBodyFrom E 0 s =
      (avx2Kernel.bb18 p).runBodyFrom (resultEnv E P) 118 (resultState s a b r P) := by
  let E1 := prepareEnv E
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
  have hc1 : Constants E1 := hc.frame (prepare_frame E)
  have hp1 : Pointers E1 a b r := hptr.frame (prepare_frame E)
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
  have hr5 : SmallRange S5.mem r 160 := storeBlocks_live hr4 _ _
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
  have hread5 : readBlocks S5.mem r = packPoint (doublePoint P) :=
    readBlocks_storeBlocks S4.mem r _ hr4
  have hprep := prepared_stores p E1 s a (prepareBlocks (packPoint P)) ha
    hp1.r256 (prepare_field E _ hc hinput 0)
    hp1.r327 (prepare_field E _ hc hinput 1)
    hp1.r328 (prepare_field E _ hc hinput 2)
    hp1.r329 (prepare_field E _ hc hinput 3)
    hp1.r330 (prepare_field E _ hc hinput 4)
  have hsquare1 : runSlice (avx2Kernel.bb18 p) E1 28 1 S1 = .value (E1, S2) := by
    have h := square_slice p E1 S1 a b (packPoint P) hsquare hw1 ha1 hb1
      ((blockCoordinates_packPoint hp).symm ▸ hP) hread1 hp1.r256 hp1.r255
    simpa only [blockCoordinates_packPoint hp, S1, S2, squaredState] using h
  have hmix := mix_slice p E1 S2 b (packCoordinates Q) hb2 hread2
    hp1.r255 hp1.r331 hp1.r332 hp1.r333 hp1.r334
  have hright := right_stores p E2 S2 b (packCoordinates (right Q)) hb2
    hp2.r255 (right_field E1 Q hc1 hQ 0)
    hp2.r331 (right_field E1 Q hc1 hQ 1)
    hp2.r332 (right_field E1 Q hc1 hQ 2)
    hp2.r333 (right_field E1 Q hc1 hQ 3)
    hp2.r334 (right_field E1 Q hc1 hQ 4)
  have hleft := left_stores p E3 S3 a (packCoordinates (left Q)) ha3
    hp3.r256 (left_field E1 Q hc1 hQ 0)
    hp3.r327 (left_field E1 Q hc1 hQ 1)
    hp3.r328 (left_field E1 Q hc1 hQ 2)
    hp3.r329 (left_field E1 Q hc1 hQ 3)
    hp3.r330 (left_field E1 Q hc1 hQ 4)
  have hcoordsA : Execution.readCoordinates S4.mem a = left Q := by
    change blockCoordinates (readBlocks S4.mem a) = _
    rw [hread4a, Execution.blockCoordinates_pack_left hQ]
  have hcoordsB : Execution.readCoordinates S4.mem b = right Q := by
    change blockCoordinates (readBlocks S4.mem b) = _
    rw [hread4b, Execution.blockCoordinates_pack_right hQ]
  have hmul1 := multiply_slice p E3 S4 a b r (coordinates P) hmul hw4 ha4 hb4 hr4
    hP hcoordsA hcoordsB hp3.r256 hp3.r255 hp3.r263
  have hloads := loadResult_slice p E3 S5 r (packPoint (doublePoint P)) hr5 hread5
    hp3.r263 hp3.r335 hp3.r336 hp3.r337 hp3.r338
  calc
    _ = (avx2Kernel.bb18 p).runBodyFrom E1 23 s :=
      runBodyFrom_slice _ E E1 0 23 s s (prepare_slice p E s)
    _ = (avx2Kernel.bb18 p).runBodyFrom E1 28 S1 :=
      runBodyFrom_slice _ E1 E1 23 5 s S1 hprep
    _ = (avx2Kernel.bb18 p).runBodyFrom E1 29 S2 :=
      runBodyFrom_slice _ E1 E1 28 1 S1 S2 hsquare1
    _ = (avx2Kernel.bb18 p).runBodyFrom E2 94 S2 :=
      runBodyFrom_slice _ E1 E2 29 65 S2 S2 hmix
    _ = (avx2Kernel.bb18 p).runBodyFrom E2 99 S3 :=
      runBodyFrom_slice _ E2 E2 94 5 S2 S3 hright
    _ = (avx2Kernel.bb18 p).runBodyFrom E3 104 S3 :=
      runBodyFrom_slice _ E2 E3 99 5 S3 S3 (left_slice p E2 S3)
    _ = (avx2Kernel.bb18 p).runBodyFrom E3 109 S4 :=
      runBodyFrom_slice _ E3 E3 104 5 S3 S4 hleft
    _ = (avx2Kernel.bb18 p).runBodyFrom E3 110 S5 :=
      runBodyFrom_slice _ E3 E3 109 1 S4 S5 hmul1
    _ = (avx2Kernel.bb18 p).runBodyFrom (resultEnv E P) 118 S5 :=
      runBodyFrom_slice _ E3 (resultEnv E P) 110 8 S5 S5 hloads

def dispatchEnv (E : ⟪avx2Kernel.Γ⟫) (digits : Pointer) (pos : Fin 256)
    (digit : BitVec 8) : ⟪avx2Kernel.Γ⟫ :=
  E[%522 := .value (digits.add (BitVec.ofNat 64 pos.val)),
    %523 := .value digit, %524 := .value (digitSign digit)]

def zeroEnv (E : ⟪avx2Kernel.Γ⟫) : ⟪avx2Kernel.Γ⟫ :=
  E[%698 := E.read (%520), %699 := E.read (%519), %700 := E.read (%518),
    %701 := E.read (%517), %702 := E.read (%521)]

def successor (digit : BitVec 8) : Fin 35 :=
  if digit.toInt < 0 then 20 else if digit = 0#8 then 26 else 23

def exitEnv (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point)
    (digits : Pointer) (pos : Fin 256) (digit : BitVec 8) : ⟪avx2Kernel.Γ⟫ :=
  let F := dispatchEnv (resultEnv E P) digits pos digit
  if digit.toInt < 0 then F else if digit = 0#8 then zeroEnv F else F

theorem dispatch_body (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (digits : Pointer) (pos : Fin 256) (digit : BitVec 8) (s : GlobalState)
    (hbuffer : Buffer s.mem digits 256)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit)
    (hzero : E.read (%1) = .value 0#8)
    (hdigits : E.read (%266) = .value digits)
    (hpos : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    (avx2Kernel.bb18 p).runBodyFrom E 118 s =
      .value (dispatchEnv E digits pos digit, s) := by
  have hscale := NAF.RIR.cursor_byte_offset pos
  have hgep := hbuffer.gep pos.val (by have := pos.isLt; omega)
  have hfits := hbuffer.fits_at pos.val 1 (by have := pos.isLt; omega)
  have hload (env : ⟪avx2Kernel.Γ⟫) :
      Operation.load (%523 : Dst avx2Kernel.Γ (.bv 8))
        (.value (digits.add (BitVec.ofNat 64 pos.val))) env s =
          .value (env[%523 := .value digit], s) := by
    apply run_load hfits
    change PoisonOr.value (s.mem.readAt _ 8) = _
    rw [hread]
  simp [BasicBlock.runBodyFrom, avx2Kernel.bb18, dispatchEnv,
    List.foldlM_cons, List.foldlM_nil, Instr.run, BinOp.compute,
    GepIndex.inboundsOffset, EffectM.bind_eq, EffectM.get_eq, EffectM.pure_eq,
    PoisonOr.value_bind, mlir_env, hscale, hgep, hload, hzero, hdigits, hpos,
    digitSign_cmp digit]

theorem dispatch_exit (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (digits : Pointer) (pos : Fin 256) (digit : BitVec 8) (s : GlobalState) :
    (avx2Kernel.bb18 p).exit.run avx2Kernel.blockParams
      (dispatchEnv E digits pos digit) s =
      .value ((if digit.toInt < 0 then dispatchEnv E digits pos digit
        else if digit = 0#8 then zeroEnv (dispatchEnv E digits pos digit)
        else dispatchEnv E digits pos digit, .inr (successor digit)), s) := by
  by_cases hneg : digit.toInt < 0 <;> by_cases hzero : digit = 0#8 <;>
    simp [avx2Kernel.bb18, dispatchEnv, zeroEnv, successor, digitSign,
      Exit.run, switchTarget, Jump.run, Regs.read_cons, Regs.read_nil,
      Env.writeMany_cons, Env.writeMany_nil, mlir_env, hneg, hzero]

theorem resultState_buffer (s : GlobalState) (a b r : Pointer) (P : Avx2PointAdd.Point)
    {q : Pointer} {bytes : Nat} (h : Buffer s.mem q bytes) :
    Buffer (resultState s a b r P).mem q bytes := by
  unfold resultState leftState rightState squaredState preparedState storeBlocks
  repeat' apply Buffer.storeAt
  exact h

theorem exitEnv_frame (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point)
    (digits : Pointer) (pos : Fin 256) (digit : BitVec 8) :
    RegisterFrame 427 avx2Kernel.Γ.n E (exitEnv E P digits pos digit) := by
  have hdispatch : RegisterFrame 427 avx2Kernel.Γ.n E
      (dispatchEnv (resultEnv E P) digits pos digit) := by
    unfold dispatchEnv
    iterate 3 apply RegisterFrame.write (hd := by decide)
    exact resultEnv_frame E P
  unfold exitEnv
  split_ifs
  · exact hdispatch
  · unfold zeroEnv
    iterate 5 apply RegisterFrame.write (hd := by decide)
    exact hdispatch
  · exact hdispatch

/-- All three switch arms preserve the five doubled-point output registers.
The zero arm additionally writes them to bb26's parameters in its reversed
first-four register order. -/
theorem exitEnv_reads (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point)
    (digits : Pointer) (pos : Fin 256) (digit : BitVec 8) :
    (exitEnv E P digits pos digit).read (%517) = Ty.wrap (packPoint (doublePoint P) 0) ∧
    (exitEnv E P digits pos digit).read (%518) = Ty.wrap (packPoint (doublePoint P) 1) ∧
    (exitEnv E P digits pos digit).read (%519) = Ty.wrap (packPoint (doublePoint P) 2) ∧
    (exitEnv E P digits pos digit).read (%520) = Ty.wrap (packPoint (doublePoint P) 3) ∧
    (exitEnv E P digits pos digit).read (%521) = Ty.wrap (packPoint (doublePoint P) 4) := by
  unfold exitEnv
  split_ifs
  all_goals simpa [zeroEnv, dispatchEnv, mlir_env] using resultEnv_reads E P

theorem exitEnv_zero_reads (E : ⟪avx2Kernel.Γ⟫) (P : Avx2PointAdd.Point)
    (digits : Pointer) (pos : Fin 256) :
    (exitEnv E P digits pos 0#8).read (%698) = Ty.wrap (packPoint (doublePoint P) 3) ∧
    (exitEnv E P digits pos 0#8).read (%699) = Ty.wrap (packPoint (doublePoint P) 2) ∧
    (exitEnv E P digits pos 0#8).read (%700) = Ty.wrap (packPoint (doublePoint P) 1) ∧
    (exitEnv E P digits pos 0#8).read (%701) = Ty.wrap (packPoint (doublePoint P) 0) ∧
    (exitEnv E P digits pos 0#8).read (%702) = Ty.wrap (packPoint (doublePoint P) 4) := by
  simp [exitEnv, zeroEnv, dispatchEnv, resultEnv, loadResultEnv, mlir_env]

/-- Exact execution of bb18, including its original digit-A dispatch. The
only primitive premises are the byte-level square and multiply contracts;
all point arithmetic, stored operands and branch results are derived. -/
theorem block_correct (p : Avx2CFG.Primitives) (E : ⟪avx2Kernel.Γ⟫)
    (s : GlobalState) (a b r digits : Pointer) (P : Avx2PointAdd.Point)
    (pos : Fin 256) (digit : BitVec 8)
    (hsquare : DoubleBase.ExecutionAvx2.SquareContract p.call1)
    (hmul : DoubleBase.ExecutionAvx2.MulContract p.call2)
    (hwf : s.WF) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hr : SmallRange s.mem r 160) (hab : a.id ≠ b.id)
    (hbuffer : Buffer s.mem digits 256)
    (had : a.id ≠ digits.id) (hbd : b.id ≠ digits.id) (hrd : r.id ≠ digits.id)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit)
    (hp : Avx2PointAdd.pointReduced P) (hc : Constants E)
    (hptr : Pointers E a b r) (hinput : inputReads E (packPoint P))
    (hzero : E.read (%1) = .value 0#8)
    (hdigits : E.read (%266) = .value digits)
    (hpos : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    (avx2Kernel.bb18 p).run avx2Kernel.blockParams E s =
      .value ((exitEnv E P digits pos digit, .inr (successor digit)), resultState s a b r P) := by
  have hf := resultEnv_frame E P
  have hread' : (resultState s a b r P).mem.readAt
      (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit :=
    (resultState_read s a b r (digits.add (BitVec.ofNat 64 pos.val)) P 8 had hbd hrd).trans hread
  have hdispatch := dispatch_body p (resultEnv E P) digits pos digit (resultState s a b r P)
    (resultState_buffer s a b r P hbuffer) hread'
    ((hf.read (%1) (by decide)).trans hzero)
    ((hf.read (%266) (by decide)).trans hdigits)
    ((hf.read (%426) (by decide)).trans hpos)
  rw [BasicBlock.run_eq]
  simp only [EffectM.bind_eq]
  rw [body_continue p E s a b r P hsquare hmul hwf ha hb hr hab hp hc hptr hinput,
    hdispatch]
  simpa only [PoisonOr.value_bind, exitEnv] using
    dispatch_exit p (resultEnv E P) digits pos digit (resultState s a b r P)

theorem block_run (p : Avx2CFG.Primitives) (g : Avx2CFG.Globals)
    (E : ⟪avx2Kernel.Γ⟫) (s : GlobalState) (a b r digits : Pointer)
    (P : Avx2PointAdd.Point) (pos : Fin 256) (digit : BitVec 8)
    (hsquare : DoubleBase.ExecutionAvx2.SquareContract p.call1)
    (hmul : DoubleBase.ExecutionAvx2.MulContract p.call2)
    (hwf : s.WF) (ha : SmallRange s.mem a 160) (hb : SmallRange s.mem b 160)
    (hr : SmallRange s.mem r 160) (hab : a.id ≠ b.id)
    (hbuffer : Buffer s.mem digits 256)
    (had : a.id ≠ digits.id) (hbd : b.id ≠ digits.id) (hrd : r.id ≠ digits.id)
    (hread : s.mem.readAt (digits.add (BitVec.ofNat 64 pos.val)) 8 = digit)
    (hp : Avx2PointAdd.pointReduced P) (hc : Constants E)
    (hptr : Pointers E a b r) (hinput : inputReads E (packPoint P))
    (hzero : E.read (%1) = .value 0#8)
    (hdigits : E.read (%266) = .value digits)
    (hpos : E.read (%426) = .value (BitVec.ofNat 64 pos.val)) :
    (avx2Kernel p g).runFrom E 18 s =
      (avx2Kernel p g).runFrom (exitEnv E P digits pos digit) (successor digit)
        (resultState s a b r P) := by
  rw [Func.runFrom_eq, show (avx2Kernel p g).blocks 18 = avx2Kernel.bb18 p from rfl,
    block_correct p E s a b r digits P pos digit hsquare hmul hwf ha hb hr hab
      hbuffer had hbd hrd hread hp hc hptr hinput hzero hdigits hpos]
  rfl

end Agave.Ed25519.Avx2PointDouble.CFG
