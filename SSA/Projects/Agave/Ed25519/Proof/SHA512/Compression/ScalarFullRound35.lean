import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1208..1246: round 35. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv35 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1408 := (w 20).rotateRight 1
  let v1409 := (w 20).rotateRight 8
  let v1410 := v1408 ^^^ v1409
  let v1411 := (w 20) >>> 7
  let v1412 := v1410 ^^^ v1411
  let v1413 := (w 33).rotateRight 19
  let v1414 := (w 33).rotateRight 61
  let v1415 := v1413 ^^^ v1414
  let v1416 := (w 33) >>> 6
  let v1417 := v1415 ^^^ v1416
  let v1418 := v1412 + (w 19)
  let v1419 := v1418 + (w 28)
  let v1420 := v1419 + v1417
  let v1421 := s.e.rotateRight 14
  let v1422 := s.e.rotateRight 18
  let v1423 := v1421 ^^^ v1422
  let v1424 := s.e.rotateRight 41
  let v1425 := v1423 ^^^ v1424
  let v1426 := s.e &&& s.f
  let v1427 := s.e ^^^ (-1 : Word)
  let v1428 := s.g &&& v1427
  let v1429 := v1426 ||| v1428
  let v1430 := k
  let v1431 := v1420 + v1430
  let v1432 := v1431 + s.h
  let v1433 := v1432 + v1429
  let v1434 := v1433 + v1425
  let v1435 := s.a.rotateRight 28
  let v1436 := s.a.rotateRight 34
  let v1437 := v1435 ^^^ v1436
  let v1438 := s.a.rotateRight 39
  let v1439 := v1437 ^^^ v1438
  let v1440 := s.a &&& s.b
  let v1441 := s.b ^^^ s.c
  let v1442 := s.a &&& v1441
  let v1443 := v1442 ^^^ (s.b &&& s.c)
  let v1444 := v1439 + v1443
  let v1445 := v1434 + s.d
  let v1446 := v1444 + v1434
  E[%1408 := .value v1408,
    %1409 := .value v1409,
    %1410 := .value v1410,
    %1411 := .value v1411,
    %1412 := .value v1412,
    %1413 := .value v1413,
    %1414 := .value v1414,
    %1415 := .value v1415,
    %1416 := .value v1416,
    %1417 := .value v1417,
    %1418 := .value v1418,
    %1419 := .value v1419,
    %1420 := .value v1420,
    %1421 := .value v1421,
    %1422 := .value v1422,
    %1423 := .value v1423,
    %1424 := .value v1424,
    %1425 := .value v1425,
    %1426 := .value v1426,
    %1427 := .value v1427,
    %1428 := .value v1428,
    %1429 := .value v1429,
    %1430 := .value v1430,
    %1431 := .value v1431,
    %1432 := .value v1432,
    %1433 := .value v1433,
    %1434 := .value v1434,
    %1435 := .value v1435,
    %1436 := .value v1436,
    %1437 := .value v1437,
    %1438 := .value v1438,
    %1439 := .value v1439,
    %1440 := .value v1440,
    %1441 := .value v1441,
    %1442 := .value v1442,
    %1443 := .value v1443,
    %1444 := .value v1444,
    %1445 := .value v1445,
    %1446 := .value v1446]

def fullOut35 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1408 := (w 20).rotateRight 1
  let v1409 := (w 20).rotateRight 8
  let v1410 := v1408 ^^^ v1409
  let v1411 := (w 20) >>> 7
  let v1412 := v1410 ^^^ v1411
  let v1413 := (w 33).rotateRight 19
  let v1414 := (w 33).rotateRight 61
  let v1415 := v1413 ^^^ v1414
  let v1416 := (w 33) >>> 6
  let v1417 := v1415 ^^^ v1416
  let v1418 := v1412 + (w 19)
  let v1419 := v1418 + (w 28)
  let v1420 := v1419 + v1417
  let v1421 := s.e.rotateRight 14
  let v1422 := s.e.rotateRight 18
  let v1423 := v1421 ^^^ v1422
  let v1424 := s.e.rotateRight 41
  let v1425 := v1423 ^^^ v1424
  let v1426 := s.e &&& s.f
  let v1427 := s.e ^^^ (-1 : Word)
  let v1428 := s.g &&& v1427
  let v1429 := v1426 ||| v1428
  let v1430 := k
  let v1431 := v1420 + v1430
  let v1432 := v1431 + s.h
  let v1433 := v1432 + v1429
  let v1434 := v1433 + v1425
  let v1435 := s.a.rotateRight 28
  let v1436 := s.a.rotateRight 34
  let v1437 := v1435 ^^^ v1436
  let v1438 := s.a.rotateRight 39
  let v1439 := v1437 ^^^ v1438
  let v1440 := s.a &&& s.b
  let v1441 := s.b ^^^ s.c
  let v1442 := s.a &&& v1441
  let v1443 := v1442 ^^^ (s.b &&& s.c)
  let v1444 := v1439 + v1443
  let v1445 := v1434 + s.d
  let v1446 := v1444 + v1434
  ⟨v1446, s.a, s.b, s.c, v1445, s.e, s.f, s.g⟩

theorem fullOut35_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut35 s w k = Spec.round s (w 35) k := by
  have hw35 := hw 35 (by decide) (by decide)
  dsimp only [fullOut35, Spec.round]
  rw [hw35]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv35_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1408 E (fullEnv35 E s w k) := by
  unfold fullEnv35
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv35_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv35 E s w k) := by
  exact (fullEnv35_before E s w k).frame (by decide)

theorem full_body35 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready35 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 280#64) 64)
    (hk : state.mem.readAt (kp.add 280#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1208 |>.take 39) state =
      .value (fullEnv35 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv35, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k35, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready35 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready35 E s w) (hw : ScheduleReady w) :
    Ready36 (fullEnv35 E s w k) (Spec.round s (w 35) k) w := by
  have hb := fullEnv35_before E s w k
  have hout := fullOut35_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv35, fullOut35, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1407 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1368 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1329 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv35, fullOut35, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1406 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1367 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1328 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv35, Spec.round, mlir_env]
  · rw [hb.read_val 835 (by decide) (by rfl)]; exact h.w20
  · rw [hb.read_val 874 (by decide) (by rfl)]; exact h.w21
  · rw [hb.read_val 913 (by decide) (by rfl)]; exact h.w22
  · rw [hb.read_val 952 (by decide) (by rfl)]; exact h.w23
  · rw [hb.read_val 991 (by decide) (by rfl)]; exact h.w24
  · rw [hb.read_val 1030 (by decide) (by rfl)]; exact h.w25
  · rw [hb.read_val 1069 (by decide) (by rfl)]; exact h.w26
  · rw [hb.read_val 1108 (by decide) (by rfl)]; exact h.w27
  · rw [hb.read_val 1147 (by decide) (by rfl)]; exact h.w28
  · rw [hb.read_val 1186 (by decide) (by rfl)]; exact h.w29
  · rw [hb.read_val 1225 (by decide) (by rfl)]; exact h.w30
  · rw [hb.read_val 1264 (by decide) (by rfl)]; exact h.w31
  · rw [hb.read_val 1303 (by decide) (by rfl)]; exact h.w32
  · rw [hb.read_val 1342 (by decide) (by rfl)]; exact h.w33
  · rw [hb.read_val 1381 (by decide) (by rfl)]; exact h.w34
  · have hwr := hw 35 (by decide) (by decide)
    simp [fullEnv35, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step35 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready35 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1208 |>.take 39) state =
      .value (E', state) ∧
      Ready36 E' (Spec.round s (w 35) (constants.toList.getD 35 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 35 0
  have hf := fullEnv35_frame E s w k
  refine ⟨fullEnv35 E s w k,
    full_body35 E state s w kp k h hc (hk 35).1 (hk 35).2,
    full_ready35 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
