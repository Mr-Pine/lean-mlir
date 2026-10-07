import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1247..1285: round 36. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv36 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1447 := (w 21).rotateRight 1
  let v1448 := (w 21).rotateRight 8
  let v1449 := v1447 ^^^ v1448
  let v1450 := (w 21) >>> 7
  let v1451 := v1449 ^^^ v1450
  let v1452 := (w 34).rotateRight 19
  let v1453 := (w 34).rotateRight 61
  let v1454 := v1452 ^^^ v1453
  let v1455 := (w 34) >>> 6
  let v1456 := v1454 ^^^ v1455
  let v1457 := v1451 + (w 20)
  let v1458 := v1457 + (w 29)
  let v1459 := v1458 + v1456
  let v1460 := s.e.rotateRight 14
  let v1461 := s.e.rotateRight 18
  let v1462 := v1460 ^^^ v1461
  let v1463 := s.e.rotateRight 41
  let v1464 := v1462 ^^^ v1463
  let v1465 := s.e &&& s.f
  let v1466 := s.e ^^^ (-1 : Word)
  let v1467 := s.g &&& v1466
  let v1468 := v1465 ||| v1467
  let v1469 := k
  let v1470 := v1459 + v1469
  let v1471 := v1470 + s.h
  let v1472 := v1471 + v1468
  let v1473 := v1472 + v1464
  let v1474 := s.a.rotateRight 28
  let v1475 := s.a.rotateRight 34
  let v1476 := v1474 ^^^ v1475
  let v1477 := s.a.rotateRight 39
  let v1478 := v1476 ^^^ v1477
  let v1479 := s.a &&& s.b
  let v1480 := s.b ^^^ s.c
  let v1481 := s.a &&& v1480
  let v1482 := v1481 ^^^ (s.b &&& s.c)
  let v1483 := v1478 + v1482
  let v1484 := v1473 + s.d
  let v1485 := v1483 + v1473
  E[%1447 := .value v1447,
    %1448 := .value v1448,
    %1449 := .value v1449,
    %1450 := .value v1450,
    %1451 := .value v1451,
    %1452 := .value v1452,
    %1453 := .value v1453,
    %1454 := .value v1454,
    %1455 := .value v1455,
    %1456 := .value v1456,
    %1457 := .value v1457,
    %1458 := .value v1458,
    %1459 := .value v1459,
    %1460 := .value v1460,
    %1461 := .value v1461,
    %1462 := .value v1462,
    %1463 := .value v1463,
    %1464 := .value v1464,
    %1465 := .value v1465,
    %1466 := .value v1466,
    %1467 := .value v1467,
    %1468 := .value v1468,
    %1469 := .value v1469,
    %1470 := .value v1470,
    %1471 := .value v1471,
    %1472 := .value v1472,
    %1473 := .value v1473,
    %1474 := .value v1474,
    %1475 := .value v1475,
    %1476 := .value v1476,
    %1477 := .value v1477,
    %1478 := .value v1478,
    %1479 := .value v1479,
    %1480 := .value v1480,
    %1481 := .value v1481,
    %1482 := .value v1482,
    %1483 := .value v1483,
    %1484 := .value v1484,
    %1485 := .value v1485]

def fullOut36 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1447 := (w 21).rotateRight 1
  let v1448 := (w 21).rotateRight 8
  let v1449 := v1447 ^^^ v1448
  let v1450 := (w 21) >>> 7
  let v1451 := v1449 ^^^ v1450
  let v1452 := (w 34).rotateRight 19
  let v1453 := (w 34).rotateRight 61
  let v1454 := v1452 ^^^ v1453
  let v1455 := (w 34) >>> 6
  let v1456 := v1454 ^^^ v1455
  let v1457 := v1451 + (w 20)
  let v1458 := v1457 + (w 29)
  let v1459 := v1458 + v1456
  let v1460 := s.e.rotateRight 14
  let v1461 := s.e.rotateRight 18
  let v1462 := v1460 ^^^ v1461
  let v1463 := s.e.rotateRight 41
  let v1464 := v1462 ^^^ v1463
  let v1465 := s.e &&& s.f
  let v1466 := s.e ^^^ (-1 : Word)
  let v1467 := s.g &&& v1466
  let v1468 := v1465 ||| v1467
  let v1469 := k
  let v1470 := v1459 + v1469
  let v1471 := v1470 + s.h
  let v1472 := v1471 + v1468
  let v1473 := v1472 + v1464
  let v1474 := s.a.rotateRight 28
  let v1475 := s.a.rotateRight 34
  let v1476 := v1474 ^^^ v1475
  let v1477 := s.a.rotateRight 39
  let v1478 := v1476 ^^^ v1477
  let v1479 := s.a &&& s.b
  let v1480 := s.b ^^^ s.c
  let v1481 := s.a &&& v1480
  let v1482 := v1481 ^^^ (s.b &&& s.c)
  let v1483 := v1478 + v1482
  let v1484 := v1473 + s.d
  let v1485 := v1483 + v1473
  ⟨v1485, s.a, s.b, s.c, v1484, s.e, s.f, s.g⟩

theorem fullOut36_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut36 s w k = Spec.round s (w 36) k := by
  have hw36 := hw 36 (by decide) (by decide)
  dsimp only [fullOut36, Spec.round]
  rw [hw36]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv36_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1447 E (fullEnv36 E s w k) := by
  unfold fullEnv36
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv36_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv36 E s w k) := by
  exact (fullEnv36_before E s w k).frame (by decide)

theorem full_body36 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready36 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 288#64) 64)
    (hk : state.mem.readAt (kp.add 288#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1247 |>.take 39) state =
      .value (fullEnv36 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv36, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k36, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready36 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready36 E s w) (hw : ScheduleReady w) :
    Ready37 (fullEnv36 E s w k) (Spec.round s (w 36) k) w := by
  have hb := fullEnv36_before E s w k
  have hout := fullOut36_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv36, fullOut36, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1446 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1407 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1368 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv36, fullOut36, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1445 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1406 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1367 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv36, Spec.round, mlir_env]
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
  · rw [hb.read_val 1420 (by decide) (by rfl)]; exact h.w35
  · have hwr := hw 36 (by decide) (by decide)
    simp [fullEnv36, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step36 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready36 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1247 |>.take 39) state =
      .value (E', state) ∧
      Ready37 E' (Spec.round s (w 36) (constants.toList.getD 36 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 36 0
  have hf := fullEnv36_frame E s w k
  refine ⟨fullEnv36 E s w k,
    full_body36 E state s w kp k h hc (hk 36).1 (hk 36).2,
    full_ready36 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
