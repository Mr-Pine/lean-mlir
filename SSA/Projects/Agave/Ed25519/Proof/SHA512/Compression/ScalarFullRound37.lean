import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1286..1324: round 37. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv37 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1486 := (w 22).rotateRight 1
  let v1487 := (w 22).rotateRight 8
  let v1488 := v1486 ^^^ v1487
  let v1489 := (w 22) >>> 7
  let v1490 := v1488 ^^^ v1489
  let v1491 := (w 35).rotateRight 19
  let v1492 := (w 35).rotateRight 61
  let v1493 := v1491 ^^^ v1492
  let v1494 := (w 35) >>> 6
  let v1495 := v1493 ^^^ v1494
  let v1496 := v1490 + (w 21)
  let v1497 := v1496 + (w 30)
  let v1498 := v1497 + v1495
  let v1499 := s.e.rotateRight 14
  let v1500 := s.e.rotateRight 18
  let v1501 := v1499 ^^^ v1500
  let v1502 := s.e.rotateRight 41
  let v1503 := v1501 ^^^ v1502
  let v1504 := s.e &&& s.f
  let v1505 := s.e ^^^ (-1 : Word)
  let v1506 := s.g &&& v1505
  let v1507 := v1504 ||| v1506
  let v1508 := k
  let v1509 := v1498 + v1508
  let v1510 := v1509 + s.h
  let v1511 := v1510 + v1507
  let v1512 := v1511 + v1503
  let v1513 := s.a.rotateRight 28
  let v1514 := s.a.rotateRight 34
  let v1515 := v1513 ^^^ v1514
  let v1516 := s.a.rotateRight 39
  let v1517 := v1515 ^^^ v1516
  let v1518 := s.a &&& s.b
  let v1519 := s.b ^^^ s.c
  let v1520 := s.a &&& v1519
  let v1521 := v1520 ^^^ (s.b &&& s.c)
  let v1522 := v1517 + v1521
  let v1523 := v1512 + s.d
  let v1524 := v1522 + v1512
  E[%1486 := .value v1486,
    %1487 := .value v1487,
    %1488 := .value v1488,
    %1489 := .value v1489,
    %1490 := .value v1490,
    %1491 := .value v1491,
    %1492 := .value v1492,
    %1493 := .value v1493,
    %1494 := .value v1494,
    %1495 := .value v1495,
    %1496 := .value v1496,
    %1497 := .value v1497,
    %1498 := .value v1498,
    %1499 := .value v1499,
    %1500 := .value v1500,
    %1501 := .value v1501,
    %1502 := .value v1502,
    %1503 := .value v1503,
    %1504 := .value v1504,
    %1505 := .value v1505,
    %1506 := .value v1506,
    %1507 := .value v1507,
    %1508 := .value v1508,
    %1509 := .value v1509,
    %1510 := .value v1510,
    %1511 := .value v1511,
    %1512 := .value v1512,
    %1513 := .value v1513,
    %1514 := .value v1514,
    %1515 := .value v1515,
    %1516 := .value v1516,
    %1517 := .value v1517,
    %1518 := .value v1518,
    %1519 := .value v1519,
    %1520 := .value v1520,
    %1521 := .value v1521,
    %1522 := .value v1522,
    %1523 := .value v1523,
    %1524 := .value v1524]

def fullOut37 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1486 := (w 22).rotateRight 1
  let v1487 := (w 22).rotateRight 8
  let v1488 := v1486 ^^^ v1487
  let v1489 := (w 22) >>> 7
  let v1490 := v1488 ^^^ v1489
  let v1491 := (w 35).rotateRight 19
  let v1492 := (w 35).rotateRight 61
  let v1493 := v1491 ^^^ v1492
  let v1494 := (w 35) >>> 6
  let v1495 := v1493 ^^^ v1494
  let v1496 := v1490 + (w 21)
  let v1497 := v1496 + (w 30)
  let v1498 := v1497 + v1495
  let v1499 := s.e.rotateRight 14
  let v1500 := s.e.rotateRight 18
  let v1501 := v1499 ^^^ v1500
  let v1502 := s.e.rotateRight 41
  let v1503 := v1501 ^^^ v1502
  let v1504 := s.e &&& s.f
  let v1505 := s.e ^^^ (-1 : Word)
  let v1506 := s.g &&& v1505
  let v1507 := v1504 ||| v1506
  let v1508 := k
  let v1509 := v1498 + v1508
  let v1510 := v1509 + s.h
  let v1511 := v1510 + v1507
  let v1512 := v1511 + v1503
  let v1513 := s.a.rotateRight 28
  let v1514 := s.a.rotateRight 34
  let v1515 := v1513 ^^^ v1514
  let v1516 := s.a.rotateRight 39
  let v1517 := v1515 ^^^ v1516
  let v1518 := s.a &&& s.b
  let v1519 := s.b ^^^ s.c
  let v1520 := s.a &&& v1519
  let v1521 := v1520 ^^^ (s.b &&& s.c)
  let v1522 := v1517 + v1521
  let v1523 := v1512 + s.d
  let v1524 := v1522 + v1512
  ⟨v1524, s.a, s.b, s.c, v1523, s.e, s.f, s.g⟩

theorem fullOut37_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut37 s w k = Spec.round s (w 37) k := by
  have hw37 := hw 37 (by decide) (by decide)
  dsimp only [fullOut37, Spec.round]
  rw [hw37]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv37_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1486 E (fullEnv37 E s w k) := by
  unfold fullEnv37
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv37_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv37 E s w k) := by
  exact (fullEnv37_before E s w k).frame (by decide)

theorem full_body37 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready37 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 296#64) 64)
    (hk : state.mem.readAt (kp.add 296#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1286 |>.take 39) state =
      .value (fullEnv37 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv37, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k37, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready37 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready37 E s w) (hw : ScheduleReady w) :
    Ready38 (fullEnv37 E s w k) (Spec.round s (w 37) k) w := by
  have hb := fullEnv37_before E s w k
  have hout := fullOut37_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv37, fullOut37, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1485 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1446 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1407 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv37, fullOut37, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1484 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1445 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1406 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv37, Spec.round, mlir_env]
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
  · rw [hb.read_val 1459 (by decide) (by rfl)]; exact h.w36
  · have hwr := hw 37 (by decide) (by decide)
    simp [fullEnv37, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step37 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready37 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1286 |>.take 39) state =
      .value (E', state) ∧
      Ready38 E' (Spec.round s (w 37) (constants.toList.getD 37 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 37 0
  have hf := fullEnv37_frame E s w k
  refine ⟨fullEnv37 E s w k,
    full_body37 E state s w kp k h hc (hk 37).1 (hk 37).2,
    full_ready37 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
