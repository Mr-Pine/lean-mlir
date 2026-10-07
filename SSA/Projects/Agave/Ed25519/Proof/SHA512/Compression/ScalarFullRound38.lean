import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1325..1363: round 38. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv38 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1525 := (w 23).rotateRight 1
  let v1526 := (w 23).rotateRight 8
  let v1527 := v1525 ^^^ v1526
  let v1528 := (w 23) >>> 7
  let v1529 := v1527 ^^^ v1528
  let v1530 := (w 36).rotateRight 19
  let v1531 := (w 36).rotateRight 61
  let v1532 := v1530 ^^^ v1531
  let v1533 := (w 36) >>> 6
  let v1534 := v1532 ^^^ v1533
  let v1535 := v1529 + (w 22)
  let v1536 := v1535 + (w 31)
  let v1537 := v1536 + v1534
  let v1538 := s.e.rotateRight 14
  let v1539 := s.e.rotateRight 18
  let v1540 := v1538 ^^^ v1539
  let v1541 := s.e.rotateRight 41
  let v1542 := v1540 ^^^ v1541
  let v1543 := s.e &&& s.f
  let v1544 := s.e ^^^ (-1 : Word)
  let v1545 := s.g &&& v1544
  let v1546 := v1543 ||| v1545
  let v1547 := k
  let v1548 := v1537 + v1547
  let v1549 := v1548 + s.h
  let v1550 := v1549 + v1546
  let v1551 := v1550 + v1542
  let v1552 := s.a.rotateRight 28
  let v1553 := s.a.rotateRight 34
  let v1554 := v1552 ^^^ v1553
  let v1555 := s.a.rotateRight 39
  let v1556 := v1554 ^^^ v1555
  let v1557 := s.a &&& s.b
  let v1558 := s.b ^^^ s.c
  let v1559 := s.a &&& v1558
  let v1560 := v1559 ^^^ (s.b &&& s.c)
  let v1561 := v1556 + v1560
  let v1562 := v1551 + s.d
  let v1563 := v1561 + v1551
  E[%1525 := .value v1525,
    %1526 := .value v1526,
    %1527 := .value v1527,
    %1528 := .value v1528,
    %1529 := .value v1529,
    %1530 := .value v1530,
    %1531 := .value v1531,
    %1532 := .value v1532,
    %1533 := .value v1533,
    %1534 := .value v1534,
    %1535 := .value v1535,
    %1536 := .value v1536,
    %1537 := .value v1537,
    %1538 := .value v1538,
    %1539 := .value v1539,
    %1540 := .value v1540,
    %1541 := .value v1541,
    %1542 := .value v1542,
    %1543 := .value v1543,
    %1544 := .value v1544,
    %1545 := .value v1545,
    %1546 := .value v1546,
    %1547 := .value v1547,
    %1548 := .value v1548,
    %1549 := .value v1549,
    %1550 := .value v1550,
    %1551 := .value v1551,
    %1552 := .value v1552,
    %1553 := .value v1553,
    %1554 := .value v1554,
    %1555 := .value v1555,
    %1556 := .value v1556,
    %1557 := .value v1557,
    %1558 := .value v1558,
    %1559 := .value v1559,
    %1560 := .value v1560,
    %1561 := .value v1561,
    %1562 := .value v1562,
    %1563 := .value v1563]

def fullOut38 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1525 := (w 23).rotateRight 1
  let v1526 := (w 23).rotateRight 8
  let v1527 := v1525 ^^^ v1526
  let v1528 := (w 23) >>> 7
  let v1529 := v1527 ^^^ v1528
  let v1530 := (w 36).rotateRight 19
  let v1531 := (w 36).rotateRight 61
  let v1532 := v1530 ^^^ v1531
  let v1533 := (w 36) >>> 6
  let v1534 := v1532 ^^^ v1533
  let v1535 := v1529 + (w 22)
  let v1536 := v1535 + (w 31)
  let v1537 := v1536 + v1534
  let v1538 := s.e.rotateRight 14
  let v1539 := s.e.rotateRight 18
  let v1540 := v1538 ^^^ v1539
  let v1541 := s.e.rotateRight 41
  let v1542 := v1540 ^^^ v1541
  let v1543 := s.e &&& s.f
  let v1544 := s.e ^^^ (-1 : Word)
  let v1545 := s.g &&& v1544
  let v1546 := v1543 ||| v1545
  let v1547 := k
  let v1548 := v1537 + v1547
  let v1549 := v1548 + s.h
  let v1550 := v1549 + v1546
  let v1551 := v1550 + v1542
  let v1552 := s.a.rotateRight 28
  let v1553 := s.a.rotateRight 34
  let v1554 := v1552 ^^^ v1553
  let v1555 := s.a.rotateRight 39
  let v1556 := v1554 ^^^ v1555
  let v1557 := s.a &&& s.b
  let v1558 := s.b ^^^ s.c
  let v1559 := s.a &&& v1558
  let v1560 := v1559 ^^^ (s.b &&& s.c)
  let v1561 := v1556 + v1560
  let v1562 := v1551 + s.d
  let v1563 := v1561 + v1551
  ⟨v1563, s.a, s.b, s.c, v1562, s.e, s.f, s.g⟩

theorem fullOut38_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut38 s w k = Spec.round s (w 38) k := by
  have hw38 := hw 38 (by decide) (by decide)
  dsimp only [fullOut38, Spec.round]
  rw [hw38]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv38_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1525 E (fullEnv38 E s w k) := by
  unfold fullEnv38
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv38_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv38 E s w k) := by
  exact (fullEnv38_before E s w k).frame (by decide)

theorem full_body38 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready38 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 304#64) 64)
    (hk : state.mem.readAt (kp.add 304#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1325 |>.take 39) state =
      .value (fullEnv38 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv38, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k38, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready38 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready38 E s w) (hw : ScheduleReady w) :
    Ready39 (fullEnv38 E s w k) (Spec.round s (w 38) k) w := by
  have hb := fullEnv38_before E s w k
  have hout := fullOut38_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv38, fullOut38, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1524 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1485 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1446 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv38, fullOut38, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1523 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1484 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1445 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv38, Spec.round, mlir_env]
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
  · rw [hb.read_val 1498 (by decide) (by rfl)]; exact h.w37
  · have hwr := hw 38 (by decide) (by decide)
    simp [fullEnv38, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step38 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready38 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1325 |>.take 39) state =
      .value (E', state) ∧
      Ready39 E' (Spec.round s (w 38) (constants.toList.getD 38 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 38 0
  have hf := fullEnv38_frame E s w k
  refine ⟨fullEnv38 E s w k,
    full_body38 E state s w kp k h hc (hk 38).1 (hk 38).2,
    full_ready38 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
