import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1403..1441: round 40. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv40 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1603 := (w 25).rotateRight 1
  let v1604 := (w 25).rotateRight 8
  let v1605 := v1603 ^^^ v1604
  let v1606 := (w 25) >>> 7
  let v1607 := v1605 ^^^ v1606
  let v1608 := (w 38).rotateRight 19
  let v1609 := (w 38).rotateRight 61
  let v1610 := v1608 ^^^ v1609
  let v1611 := (w 38) >>> 6
  let v1612 := v1610 ^^^ v1611
  let v1613 := v1607 + (w 24)
  let v1614 := v1613 + (w 33)
  let v1615 := v1614 + v1612
  let v1616 := s.e.rotateRight 14
  let v1617 := s.e.rotateRight 18
  let v1618 := v1616 ^^^ v1617
  let v1619 := s.e.rotateRight 41
  let v1620 := v1618 ^^^ v1619
  let v1621 := s.e &&& s.f
  let v1622 := s.e ^^^ (-1 : Word)
  let v1623 := s.g &&& v1622
  let v1624 := v1621 ||| v1623
  let v1625 := k
  let v1626 := v1615 + v1625
  let v1627 := v1626 + s.h
  let v1628 := v1627 + v1624
  let v1629 := v1628 + v1620
  let v1630 := s.a.rotateRight 28
  let v1631 := s.a.rotateRight 34
  let v1632 := v1630 ^^^ v1631
  let v1633 := s.a.rotateRight 39
  let v1634 := v1632 ^^^ v1633
  let v1635 := s.a &&& s.b
  let v1636 := s.b ^^^ s.c
  let v1637 := s.a &&& v1636
  let v1638 := v1637 ^^^ (s.b &&& s.c)
  let v1639 := v1634 + v1638
  let v1640 := v1629 + s.d
  let v1641 := v1639 + v1629
  E[%1603 := .value v1603,
    %1604 := .value v1604,
    %1605 := .value v1605,
    %1606 := .value v1606,
    %1607 := .value v1607,
    %1608 := .value v1608,
    %1609 := .value v1609,
    %1610 := .value v1610,
    %1611 := .value v1611,
    %1612 := .value v1612,
    %1613 := .value v1613,
    %1614 := .value v1614,
    %1615 := .value v1615,
    %1616 := .value v1616,
    %1617 := .value v1617,
    %1618 := .value v1618,
    %1619 := .value v1619,
    %1620 := .value v1620,
    %1621 := .value v1621,
    %1622 := .value v1622,
    %1623 := .value v1623,
    %1624 := .value v1624,
    %1625 := .value v1625,
    %1626 := .value v1626,
    %1627 := .value v1627,
    %1628 := .value v1628,
    %1629 := .value v1629,
    %1630 := .value v1630,
    %1631 := .value v1631,
    %1632 := .value v1632,
    %1633 := .value v1633,
    %1634 := .value v1634,
    %1635 := .value v1635,
    %1636 := .value v1636,
    %1637 := .value v1637,
    %1638 := .value v1638,
    %1639 := .value v1639,
    %1640 := .value v1640,
    %1641 := .value v1641]

def fullOut40 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1603 := (w 25).rotateRight 1
  let v1604 := (w 25).rotateRight 8
  let v1605 := v1603 ^^^ v1604
  let v1606 := (w 25) >>> 7
  let v1607 := v1605 ^^^ v1606
  let v1608 := (w 38).rotateRight 19
  let v1609 := (w 38).rotateRight 61
  let v1610 := v1608 ^^^ v1609
  let v1611 := (w 38) >>> 6
  let v1612 := v1610 ^^^ v1611
  let v1613 := v1607 + (w 24)
  let v1614 := v1613 + (w 33)
  let v1615 := v1614 + v1612
  let v1616 := s.e.rotateRight 14
  let v1617 := s.e.rotateRight 18
  let v1618 := v1616 ^^^ v1617
  let v1619 := s.e.rotateRight 41
  let v1620 := v1618 ^^^ v1619
  let v1621 := s.e &&& s.f
  let v1622 := s.e ^^^ (-1 : Word)
  let v1623 := s.g &&& v1622
  let v1624 := v1621 ||| v1623
  let v1625 := k
  let v1626 := v1615 + v1625
  let v1627 := v1626 + s.h
  let v1628 := v1627 + v1624
  let v1629 := v1628 + v1620
  let v1630 := s.a.rotateRight 28
  let v1631 := s.a.rotateRight 34
  let v1632 := v1630 ^^^ v1631
  let v1633 := s.a.rotateRight 39
  let v1634 := v1632 ^^^ v1633
  let v1635 := s.a &&& s.b
  let v1636 := s.b ^^^ s.c
  let v1637 := s.a &&& v1636
  let v1638 := v1637 ^^^ (s.b &&& s.c)
  let v1639 := v1634 + v1638
  let v1640 := v1629 + s.d
  let v1641 := v1639 + v1629
  ⟨v1641, s.a, s.b, s.c, v1640, s.e, s.f, s.g⟩

theorem fullOut40_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut40 s w k = Spec.round s (w 40) k := by
  have hw40 := hw 40 (by decide) (by decide)
  dsimp only [fullOut40, Spec.round]
  rw [hw40]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv40_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1603 E (fullEnv40 E s w k) := by
  unfold fullEnv40
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv40_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv40 E s w k) := by
  exact (fullEnv40_before E s w k).frame (by decide)

theorem full_body40 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready40 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 320#64) 64)
    (hk : state.mem.readAt (kp.add 320#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1403 |>.take 39) state =
      .value (fullEnv40 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv40, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k40, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready40 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready40 E s w) (hw : ScheduleReady w) :
    Ready41 (fullEnv40 E s w k) (Spec.round s (w 40) k) w := by
  have hb := fullEnv40_before E s w k
  have hout := fullOut40_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv40, fullOut40, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1602 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1563 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1524 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv40, fullOut40, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1601 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1562 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1523 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv40, Spec.round, mlir_env]
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
  · rw [hb.read_val 1537 (by decide) (by rfl)]; exact h.w38
  · rw [hb.read_val 1576 (by decide) (by rfl)]; exact h.w39
  · have hwr := hw 40 (by decide) (by decide)
    simp [fullEnv40, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step40 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready40 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1403 |>.take 39) state =
      .value (E', state) ∧
      Ready41 E' (Spec.round s (w 40) (constants.toList.getD 40 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 40 0
  have hf := fullEnv40_frame E s w k
  refine ⟨fullEnv40 E s w k,
    full_body40 E state s w kp k h hc (hk 40).1 (hk 40).2,
    full_ready40 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
