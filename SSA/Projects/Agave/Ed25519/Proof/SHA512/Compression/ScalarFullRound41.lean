import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1442..1480: round 41. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv41 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1642 := (w 26).rotateRight 1
  let v1643 := (w 26).rotateRight 8
  let v1644 := v1642 ^^^ v1643
  let v1645 := (w 26) >>> 7
  let v1646 := v1644 ^^^ v1645
  let v1647 := (w 39).rotateRight 19
  let v1648 := (w 39).rotateRight 61
  let v1649 := v1647 ^^^ v1648
  let v1650 := (w 39) >>> 6
  let v1651 := v1649 ^^^ v1650
  let v1652 := v1646 + (w 25)
  let v1653 := v1652 + (w 34)
  let v1654 := v1653 + v1651
  let v1655 := s.e.rotateRight 14
  let v1656 := s.e.rotateRight 18
  let v1657 := v1655 ^^^ v1656
  let v1658 := s.e.rotateRight 41
  let v1659 := v1657 ^^^ v1658
  let v1660 := s.e &&& s.f
  let v1661 := s.e ^^^ (-1 : Word)
  let v1662 := s.g &&& v1661
  let v1663 := v1660 ||| v1662
  let v1664 := k
  let v1665 := v1654 + v1664
  let v1666 := v1665 + s.h
  let v1667 := v1666 + v1663
  let v1668 := v1667 + v1659
  let v1669 := s.a.rotateRight 28
  let v1670 := s.a.rotateRight 34
  let v1671 := v1669 ^^^ v1670
  let v1672 := s.a.rotateRight 39
  let v1673 := v1671 ^^^ v1672
  let v1674 := s.a &&& s.b
  let v1675 := s.b ^^^ s.c
  let v1676 := s.a &&& v1675
  let v1677 := v1676 ^^^ (s.b &&& s.c)
  let v1678 := v1673 + v1677
  let v1679 := v1668 + s.d
  let v1680 := v1678 + v1668
  E[%1642 := .value v1642,
    %1643 := .value v1643,
    %1644 := .value v1644,
    %1645 := .value v1645,
    %1646 := .value v1646,
    %1647 := .value v1647,
    %1648 := .value v1648,
    %1649 := .value v1649,
    %1650 := .value v1650,
    %1651 := .value v1651,
    %1652 := .value v1652,
    %1653 := .value v1653,
    %1654 := .value v1654,
    %1655 := .value v1655,
    %1656 := .value v1656,
    %1657 := .value v1657,
    %1658 := .value v1658,
    %1659 := .value v1659,
    %1660 := .value v1660,
    %1661 := .value v1661,
    %1662 := .value v1662,
    %1663 := .value v1663,
    %1664 := .value v1664,
    %1665 := .value v1665,
    %1666 := .value v1666,
    %1667 := .value v1667,
    %1668 := .value v1668,
    %1669 := .value v1669,
    %1670 := .value v1670,
    %1671 := .value v1671,
    %1672 := .value v1672,
    %1673 := .value v1673,
    %1674 := .value v1674,
    %1675 := .value v1675,
    %1676 := .value v1676,
    %1677 := .value v1677,
    %1678 := .value v1678,
    %1679 := .value v1679,
    %1680 := .value v1680]

def fullOut41 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1642 := (w 26).rotateRight 1
  let v1643 := (w 26).rotateRight 8
  let v1644 := v1642 ^^^ v1643
  let v1645 := (w 26) >>> 7
  let v1646 := v1644 ^^^ v1645
  let v1647 := (w 39).rotateRight 19
  let v1648 := (w 39).rotateRight 61
  let v1649 := v1647 ^^^ v1648
  let v1650 := (w 39) >>> 6
  let v1651 := v1649 ^^^ v1650
  let v1652 := v1646 + (w 25)
  let v1653 := v1652 + (w 34)
  let v1654 := v1653 + v1651
  let v1655 := s.e.rotateRight 14
  let v1656 := s.e.rotateRight 18
  let v1657 := v1655 ^^^ v1656
  let v1658 := s.e.rotateRight 41
  let v1659 := v1657 ^^^ v1658
  let v1660 := s.e &&& s.f
  let v1661 := s.e ^^^ (-1 : Word)
  let v1662 := s.g &&& v1661
  let v1663 := v1660 ||| v1662
  let v1664 := k
  let v1665 := v1654 + v1664
  let v1666 := v1665 + s.h
  let v1667 := v1666 + v1663
  let v1668 := v1667 + v1659
  let v1669 := s.a.rotateRight 28
  let v1670 := s.a.rotateRight 34
  let v1671 := v1669 ^^^ v1670
  let v1672 := s.a.rotateRight 39
  let v1673 := v1671 ^^^ v1672
  let v1674 := s.a &&& s.b
  let v1675 := s.b ^^^ s.c
  let v1676 := s.a &&& v1675
  let v1677 := v1676 ^^^ (s.b &&& s.c)
  let v1678 := v1673 + v1677
  let v1679 := v1668 + s.d
  let v1680 := v1678 + v1668
  ⟨v1680, s.a, s.b, s.c, v1679, s.e, s.f, s.g⟩

theorem fullOut41_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut41 s w k = Spec.round s (w 41) k := by
  have hw41 := hw 41 (by decide) (by decide)
  dsimp only [fullOut41, Spec.round]
  rw [hw41]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv41_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1642 E (fullEnv41 E s w k) := by
  unfold fullEnv41
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv41_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv41 E s w k) := by
  exact (fullEnv41_before E s w k).frame (by decide)

theorem full_body41 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready41 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 328#64) 64)
    (hk : state.mem.readAt (kp.add 328#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1442 |>.take 39) state =
      .value (fullEnv41 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv41, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k41, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready41 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready41 E s w) (hw : ScheduleReady w) :
    Ready42 (fullEnv41 E s w k) (Spec.round s (w 41) k) w := by
  have hb := fullEnv41_before E s w k
  have hout := fullOut41_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv41, fullOut41, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1641 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1602 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1563 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv41, fullOut41, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1640 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1601 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1562 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv41, Spec.round, mlir_env]
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
  · rw [hb.read_val 1615 (by decide) (by rfl)]; exact h.w40
  · have hwr := hw 41 (by decide) (by decide)
    simp [fullEnv41, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step41 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready41 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1442 |>.take 39) state =
      .value (E', state) ∧
      Ready42 E' (Spec.round s (w 41) (constants.toList.getD 41 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 41 0
  have hf := fullEnv41_frame E s w k
  refine ⟨fullEnv41 E s w k,
    full_body41 E state s w kp k h hc (hk 41).1 (hk 41).2,
    full_ready41 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
