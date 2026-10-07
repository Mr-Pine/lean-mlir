import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1520..1558: round 43. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv43 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1720 := (w 28).rotateRight 1
  let v1721 := (w 28).rotateRight 8
  let v1722 := v1720 ^^^ v1721
  let v1723 := (w 28) >>> 7
  let v1724 := v1722 ^^^ v1723
  let v1725 := (w 41).rotateRight 19
  let v1726 := (w 41).rotateRight 61
  let v1727 := v1725 ^^^ v1726
  let v1728 := (w 41) >>> 6
  let v1729 := v1727 ^^^ v1728
  let v1730 := v1724 + (w 27)
  let v1731 := v1730 + (w 36)
  let v1732 := v1731 + v1729
  let v1733 := s.e.rotateRight 14
  let v1734 := s.e.rotateRight 18
  let v1735 := v1733 ^^^ v1734
  let v1736 := s.e.rotateRight 41
  let v1737 := v1735 ^^^ v1736
  let v1738 := s.e &&& s.f
  let v1739 := s.e ^^^ (-1 : Word)
  let v1740 := s.g &&& v1739
  let v1741 := v1738 ||| v1740
  let v1742 := k
  let v1743 := v1732 + v1742
  let v1744 := v1743 + s.h
  let v1745 := v1744 + v1741
  let v1746 := v1745 + v1737
  let v1747 := s.a.rotateRight 28
  let v1748 := s.a.rotateRight 34
  let v1749 := v1747 ^^^ v1748
  let v1750 := s.a.rotateRight 39
  let v1751 := v1749 ^^^ v1750
  let v1752 := s.a &&& s.b
  let v1753 := s.b ^^^ s.c
  let v1754 := s.a &&& v1753
  let v1755 := v1754 ^^^ (s.b &&& s.c)
  let v1756 := v1751 + v1755
  let v1757 := v1746 + s.d
  let v1758 := v1756 + v1746
  E[%1720 := .value v1720,
    %1721 := .value v1721,
    %1722 := .value v1722,
    %1723 := .value v1723,
    %1724 := .value v1724,
    %1725 := .value v1725,
    %1726 := .value v1726,
    %1727 := .value v1727,
    %1728 := .value v1728,
    %1729 := .value v1729,
    %1730 := .value v1730,
    %1731 := .value v1731,
    %1732 := .value v1732,
    %1733 := .value v1733,
    %1734 := .value v1734,
    %1735 := .value v1735,
    %1736 := .value v1736,
    %1737 := .value v1737,
    %1738 := .value v1738,
    %1739 := .value v1739,
    %1740 := .value v1740,
    %1741 := .value v1741,
    %1742 := .value v1742,
    %1743 := .value v1743,
    %1744 := .value v1744,
    %1745 := .value v1745,
    %1746 := .value v1746,
    %1747 := .value v1747,
    %1748 := .value v1748,
    %1749 := .value v1749,
    %1750 := .value v1750,
    %1751 := .value v1751,
    %1752 := .value v1752,
    %1753 := .value v1753,
    %1754 := .value v1754,
    %1755 := .value v1755,
    %1756 := .value v1756,
    %1757 := .value v1757,
    %1758 := .value v1758]

def fullOut43 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1720 := (w 28).rotateRight 1
  let v1721 := (w 28).rotateRight 8
  let v1722 := v1720 ^^^ v1721
  let v1723 := (w 28) >>> 7
  let v1724 := v1722 ^^^ v1723
  let v1725 := (w 41).rotateRight 19
  let v1726 := (w 41).rotateRight 61
  let v1727 := v1725 ^^^ v1726
  let v1728 := (w 41) >>> 6
  let v1729 := v1727 ^^^ v1728
  let v1730 := v1724 + (w 27)
  let v1731 := v1730 + (w 36)
  let v1732 := v1731 + v1729
  let v1733 := s.e.rotateRight 14
  let v1734 := s.e.rotateRight 18
  let v1735 := v1733 ^^^ v1734
  let v1736 := s.e.rotateRight 41
  let v1737 := v1735 ^^^ v1736
  let v1738 := s.e &&& s.f
  let v1739 := s.e ^^^ (-1 : Word)
  let v1740 := s.g &&& v1739
  let v1741 := v1738 ||| v1740
  let v1742 := k
  let v1743 := v1732 + v1742
  let v1744 := v1743 + s.h
  let v1745 := v1744 + v1741
  let v1746 := v1745 + v1737
  let v1747 := s.a.rotateRight 28
  let v1748 := s.a.rotateRight 34
  let v1749 := v1747 ^^^ v1748
  let v1750 := s.a.rotateRight 39
  let v1751 := v1749 ^^^ v1750
  let v1752 := s.a &&& s.b
  let v1753 := s.b ^^^ s.c
  let v1754 := s.a &&& v1753
  let v1755 := v1754 ^^^ (s.b &&& s.c)
  let v1756 := v1751 + v1755
  let v1757 := v1746 + s.d
  let v1758 := v1756 + v1746
  ⟨v1758, s.a, s.b, s.c, v1757, s.e, s.f, s.g⟩

theorem fullOut43_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut43 s w k = Spec.round s (w 43) k := by
  have hw43 := hw 43 (by decide) (by decide)
  dsimp only [fullOut43, Spec.round]
  rw [hw43]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv43_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1720 E (fullEnv43 E s w k) := by
  unfold fullEnv43
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv43_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv43 E s w k) := by
  exact (fullEnv43_before E s w k).frame (by decide)

theorem full_body43 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready43 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 344#64) 64)
    (hk : state.mem.readAt (kp.add 344#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1520 |>.take 39) state =
      .value (fullEnv43 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv43, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k43, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready43 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready43 E s w) (hw : ScheduleReady w) :
    Ready44 (fullEnv43 E s w k) (Spec.round s (w 43) k) w := by
  have hb := fullEnv43_before E s w k
  have hout := fullOut43_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv43, fullOut43, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1719 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1680 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1641 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv43, fullOut43, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1718 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1679 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1640 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv43, Spec.round, mlir_env]
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
  · rw [hb.read_val 1654 (by decide) (by rfl)]; exact h.w41
  · rw [hb.read_val 1693 (by decide) (by rfl)]; exact h.w42
  · have hwr := hw 43 (by decide) (by decide)
    simp [fullEnv43, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step43 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready43 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1520 |>.take 39) state =
      .value (E', state) ∧
      Ready44 E' (Spec.round s (w 43) (constants.toList.getD 43 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 43 0
  have hf := fullEnv43_frame E s w k
  refine ⟨fullEnv43 E s w k,
    full_body43 E state s w kp k h hc (hk 43).1 (hk 43).2,
    full_ready43 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
