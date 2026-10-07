import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1559..1597: round 44. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv44 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1759 := (w 29).rotateRight 1
  let v1760 := (w 29).rotateRight 8
  let v1761 := v1759 ^^^ v1760
  let v1762 := (w 29) >>> 7
  let v1763 := v1761 ^^^ v1762
  let v1764 := (w 42).rotateRight 19
  let v1765 := (w 42).rotateRight 61
  let v1766 := v1764 ^^^ v1765
  let v1767 := (w 42) >>> 6
  let v1768 := v1766 ^^^ v1767
  let v1769 := v1763 + (w 28)
  let v1770 := v1769 + (w 37)
  let v1771 := v1770 + v1768
  let v1772 := s.e.rotateRight 14
  let v1773 := s.e.rotateRight 18
  let v1774 := v1772 ^^^ v1773
  let v1775 := s.e.rotateRight 41
  let v1776 := v1774 ^^^ v1775
  let v1777 := s.e &&& s.f
  let v1778 := s.e ^^^ (-1 : Word)
  let v1779 := s.g &&& v1778
  let v1780 := v1777 ||| v1779
  let v1781 := k
  let v1782 := v1771 + v1781
  let v1783 := v1782 + s.h
  let v1784 := v1783 + v1780
  let v1785 := v1784 + v1776
  let v1786 := s.a.rotateRight 28
  let v1787 := s.a.rotateRight 34
  let v1788 := v1786 ^^^ v1787
  let v1789 := s.a.rotateRight 39
  let v1790 := v1788 ^^^ v1789
  let v1791 := s.a &&& s.b
  let v1792 := s.b ^^^ s.c
  let v1793 := s.a &&& v1792
  let v1794 := v1793 ^^^ (s.b &&& s.c)
  let v1795 := v1790 + v1794
  let v1796 := v1785 + s.d
  let v1797 := v1795 + v1785
  E[%1759 := .value v1759,
    %1760 := .value v1760,
    %1761 := .value v1761,
    %1762 := .value v1762,
    %1763 := .value v1763,
    %1764 := .value v1764,
    %1765 := .value v1765,
    %1766 := .value v1766,
    %1767 := .value v1767,
    %1768 := .value v1768,
    %1769 := .value v1769,
    %1770 := .value v1770,
    %1771 := .value v1771,
    %1772 := .value v1772,
    %1773 := .value v1773,
    %1774 := .value v1774,
    %1775 := .value v1775,
    %1776 := .value v1776,
    %1777 := .value v1777,
    %1778 := .value v1778,
    %1779 := .value v1779,
    %1780 := .value v1780,
    %1781 := .value v1781,
    %1782 := .value v1782,
    %1783 := .value v1783,
    %1784 := .value v1784,
    %1785 := .value v1785,
    %1786 := .value v1786,
    %1787 := .value v1787,
    %1788 := .value v1788,
    %1789 := .value v1789,
    %1790 := .value v1790,
    %1791 := .value v1791,
    %1792 := .value v1792,
    %1793 := .value v1793,
    %1794 := .value v1794,
    %1795 := .value v1795,
    %1796 := .value v1796,
    %1797 := .value v1797]

def fullOut44 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1759 := (w 29).rotateRight 1
  let v1760 := (w 29).rotateRight 8
  let v1761 := v1759 ^^^ v1760
  let v1762 := (w 29) >>> 7
  let v1763 := v1761 ^^^ v1762
  let v1764 := (w 42).rotateRight 19
  let v1765 := (w 42).rotateRight 61
  let v1766 := v1764 ^^^ v1765
  let v1767 := (w 42) >>> 6
  let v1768 := v1766 ^^^ v1767
  let v1769 := v1763 + (w 28)
  let v1770 := v1769 + (w 37)
  let v1771 := v1770 + v1768
  let v1772 := s.e.rotateRight 14
  let v1773 := s.e.rotateRight 18
  let v1774 := v1772 ^^^ v1773
  let v1775 := s.e.rotateRight 41
  let v1776 := v1774 ^^^ v1775
  let v1777 := s.e &&& s.f
  let v1778 := s.e ^^^ (-1 : Word)
  let v1779 := s.g &&& v1778
  let v1780 := v1777 ||| v1779
  let v1781 := k
  let v1782 := v1771 + v1781
  let v1783 := v1782 + s.h
  let v1784 := v1783 + v1780
  let v1785 := v1784 + v1776
  let v1786 := s.a.rotateRight 28
  let v1787 := s.a.rotateRight 34
  let v1788 := v1786 ^^^ v1787
  let v1789 := s.a.rotateRight 39
  let v1790 := v1788 ^^^ v1789
  let v1791 := s.a &&& s.b
  let v1792 := s.b ^^^ s.c
  let v1793 := s.a &&& v1792
  let v1794 := v1793 ^^^ (s.b &&& s.c)
  let v1795 := v1790 + v1794
  let v1796 := v1785 + s.d
  let v1797 := v1795 + v1785
  ⟨v1797, s.a, s.b, s.c, v1796, s.e, s.f, s.g⟩

theorem fullOut44_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut44 s w k = Spec.round s (w 44) k := by
  have hw44 := hw 44 (by decide) (by decide)
  dsimp only [fullOut44, Spec.round]
  rw [hw44]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv44_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1759 E (fullEnv44 E s w k) := by
  unfold fullEnv44
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv44_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv44 E s w k) := by
  exact (fullEnv44_before E s w k).frame (by decide)

theorem full_body44 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready44 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 352#64) 64)
    (hk : state.mem.readAt (kp.add 352#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1559 |>.take 39) state =
      .value (fullEnv44 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv44, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k44, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready44 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready44 E s w) (hw : ScheduleReady w) :
    Ready45 (fullEnv44 E s w k) (Spec.round s (w 44) k) w := by
  have hb := fullEnv44_before E s w k
  have hout := fullOut44_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv44, fullOut44, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1758 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1719 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1680 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv44, fullOut44, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1757 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1718 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1679 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv44, Spec.round, mlir_env]
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
  · rw [hb.read_val 1732 (by decide) (by rfl)]; exact h.w43
  · have hwr := hw 44 (by decide) (by decide)
    simp [fullEnv44, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step44 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready44 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1559 |>.take 39) state =
      .value (E', state) ∧
      Ready45 E' (Spec.round s (w 44) (constants.toList.getD 44 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 44 0
  have hf := fullEnv44_frame E s w k
  refine ⟨fullEnv44 E s w k,
    full_body44 E state s w kp k h hc (hk 44).1 (hk 44).2,
    full_ready44 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
