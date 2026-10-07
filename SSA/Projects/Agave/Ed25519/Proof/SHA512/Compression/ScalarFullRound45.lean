import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1598..1636: round 45. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv45 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1798 := (w 30).rotateRight 1
  let v1799 := (w 30).rotateRight 8
  let v1800 := v1798 ^^^ v1799
  let v1801 := (w 30) >>> 7
  let v1802 := v1800 ^^^ v1801
  let v1803 := (w 43).rotateRight 19
  let v1804 := (w 43).rotateRight 61
  let v1805 := v1803 ^^^ v1804
  let v1806 := (w 43) >>> 6
  let v1807 := v1805 ^^^ v1806
  let v1808 := v1802 + (w 29)
  let v1809 := v1808 + (w 38)
  let v1810 := v1809 + v1807
  let v1811 := s.e.rotateRight 14
  let v1812 := s.e.rotateRight 18
  let v1813 := v1811 ^^^ v1812
  let v1814 := s.e.rotateRight 41
  let v1815 := v1813 ^^^ v1814
  let v1816 := s.e &&& s.f
  let v1817 := s.e ^^^ (-1 : Word)
  let v1818 := s.g &&& v1817
  let v1819 := v1816 ||| v1818
  let v1820 := k
  let v1821 := v1810 + v1820
  let v1822 := v1821 + s.h
  let v1823 := v1822 + v1819
  let v1824 := v1823 + v1815
  let v1825 := s.a.rotateRight 28
  let v1826 := s.a.rotateRight 34
  let v1827 := v1825 ^^^ v1826
  let v1828 := s.a.rotateRight 39
  let v1829 := v1827 ^^^ v1828
  let v1830 := s.a &&& s.b
  let v1831 := s.b ^^^ s.c
  let v1832 := s.a &&& v1831
  let v1833 := v1832 ^^^ (s.b &&& s.c)
  let v1834 := v1829 + v1833
  let v1835 := v1824 + s.d
  let v1836 := v1834 + v1824
  E[%1798 := .value v1798,
    %1799 := .value v1799,
    %1800 := .value v1800,
    %1801 := .value v1801,
    %1802 := .value v1802,
    %1803 := .value v1803,
    %1804 := .value v1804,
    %1805 := .value v1805,
    %1806 := .value v1806,
    %1807 := .value v1807,
    %1808 := .value v1808,
    %1809 := .value v1809,
    %1810 := .value v1810,
    %1811 := .value v1811,
    %1812 := .value v1812,
    %1813 := .value v1813,
    %1814 := .value v1814,
    %1815 := .value v1815,
    %1816 := .value v1816,
    %1817 := .value v1817,
    %1818 := .value v1818,
    %1819 := .value v1819,
    %1820 := .value v1820,
    %1821 := .value v1821,
    %1822 := .value v1822,
    %1823 := .value v1823,
    %1824 := .value v1824,
    %1825 := .value v1825,
    %1826 := .value v1826,
    %1827 := .value v1827,
    %1828 := .value v1828,
    %1829 := .value v1829,
    %1830 := .value v1830,
    %1831 := .value v1831,
    %1832 := .value v1832,
    %1833 := .value v1833,
    %1834 := .value v1834,
    %1835 := .value v1835,
    %1836 := .value v1836]

def fullOut45 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1798 := (w 30).rotateRight 1
  let v1799 := (w 30).rotateRight 8
  let v1800 := v1798 ^^^ v1799
  let v1801 := (w 30) >>> 7
  let v1802 := v1800 ^^^ v1801
  let v1803 := (w 43).rotateRight 19
  let v1804 := (w 43).rotateRight 61
  let v1805 := v1803 ^^^ v1804
  let v1806 := (w 43) >>> 6
  let v1807 := v1805 ^^^ v1806
  let v1808 := v1802 + (w 29)
  let v1809 := v1808 + (w 38)
  let v1810 := v1809 + v1807
  let v1811 := s.e.rotateRight 14
  let v1812 := s.e.rotateRight 18
  let v1813 := v1811 ^^^ v1812
  let v1814 := s.e.rotateRight 41
  let v1815 := v1813 ^^^ v1814
  let v1816 := s.e &&& s.f
  let v1817 := s.e ^^^ (-1 : Word)
  let v1818 := s.g &&& v1817
  let v1819 := v1816 ||| v1818
  let v1820 := k
  let v1821 := v1810 + v1820
  let v1822 := v1821 + s.h
  let v1823 := v1822 + v1819
  let v1824 := v1823 + v1815
  let v1825 := s.a.rotateRight 28
  let v1826 := s.a.rotateRight 34
  let v1827 := v1825 ^^^ v1826
  let v1828 := s.a.rotateRight 39
  let v1829 := v1827 ^^^ v1828
  let v1830 := s.a &&& s.b
  let v1831 := s.b ^^^ s.c
  let v1832 := s.a &&& v1831
  let v1833 := v1832 ^^^ (s.b &&& s.c)
  let v1834 := v1829 + v1833
  let v1835 := v1824 + s.d
  let v1836 := v1834 + v1824
  ⟨v1836, s.a, s.b, s.c, v1835, s.e, s.f, s.g⟩

theorem fullOut45_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut45 s w k = Spec.round s (w 45) k := by
  have hw45 := hw 45 (by decide) (by decide)
  dsimp only [fullOut45, Spec.round]
  rw [hw45]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv45_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1798 E (fullEnv45 E s w k) := by
  unfold fullEnv45
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv45_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv45 E s w k) := by
  exact (fullEnv45_before E s w k).frame (by decide)

theorem full_body45 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready45 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 360#64) 64)
    (hk : state.mem.readAt (kp.add 360#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1598 |>.take 39) state =
      .value (fullEnv45 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv45, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w29, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k45, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready45 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready45 E s w) (hw : ScheduleReady w) :
    Ready46 (fullEnv45 E s w k) (Spec.round s (w 45) k) w := by
  have hb := fullEnv45_before E s w k
  have hout := fullOut45_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv45, fullOut45, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1797 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1758 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1719 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv45, fullOut45, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1796 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1757 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1718 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv45, Spec.round, mlir_env]
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
  · rw [hb.read_val 1771 (by decide) (by rfl)]; exact h.w44
  · have hwr := hw 45 (by decide) (by decide)
    simp [fullEnv45, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step45 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready45 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1598 |>.take 39) state =
      .value (E', state) ∧
      Ready46 E' (Spec.round s (w 45) (constants.toList.getD 45 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 45 0
  have hf := fullEnv45_frame E s w k
  refine ⟨fullEnv45 E s w k,
    full_body45 E state s w kp k h hc (hk 45).1 (hk 45).2,
    full_ready45 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
