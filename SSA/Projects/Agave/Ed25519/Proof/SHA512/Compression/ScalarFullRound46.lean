import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1637..1675: round 46. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv46 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1837 := (w 31).rotateRight 1
  let v1838 := (w 31).rotateRight 8
  let v1839 := v1837 ^^^ v1838
  let v1840 := (w 31) >>> 7
  let v1841 := v1839 ^^^ v1840
  let v1842 := (w 44).rotateRight 19
  let v1843 := (w 44).rotateRight 61
  let v1844 := v1842 ^^^ v1843
  let v1845 := (w 44) >>> 6
  let v1846 := v1844 ^^^ v1845
  let v1847 := v1841 + (w 30)
  let v1848 := v1847 + (w 39)
  let v1849 := v1848 + v1846
  let v1850 := s.e.rotateRight 14
  let v1851 := s.e.rotateRight 18
  let v1852 := v1850 ^^^ v1851
  let v1853 := s.e.rotateRight 41
  let v1854 := v1852 ^^^ v1853
  let v1855 := s.e &&& s.f
  let v1856 := s.e ^^^ (-1 : Word)
  let v1857 := s.g &&& v1856
  let v1858 := v1855 ||| v1857
  let v1859 := k
  let v1860 := v1849 + v1859
  let v1861 := v1860 + s.h
  let v1862 := v1861 + v1858
  let v1863 := v1862 + v1854
  let v1864 := s.a.rotateRight 28
  let v1865 := s.a.rotateRight 34
  let v1866 := v1864 ^^^ v1865
  let v1867 := s.a.rotateRight 39
  let v1868 := v1866 ^^^ v1867
  let v1869 := s.a &&& s.b
  let v1870 := s.b ^^^ s.c
  let v1871 := s.a &&& v1870
  let v1872 := v1871 ^^^ (s.b &&& s.c)
  let v1873 := v1868 + v1872
  let v1874 := v1863 + s.d
  let v1875 := v1873 + v1863
  E[%1837 := .value v1837,
    %1838 := .value v1838,
    %1839 := .value v1839,
    %1840 := .value v1840,
    %1841 := .value v1841,
    %1842 := .value v1842,
    %1843 := .value v1843,
    %1844 := .value v1844,
    %1845 := .value v1845,
    %1846 := .value v1846,
    %1847 := .value v1847,
    %1848 := .value v1848,
    %1849 := .value v1849,
    %1850 := .value v1850,
    %1851 := .value v1851,
    %1852 := .value v1852,
    %1853 := .value v1853,
    %1854 := .value v1854,
    %1855 := .value v1855,
    %1856 := .value v1856,
    %1857 := .value v1857,
    %1858 := .value v1858,
    %1859 := .value v1859,
    %1860 := .value v1860,
    %1861 := .value v1861,
    %1862 := .value v1862,
    %1863 := .value v1863,
    %1864 := .value v1864,
    %1865 := .value v1865,
    %1866 := .value v1866,
    %1867 := .value v1867,
    %1868 := .value v1868,
    %1869 := .value v1869,
    %1870 := .value v1870,
    %1871 := .value v1871,
    %1872 := .value v1872,
    %1873 := .value v1873,
    %1874 := .value v1874,
    %1875 := .value v1875]

def fullOut46 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1837 := (w 31).rotateRight 1
  let v1838 := (w 31).rotateRight 8
  let v1839 := v1837 ^^^ v1838
  let v1840 := (w 31) >>> 7
  let v1841 := v1839 ^^^ v1840
  let v1842 := (w 44).rotateRight 19
  let v1843 := (w 44).rotateRight 61
  let v1844 := v1842 ^^^ v1843
  let v1845 := (w 44) >>> 6
  let v1846 := v1844 ^^^ v1845
  let v1847 := v1841 + (w 30)
  let v1848 := v1847 + (w 39)
  let v1849 := v1848 + v1846
  let v1850 := s.e.rotateRight 14
  let v1851 := s.e.rotateRight 18
  let v1852 := v1850 ^^^ v1851
  let v1853 := s.e.rotateRight 41
  let v1854 := v1852 ^^^ v1853
  let v1855 := s.e &&& s.f
  let v1856 := s.e ^^^ (-1 : Word)
  let v1857 := s.g &&& v1856
  let v1858 := v1855 ||| v1857
  let v1859 := k
  let v1860 := v1849 + v1859
  let v1861 := v1860 + s.h
  let v1862 := v1861 + v1858
  let v1863 := v1862 + v1854
  let v1864 := s.a.rotateRight 28
  let v1865 := s.a.rotateRight 34
  let v1866 := v1864 ^^^ v1865
  let v1867 := s.a.rotateRight 39
  let v1868 := v1866 ^^^ v1867
  let v1869 := s.a &&& s.b
  let v1870 := s.b ^^^ s.c
  let v1871 := s.a &&& v1870
  let v1872 := v1871 ^^^ (s.b &&& s.c)
  let v1873 := v1868 + v1872
  let v1874 := v1863 + s.d
  let v1875 := v1873 + v1863
  ⟨v1875, s.a, s.b, s.c, v1874, s.e, s.f, s.g⟩

theorem fullOut46_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut46 s w k = Spec.round s (w 46) k := by
  have hw46 := hw 46 (by decide) (by decide)
  dsimp only [fullOut46, Spec.round]
  rw [hw46]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv46_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1837 E (fullEnv46 E s w k) := by
  unfold fullEnv46
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv46_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv46 E s w k) := by
  exact (fullEnv46_before E s w k).frame (by decide)

theorem full_body46 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready46 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 368#64) 64)
    (hk : state.mem.readAt (kp.add 368#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1637 |>.take 39) state =
      .value (fullEnv46 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv46, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w30, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k46, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready46 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready46 E s w) (hw : ScheduleReady w) :
    Ready47 (fullEnv46 E s w k) (Spec.round s (w 46) k) w := by
  have hb := fullEnv46_before E s w k
  have hout := fullOut46_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv46, fullOut46, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1836 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1797 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1758 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv46, fullOut46, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1835 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1796 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1757 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv46, Spec.round, mlir_env]
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
  · rw [hb.read_val 1810 (by decide) (by rfl)]; exact h.w45
  · have hwr := hw 46 (by decide) (by decide)
    simp [fullEnv46, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step46 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready46 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1637 |>.take 39) state =
      .value (E', state) ∧
      Ready47 E' (Spec.round s (w 46) (constants.toList.getD 46 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 46 0
  have hf := fullEnv46_frame E s w k
  refine ⟨fullEnv46 E s w k,
    full_body46 E state s w kp k h hc (hk 46).1 (hk 46).2,
    full_ready46 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
