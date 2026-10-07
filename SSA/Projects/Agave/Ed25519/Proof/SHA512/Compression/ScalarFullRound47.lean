import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1676..1714: round 47. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv47 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1876 := (w 32).rotateRight 1
  let v1877 := (w 32).rotateRight 8
  let v1878 := v1876 ^^^ v1877
  let v1879 := (w 32) >>> 7
  let v1880 := v1878 ^^^ v1879
  let v1881 := (w 45).rotateRight 19
  let v1882 := (w 45).rotateRight 61
  let v1883 := v1881 ^^^ v1882
  let v1884 := (w 45) >>> 6
  let v1885 := v1883 ^^^ v1884
  let v1886 := v1880 + (w 31)
  let v1887 := v1886 + (w 40)
  let v1888 := v1887 + v1885
  let v1889 := s.e.rotateRight 14
  let v1890 := s.e.rotateRight 18
  let v1891 := v1889 ^^^ v1890
  let v1892 := s.e.rotateRight 41
  let v1893 := v1891 ^^^ v1892
  let v1894 := s.e &&& s.f
  let v1895 := s.e ^^^ (-1 : Word)
  let v1896 := s.g &&& v1895
  let v1897 := v1894 ||| v1896
  let v1898 := k
  let v1899 := v1888 + v1898
  let v1900 := v1899 + s.h
  let v1901 := v1900 + v1897
  let v1902 := v1901 + v1893
  let v1903 := s.a.rotateRight 28
  let v1904 := s.a.rotateRight 34
  let v1905 := v1903 ^^^ v1904
  let v1906 := s.a.rotateRight 39
  let v1907 := v1905 ^^^ v1906
  let v1908 := s.a &&& s.b
  let v1909 := s.b ^^^ s.c
  let v1910 := s.a &&& v1909
  let v1911 := v1910 ^^^ (s.b &&& s.c)
  let v1912 := v1907 + v1911
  let v1913 := v1902 + s.d
  let v1914 := v1912 + v1902
  E[%1876 := .value v1876,
    %1877 := .value v1877,
    %1878 := .value v1878,
    %1879 := .value v1879,
    %1880 := .value v1880,
    %1881 := .value v1881,
    %1882 := .value v1882,
    %1883 := .value v1883,
    %1884 := .value v1884,
    %1885 := .value v1885,
    %1886 := .value v1886,
    %1887 := .value v1887,
    %1888 := .value v1888,
    %1889 := .value v1889,
    %1890 := .value v1890,
    %1891 := .value v1891,
    %1892 := .value v1892,
    %1893 := .value v1893,
    %1894 := .value v1894,
    %1895 := .value v1895,
    %1896 := .value v1896,
    %1897 := .value v1897,
    %1898 := .value v1898,
    %1899 := .value v1899,
    %1900 := .value v1900,
    %1901 := .value v1901,
    %1902 := .value v1902,
    %1903 := .value v1903,
    %1904 := .value v1904,
    %1905 := .value v1905,
    %1906 := .value v1906,
    %1907 := .value v1907,
    %1908 := .value v1908,
    %1909 := .value v1909,
    %1910 := .value v1910,
    %1911 := .value v1911,
    %1912 := .value v1912,
    %1913 := .value v1913,
    %1914 := .value v1914]

def fullOut47 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1876 := (w 32).rotateRight 1
  let v1877 := (w 32).rotateRight 8
  let v1878 := v1876 ^^^ v1877
  let v1879 := (w 32) >>> 7
  let v1880 := v1878 ^^^ v1879
  let v1881 := (w 45).rotateRight 19
  let v1882 := (w 45).rotateRight 61
  let v1883 := v1881 ^^^ v1882
  let v1884 := (w 45) >>> 6
  let v1885 := v1883 ^^^ v1884
  let v1886 := v1880 + (w 31)
  let v1887 := v1886 + (w 40)
  let v1888 := v1887 + v1885
  let v1889 := s.e.rotateRight 14
  let v1890 := s.e.rotateRight 18
  let v1891 := v1889 ^^^ v1890
  let v1892 := s.e.rotateRight 41
  let v1893 := v1891 ^^^ v1892
  let v1894 := s.e &&& s.f
  let v1895 := s.e ^^^ (-1 : Word)
  let v1896 := s.g &&& v1895
  let v1897 := v1894 ||| v1896
  let v1898 := k
  let v1899 := v1888 + v1898
  let v1900 := v1899 + s.h
  let v1901 := v1900 + v1897
  let v1902 := v1901 + v1893
  let v1903 := s.a.rotateRight 28
  let v1904 := s.a.rotateRight 34
  let v1905 := v1903 ^^^ v1904
  let v1906 := s.a.rotateRight 39
  let v1907 := v1905 ^^^ v1906
  let v1908 := s.a &&& s.b
  let v1909 := s.b ^^^ s.c
  let v1910 := s.a &&& v1909
  let v1911 := v1910 ^^^ (s.b &&& s.c)
  let v1912 := v1907 + v1911
  let v1913 := v1902 + s.d
  let v1914 := v1912 + v1902
  ⟨v1914, s.a, s.b, s.c, v1913, s.e, s.f, s.g⟩

theorem fullOut47_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut47 s w k = Spec.round s (w 47) k := by
  have hw47 := hw 47 (by decide) (by decide)
  dsimp only [fullOut47, Spec.round]
  rw [hw47]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv47_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1876 E (fullEnv47 E s w k) := by
  unfold fullEnv47
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv47_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv47 E s w k) := by
  exact (fullEnv47_before E s w k).frame (by decide)

theorem full_body47 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready47 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 376#64) 64)
    (hk : state.mem.readAt (kp.add 376#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1676 |>.take 39) state =
      .value (fullEnv47 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv47, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w31, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k47, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready47 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready47 E s w) (hw : ScheduleReady w) :
    Ready48 (fullEnv47 E s w k) (Spec.round s (w 47) k) w := by
  have hb := fullEnv47_before E s w k
  have hout := fullOut47_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv47, fullOut47, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1875 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1836 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1797 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv47, fullOut47, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1874 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1835 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1796 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv47, Spec.round, mlir_env]
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
  · rw [hb.read_val 1849 (by decide) (by rfl)]; exact h.w46
  · have hwr := hw 47 (by decide) (by decide)
    simp [fullEnv47, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step47 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready47 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1676 |>.take 39) state =
      .value (E', state) ∧
      Ready48 E' (Spec.round s (w 47) (constants.toList.getD 47 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 47 0
  have hf := fullEnv47_frame E s w k
  refine ⟨fullEnv47 E s w k,
    full_body47 E state s w kp k h hc (hk 47).1 (hk 47).2,
    full_ready47 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
