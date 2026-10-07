import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1715..1753: round 48. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv48 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1915 := (w 33).rotateRight 1
  let v1916 := (w 33).rotateRight 8
  let v1917 := v1915 ^^^ v1916
  let v1918 := (w 33) >>> 7
  let v1919 := v1917 ^^^ v1918
  let v1920 := (w 46).rotateRight 19
  let v1921 := (w 46).rotateRight 61
  let v1922 := v1920 ^^^ v1921
  let v1923 := (w 46) >>> 6
  let v1924 := v1922 ^^^ v1923
  let v1925 := v1919 + (w 32)
  let v1926 := v1925 + (w 41)
  let v1927 := v1926 + v1924
  let v1928 := s.e.rotateRight 14
  let v1929 := s.e.rotateRight 18
  let v1930 := v1928 ^^^ v1929
  let v1931 := s.e.rotateRight 41
  let v1932 := v1930 ^^^ v1931
  let v1933 := s.e &&& s.f
  let v1934 := s.e ^^^ (-1 : Word)
  let v1935 := s.g &&& v1934
  let v1936 := v1933 ||| v1935
  let v1937 := k
  let v1938 := v1927 + v1937
  let v1939 := v1938 + s.h
  let v1940 := v1939 + v1936
  let v1941 := v1940 + v1932
  let v1942 := s.a.rotateRight 28
  let v1943 := s.a.rotateRight 34
  let v1944 := v1942 ^^^ v1943
  let v1945 := s.a.rotateRight 39
  let v1946 := v1944 ^^^ v1945
  let v1947 := s.a &&& s.b
  let v1948 := s.b ^^^ s.c
  let v1949 := s.a &&& v1948
  let v1950 := v1949 ^^^ (s.b &&& s.c)
  let v1951 := v1946 + v1950
  let v1952 := v1941 + s.d
  let v1953 := v1951 + v1941
  E[%1915 := .value v1915,
    %1916 := .value v1916,
    %1917 := .value v1917,
    %1918 := .value v1918,
    %1919 := .value v1919,
    %1920 := .value v1920,
    %1921 := .value v1921,
    %1922 := .value v1922,
    %1923 := .value v1923,
    %1924 := .value v1924,
    %1925 := .value v1925,
    %1926 := .value v1926,
    %1927 := .value v1927,
    %1928 := .value v1928,
    %1929 := .value v1929,
    %1930 := .value v1930,
    %1931 := .value v1931,
    %1932 := .value v1932,
    %1933 := .value v1933,
    %1934 := .value v1934,
    %1935 := .value v1935,
    %1936 := .value v1936,
    %1937 := .value v1937,
    %1938 := .value v1938,
    %1939 := .value v1939,
    %1940 := .value v1940,
    %1941 := .value v1941,
    %1942 := .value v1942,
    %1943 := .value v1943,
    %1944 := .value v1944,
    %1945 := .value v1945,
    %1946 := .value v1946,
    %1947 := .value v1947,
    %1948 := .value v1948,
    %1949 := .value v1949,
    %1950 := .value v1950,
    %1951 := .value v1951,
    %1952 := .value v1952,
    %1953 := .value v1953]

def fullOut48 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1915 := (w 33).rotateRight 1
  let v1916 := (w 33).rotateRight 8
  let v1917 := v1915 ^^^ v1916
  let v1918 := (w 33) >>> 7
  let v1919 := v1917 ^^^ v1918
  let v1920 := (w 46).rotateRight 19
  let v1921 := (w 46).rotateRight 61
  let v1922 := v1920 ^^^ v1921
  let v1923 := (w 46) >>> 6
  let v1924 := v1922 ^^^ v1923
  let v1925 := v1919 + (w 32)
  let v1926 := v1925 + (w 41)
  let v1927 := v1926 + v1924
  let v1928 := s.e.rotateRight 14
  let v1929 := s.e.rotateRight 18
  let v1930 := v1928 ^^^ v1929
  let v1931 := s.e.rotateRight 41
  let v1932 := v1930 ^^^ v1931
  let v1933 := s.e &&& s.f
  let v1934 := s.e ^^^ (-1 : Word)
  let v1935 := s.g &&& v1934
  let v1936 := v1933 ||| v1935
  let v1937 := k
  let v1938 := v1927 + v1937
  let v1939 := v1938 + s.h
  let v1940 := v1939 + v1936
  let v1941 := v1940 + v1932
  let v1942 := s.a.rotateRight 28
  let v1943 := s.a.rotateRight 34
  let v1944 := v1942 ^^^ v1943
  let v1945 := s.a.rotateRight 39
  let v1946 := v1944 ^^^ v1945
  let v1947 := s.a &&& s.b
  let v1948 := s.b ^^^ s.c
  let v1949 := s.a &&& v1948
  let v1950 := v1949 ^^^ (s.b &&& s.c)
  let v1951 := v1946 + v1950
  let v1952 := v1941 + s.d
  let v1953 := v1951 + v1941
  ⟨v1953, s.a, s.b, s.c, v1952, s.e, s.f, s.g⟩

theorem fullOut48_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut48 s w k = Spec.round s (w 48) k := by
  have hw48 := hw 48 (by decide) (by decide)
  dsimp only [fullOut48, Spec.round]
  rw [hw48]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv48_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1915 E (fullEnv48 E s w k) := by
  unfold fullEnv48
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv48_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv48 E s w k) := by
  exact (fullEnv48_before E s w k).frame (by decide)

theorem full_body48 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready48 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 384#64) 64)
    (hk : state.mem.readAt (kp.add 384#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1715 |>.take 39) state =
      .value (fullEnv48 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv48, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w32, h.w33, h.w34, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k48, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready48 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready48 E s w) (hw : ScheduleReady w) :
    Ready49 (fullEnv48 E s w k) (Spec.round s (w 48) k) w := by
  have hb := fullEnv48_before E s w k
  have hout := fullOut48_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv48, fullOut48, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1914 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1875 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1836 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv48, fullOut48, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1913 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1874 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1835 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv48, Spec.round, mlir_env]
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
  · rw [hb.read_val 1888 (by decide) (by rfl)]; exact h.w47
  · have hwr := hw 48 (by decide) (by decide)
    simp [fullEnv48, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step48 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready48 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1715 |>.take 39) state =
      .value (E', state) ∧
      Ready49 E' (Spec.round s (w 48) (constants.toList.getD 48 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 48 0
  have hf := fullEnv48_frame E s w k
  refine ⟨fullEnv48 E s w k,
    full_body48 E state s w kp k h hc (hk 48).1 (hk 48).2,
    full_ready48 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
