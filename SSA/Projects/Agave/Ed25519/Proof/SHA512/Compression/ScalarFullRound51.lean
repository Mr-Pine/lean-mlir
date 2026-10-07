import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1832..1870: round 51. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv51 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2032 := (w 36).rotateRight 1
  let v2033 := (w 36).rotateRight 8
  let v2034 := v2032 ^^^ v2033
  let v2035 := (w 36) >>> 7
  let v2036 := v2034 ^^^ v2035
  let v2037 := (w 49).rotateRight 19
  let v2038 := (w 49).rotateRight 61
  let v2039 := v2037 ^^^ v2038
  let v2040 := (w 49) >>> 6
  let v2041 := v2039 ^^^ v2040
  let v2042 := v2036 + (w 35)
  let v2043 := v2042 + (w 44)
  let v2044 := v2043 + v2041
  let v2045 := s.e.rotateRight 14
  let v2046 := s.e.rotateRight 18
  let v2047 := v2045 ^^^ v2046
  let v2048 := s.e.rotateRight 41
  let v2049 := v2047 ^^^ v2048
  let v2050 := s.e &&& s.f
  let v2051 := s.e ^^^ (-1 : Word)
  let v2052 := s.g &&& v2051
  let v2053 := v2050 ||| v2052
  let v2054 := k
  let v2055 := v2044 + v2054
  let v2056 := v2055 + s.h
  let v2057 := v2056 + v2053
  let v2058 := v2057 + v2049
  let v2059 := s.a.rotateRight 28
  let v2060 := s.a.rotateRight 34
  let v2061 := v2059 ^^^ v2060
  let v2062 := s.a.rotateRight 39
  let v2063 := v2061 ^^^ v2062
  let v2064 := s.a &&& s.b
  let v2065 := s.b ^^^ s.c
  let v2066 := s.a &&& v2065
  let v2067 := v2066 ^^^ (s.b &&& s.c)
  let v2068 := v2063 + v2067
  let v2069 := v2058 + s.d
  let v2070 := v2068 + v2058
  E[%2032 := .value v2032,
    %2033 := .value v2033,
    %2034 := .value v2034,
    %2035 := .value v2035,
    %2036 := .value v2036,
    %2037 := .value v2037,
    %2038 := .value v2038,
    %2039 := .value v2039,
    %2040 := .value v2040,
    %2041 := .value v2041,
    %2042 := .value v2042,
    %2043 := .value v2043,
    %2044 := .value v2044,
    %2045 := .value v2045,
    %2046 := .value v2046,
    %2047 := .value v2047,
    %2048 := .value v2048,
    %2049 := .value v2049,
    %2050 := .value v2050,
    %2051 := .value v2051,
    %2052 := .value v2052,
    %2053 := .value v2053,
    %2054 := .value v2054,
    %2055 := .value v2055,
    %2056 := .value v2056,
    %2057 := .value v2057,
    %2058 := .value v2058,
    %2059 := .value v2059,
    %2060 := .value v2060,
    %2061 := .value v2061,
    %2062 := .value v2062,
    %2063 := .value v2063,
    %2064 := .value v2064,
    %2065 := .value v2065,
    %2066 := .value v2066,
    %2067 := .value v2067,
    %2068 := .value v2068,
    %2069 := .value v2069,
    %2070 := .value v2070]

def fullOut51 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2032 := (w 36).rotateRight 1
  let v2033 := (w 36).rotateRight 8
  let v2034 := v2032 ^^^ v2033
  let v2035 := (w 36) >>> 7
  let v2036 := v2034 ^^^ v2035
  let v2037 := (w 49).rotateRight 19
  let v2038 := (w 49).rotateRight 61
  let v2039 := v2037 ^^^ v2038
  let v2040 := (w 49) >>> 6
  let v2041 := v2039 ^^^ v2040
  let v2042 := v2036 + (w 35)
  let v2043 := v2042 + (w 44)
  let v2044 := v2043 + v2041
  let v2045 := s.e.rotateRight 14
  let v2046 := s.e.rotateRight 18
  let v2047 := v2045 ^^^ v2046
  let v2048 := s.e.rotateRight 41
  let v2049 := v2047 ^^^ v2048
  let v2050 := s.e &&& s.f
  let v2051 := s.e ^^^ (-1 : Word)
  let v2052 := s.g &&& v2051
  let v2053 := v2050 ||| v2052
  let v2054 := k
  let v2055 := v2044 + v2054
  let v2056 := v2055 + s.h
  let v2057 := v2056 + v2053
  let v2058 := v2057 + v2049
  let v2059 := s.a.rotateRight 28
  let v2060 := s.a.rotateRight 34
  let v2061 := v2059 ^^^ v2060
  let v2062 := s.a.rotateRight 39
  let v2063 := v2061 ^^^ v2062
  let v2064 := s.a &&& s.b
  let v2065 := s.b ^^^ s.c
  let v2066 := s.a &&& v2065
  let v2067 := v2066 ^^^ (s.b &&& s.c)
  let v2068 := v2063 + v2067
  let v2069 := v2058 + s.d
  let v2070 := v2068 + v2058
  ⟨v2070, s.a, s.b, s.c, v2069, s.e, s.f, s.g⟩

theorem fullOut51_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut51 s w k = Spec.round s (w 51) k := by
  have hw51 := hw 51 (by decide) (by decide)
  dsimp only [fullOut51, Spec.round]
  rw [hw51]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv51_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2032 E (fullEnv51 E s w k) := by
  unfold fullEnv51
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv51_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv51 E s w k) := by
  exact (fullEnv51_before E s w k).frame (by decide)

theorem full_body51 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready51 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 408#64) 64)
    (hk : state.mem.readAt (kp.add 408#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1832 |>.take 39) state =
      .value (fullEnv51 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv51, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w35, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k51, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready51 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready51 E s w) (hw : ScheduleReady w) :
    Ready52 (fullEnv51 E s w k) (Spec.round s (w 51) k) w := by
  have hb := fullEnv51_before E s w k
  have hout := fullOut51_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv51, fullOut51, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2031 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1992 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1953 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv51, fullOut51, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2030 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1991 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1952 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv51, Spec.round, mlir_env]
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
  · rw [hb.read_val 1927 (by decide) (by rfl)]; exact h.w48
  · rw [hb.read_val 1966 (by decide) (by rfl)]; exact h.w49
  · rw [hb.read_val 2005 (by decide) (by rfl)]; exact h.w50
  · have hwr := hw 51 (by decide) (by decide)
    simp [fullEnv51, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step51 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready51 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1832 |>.take 39) state =
      .value (E', state) ∧
      Ready52 E' (Spec.round s (w 51) (constants.toList.getD 51 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 51 0
  have hf := fullEnv51_frame E s w k
  refine ⟨fullEnv51 E s w k,
    full_body51 E state s w kp k h hc (hk 51).1 (hk 51).2,
    full_ready51 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
