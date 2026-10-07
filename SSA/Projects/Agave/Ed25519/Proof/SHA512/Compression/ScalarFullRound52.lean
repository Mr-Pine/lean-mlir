import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1871..1909: round 52. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv52 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2071 := (w 37).rotateRight 1
  let v2072 := (w 37).rotateRight 8
  let v2073 := v2071 ^^^ v2072
  let v2074 := (w 37) >>> 7
  let v2075 := v2073 ^^^ v2074
  let v2076 := (w 50).rotateRight 19
  let v2077 := (w 50).rotateRight 61
  let v2078 := v2076 ^^^ v2077
  let v2079 := (w 50) >>> 6
  let v2080 := v2078 ^^^ v2079
  let v2081 := v2075 + (w 36)
  let v2082 := v2081 + (w 45)
  let v2083 := v2082 + v2080
  let v2084 := s.e.rotateRight 14
  let v2085 := s.e.rotateRight 18
  let v2086 := v2084 ^^^ v2085
  let v2087 := s.e.rotateRight 41
  let v2088 := v2086 ^^^ v2087
  let v2089 := s.e &&& s.f
  let v2090 := s.e ^^^ (-1 : Word)
  let v2091 := s.g &&& v2090
  let v2092 := v2089 ||| v2091
  let v2093 := k
  let v2094 := v2083 + v2093
  let v2095 := v2094 + s.h
  let v2096 := v2095 + v2092
  let v2097 := v2096 + v2088
  let v2098 := s.a.rotateRight 28
  let v2099 := s.a.rotateRight 34
  let v2100 := v2098 ^^^ v2099
  let v2101 := s.a.rotateRight 39
  let v2102 := v2100 ^^^ v2101
  let v2103 := s.a &&& s.b
  let v2104 := s.b ^^^ s.c
  let v2105 := s.a &&& v2104
  let v2106 := v2105 ^^^ (s.b &&& s.c)
  let v2107 := v2102 + v2106
  let v2108 := v2097 + s.d
  let v2109 := v2107 + v2097
  E[%2071 := .value v2071,
    %2072 := .value v2072,
    %2073 := .value v2073,
    %2074 := .value v2074,
    %2075 := .value v2075,
    %2076 := .value v2076,
    %2077 := .value v2077,
    %2078 := .value v2078,
    %2079 := .value v2079,
    %2080 := .value v2080,
    %2081 := .value v2081,
    %2082 := .value v2082,
    %2083 := .value v2083,
    %2084 := .value v2084,
    %2085 := .value v2085,
    %2086 := .value v2086,
    %2087 := .value v2087,
    %2088 := .value v2088,
    %2089 := .value v2089,
    %2090 := .value v2090,
    %2091 := .value v2091,
    %2092 := .value v2092,
    %2093 := .value v2093,
    %2094 := .value v2094,
    %2095 := .value v2095,
    %2096 := .value v2096,
    %2097 := .value v2097,
    %2098 := .value v2098,
    %2099 := .value v2099,
    %2100 := .value v2100,
    %2101 := .value v2101,
    %2102 := .value v2102,
    %2103 := .value v2103,
    %2104 := .value v2104,
    %2105 := .value v2105,
    %2106 := .value v2106,
    %2107 := .value v2107,
    %2108 := .value v2108,
    %2109 := .value v2109]

def fullOut52 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2071 := (w 37).rotateRight 1
  let v2072 := (w 37).rotateRight 8
  let v2073 := v2071 ^^^ v2072
  let v2074 := (w 37) >>> 7
  let v2075 := v2073 ^^^ v2074
  let v2076 := (w 50).rotateRight 19
  let v2077 := (w 50).rotateRight 61
  let v2078 := v2076 ^^^ v2077
  let v2079 := (w 50) >>> 6
  let v2080 := v2078 ^^^ v2079
  let v2081 := v2075 + (w 36)
  let v2082 := v2081 + (w 45)
  let v2083 := v2082 + v2080
  let v2084 := s.e.rotateRight 14
  let v2085 := s.e.rotateRight 18
  let v2086 := v2084 ^^^ v2085
  let v2087 := s.e.rotateRight 41
  let v2088 := v2086 ^^^ v2087
  let v2089 := s.e &&& s.f
  let v2090 := s.e ^^^ (-1 : Word)
  let v2091 := s.g &&& v2090
  let v2092 := v2089 ||| v2091
  let v2093 := k
  let v2094 := v2083 + v2093
  let v2095 := v2094 + s.h
  let v2096 := v2095 + v2092
  let v2097 := v2096 + v2088
  let v2098 := s.a.rotateRight 28
  let v2099 := s.a.rotateRight 34
  let v2100 := v2098 ^^^ v2099
  let v2101 := s.a.rotateRight 39
  let v2102 := v2100 ^^^ v2101
  let v2103 := s.a &&& s.b
  let v2104 := s.b ^^^ s.c
  let v2105 := s.a &&& v2104
  let v2106 := v2105 ^^^ (s.b &&& s.c)
  let v2107 := v2102 + v2106
  let v2108 := v2097 + s.d
  let v2109 := v2107 + v2097
  ⟨v2109, s.a, s.b, s.c, v2108, s.e, s.f, s.g⟩

theorem fullOut52_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut52 s w k = Spec.round s (w 52) k := by
  have hw52 := hw 52 (by decide) (by decide)
  dsimp only [fullOut52, Spec.round]
  rw [hw52]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv52_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2071 E (fullEnv52 E s w k) := by
  unfold fullEnv52
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv52_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv52 E s w k) := by
  exact (fullEnv52_before E s w k).frame (by decide)

theorem full_body52 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready52 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 416#64) 64)
    (hk : state.mem.readAt (kp.add 416#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1871 |>.take 39) state =
      .value (fullEnv52 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv52, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w36, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k52, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready52 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready52 E s w) (hw : ScheduleReady w) :
    Ready53 (fullEnv52 E s w k) (Spec.round s (w 52) k) w := by
  have hb := fullEnv52_before E s w k
  have hout := fullOut52_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv52, fullOut52, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2070 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2031 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1992 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv52, fullOut52, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2069 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2030 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1991 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv52, Spec.round, mlir_env]
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
  · rw [hb.read_val 2044 (by decide) (by rfl)]; exact h.w51
  · have hwr := hw 52 (by decide) (by decide)
    simp [fullEnv52, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step52 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready52 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1871 |>.take 39) state =
      .value (E', state) ∧
      Ready53 E' (Spec.round s (w 52) (constants.toList.getD 52 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 52 0
  have hf := fullEnv52_frame E s w k
  refine ⟨fullEnv52 E s w k,
    full_body52 E state s w kp k h hc (hk 52).1 (hk 52).2,
    full_ready52 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
