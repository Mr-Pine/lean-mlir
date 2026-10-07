import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1910..1948: round 53. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv53 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2110 := (w 38).rotateRight 1
  let v2111 := (w 38).rotateRight 8
  let v2112 := v2110 ^^^ v2111
  let v2113 := (w 38) >>> 7
  let v2114 := v2112 ^^^ v2113
  let v2115 := (w 51).rotateRight 19
  let v2116 := (w 51).rotateRight 61
  let v2117 := v2115 ^^^ v2116
  let v2118 := (w 51) >>> 6
  let v2119 := v2117 ^^^ v2118
  let v2120 := v2114 + (w 37)
  let v2121 := v2120 + (w 46)
  let v2122 := v2121 + v2119
  let v2123 := s.e.rotateRight 14
  let v2124 := s.e.rotateRight 18
  let v2125 := v2123 ^^^ v2124
  let v2126 := s.e.rotateRight 41
  let v2127 := v2125 ^^^ v2126
  let v2128 := s.e &&& s.f
  let v2129 := s.e ^^^ (-1 : Word)
  let v2130 := s.g &&& v2129
  let v2131 := v2128 ||| v2130
  let v2132 := k
  let v2133 := v2122 + v2132
  let v2134 := v2133 + s.h
  let v2135 := v2134 + v2131
  let v2136 := v2135 + v2127
  let v2137 := s.a.rotateRight 28
  let v2138 := s.a.rotateRight 34
  let v2139 := v2137 ^^^ v2138
  let v2140 := s.a.rotateRight 39
  let v2141 := v2139 ^^^ v2140
  let v2142 := s.a &&& s.b
  let v2143 := s.b ^^^ s.c
  let v2144 := s.a &&& v2143
  let v2145 := v2144 ^^^ (s.b &&& s.c)
  let v2146 := v2141 + v2145
  let v2147 := v2136 + s.d
  let v2148 := v2146 + v2136
  E[%2110 := .value v2110,
    %2111 := .value v2111,
    %2112 := .value v2112,
    %2113 := .value v2113,
    %2114 := .value v2114,
    %2115 := .value v2115,
    %2116 := .value v2116,
    %2117 := .value v2117,
    %2118 := .value v2118,
    %2119 := .value v2119,
    %2120 := .value v2120,
    %2121 := .value v2121,
    %2122 := .value v2122,
    %2123 := .value v2123,
    %2124 := .value v2124,
    %2125 := .value v2125,
    %2126 := .value v2126,
    %2127 := .value v2127,
    %2128 := .value v2128,
    %2129 := .value v2129,
    %2130 := .value v2130,
    %2131 := .value v2131,
    %2132 := .value v2132,
    %2133 := .value v2133,
    %2134 := .value v2134,
    %2135 := .value v2135,
    %2136 := .value v2136,
    %2137 := .value v2137,
    %2138 := .value v2138,
    %2139 := .value v2139,
    %2140 := .value v2140,
    %2141 := .value v2141,
    %2142 := .value v2142,
    %2143 := .value v2143,
    %2144 := .value v2144,
    %2145 := .value v2145,
    %2146 := .value v2146,
    %2147 := .value v2147,
    %2148 := .value v2148]

def fullOut53 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2110 := (w 38).rotateRight 1
  let v2111 := (w 38).rotateRight 8
  let v2112 := v2110 ^^^ v2111
  let v2113 := (w 38) >>> 7
  let v2114 := v2112 ^^^ v2113
  let v2115 := (w 51).rotateRight 19
  let v2116 := (w 51).rotateRight 61
  let v2117 := v2115 ^^^ v2116
  let v2118 := (w 51) >>> 6
  let v2119 := v2117 ^^^ v2118
  let v2120 := v2114 + (w 37)
  let v2121 := v2120 + (w 46)
  let v2122 := v2121 + v2119
  let v2123 := s.e.rotateRight 14
  let v2124 := s.e.rotateRight 18
  let v2125 := v2123 ^^^ v2124
  let v2126 := s.e.rotateRight 41
  let v2127 := v2125 ^^^ v2126
  let v2128 := s.e &&& s.f
  let v2129 := s.e ^^^ (-1 : Word)
  let v2130 := s.g &&& v2129
  let v2131 := v2128 ||| v2130
  let v2132 := k
  let v2133 := v2122 + v2132
  let v2134 := v2133 + s.h
  let v2135 := v2134 + v2131
  let v2136 := v2135 + v2127
  let v2137 := s.a.rotateRight 28
  let v2138 := s.a.rotateRight 34
  let v2139 := v2137 ^^^ v2138
  let v2140 := s.a.rotateRight 39
  let v2141 := v2139 ^^^ v2140
  let v2142 := s.a &&& s.b
  let v2143 := s.b ^^^ s.c
  let v2144 := s.a &&& v2143
  let v2145 := v2144 ^^^ (s.b &&& s.c)
  let v2146 := v2141 + v2145
  let v2147 := v2136 + s.d
  let v2148 := v2146 + v2136
  ⟨v2148, s.a, s.b, s.c, v2147, s.e, s.f, s.g⟩

theorem fullOut53_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut53 s w k = Spec.round s (w 53) k := by
  have hw53 := hw 53 (by decide) (by decide)
  dsimp only [fullOut53, Spec.round]
  rw [hw53]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv53_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2110 E (fullEnv53 E s w k) := by
  unfold fullEnv53
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv53_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv53 E s w k) := by
  exact (fullEnv53_before E s w k).frame (by decide)

theorem full_body53 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready53 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 424#64) 64)
    (hk : state.mem.readAt (kp.add 424#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1910 |>.take 39) state =
      .value (fullEnv53 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv53, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w37, h.w38, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k53, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready53 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready53 E s w) (hw : ScheduleReady w) :
    Ready54 (fullEnv53 E s w k) (Spec.round s (w 53) k) w := by
  have hb := fullEnv53_before E s w k
  have hout := fullOut53_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv53, fullOut53, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2109 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2070 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2031 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv53, fullOut53, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2108 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2069 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2030 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv53, Spec.round, mlir_env]
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
  · rw [hb.read_val 2083 (by decide) (by rfl)]; exact h.w52
  · have hwr := hw 53 (by decide) (by decide)
    simp [fullEnv53, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step53 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready53 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1910 |>.take 39) state =
      .value (E', state) ∧
      Ready54 E' (Spec.round s (w 53) (constants.toList.getD 53 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 53 0
  have hf := fullEnv53_frame E s w k
  refine ⟨fullEnv53 E s w k,
    full_body53 E state s w kp k h hc (hk 53).1 (hk 53).2,
    full_ready53 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
