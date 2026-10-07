import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1988..2026: round 55. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv55 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2188 := (w 40).rotateRight 1
  let v2189 := (w 40).rotateRight 8
  let v2190 := v2188 ^^^ v2189
  let v2191 := (w 40) >>> 7
  let v2192 := v2190 ^^^ v2191
  let v2193 := (w 53).rotateRight 19
  let v2194 := (w 53).rotateRight 61
  let v2195 := v2193 ^^^ v2194
  let v2196 := (w 53) >>> 6
  let v2197 := v2195 ^^^ v2196
  let v2198 := v2192 + (w 39)
  let v2199 := v2198 + (w 48)
  let v2200 := v2199 + v2197
  let v2201 := s.e.rotateRight 14
  let v2202 := s.e.rotateRight 18
  let v2203 := v2201 ^^^ v2202
  let v2204 := s.e.rotateRight 41
  let v2205 := v2203 ^^^ v2204
  let v2206 := s.e &&& s.f
  let v2207 := s.e ^^^ (-1 : Word)
  let v2208 := s.g &&& v2207
  let v2209 := v2206 ||| v2208
  let v2210 := k
  let v2211 := v2200 + v2210
  let v2212 := v2211 + s.h
  let v2213 := v2212 + v2209
  let v2214 := v2213 + v2205
  let v2215 := s.a.rotateRight 28
  let v2216 := s.a.rotateRight 34
  let v2217 := v2215 ^^^ v2216
  let v2218 := s.a.rotateRight 39
  let v2219 := v2217 ^^^ v2218
  let v2220 := s.a &&& s.b
  let v2221 := s.b ^^^ s.c
  let v2222 := s.a &&& v2221
  let v2223 := v2222 ^^^ (s.b &&& s.c)
  let v2224 := v2219 + v2223
  let v2225 := v2214 + s.d
  let v2226 := v2224 + v2214
  E[%2188 := .value v2188,
    %2189 := .value v2189,
    %2190 := .value v2190,
    %2191 := .value v2191,
    %2192 := .value v2192,
    %2193 := .value v2193,
    %2194 := .value v2194,
    %2195 := .value v2195,
    %2196 := .value v2196,
    %2197 := .value v2197,
    %2198 := .value v2198,
    %2199 := .value v2199,
    %2200 := .value v2200,
    %2201 := .value v2201,
    %2202 := .value v2202,
    %2203 := .value v2203,
    %2204 := .value v2204,
    %2205 := .value v2205,
    %2206 := .value v2206,
    %2207 := .value v2207,
    %2208 := .value v2208,
    %2209 := .value v2209,
    %2210 := .value v2210,
    %2211 := .value v2211,
    %2212 := .value v2212,
    %2213 := .value v2213,
    %2214 := .value v2214,
    %2215 := .value v2215,
    %2216 := .value v2216,
    %2217 := .value v2217,
    %2218 := .value v2218,
    %2219 := .value v2219,
    %2220 := .value v2220,
    %2221 := .value v2221,
    %2222 := .value v2222,
    %2223 := .value v2223,
    %2224 := .value v2224,
    %2225 := .value v2225,
    %2226 := .value v2226]

def fullOut55 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2188 := (w 40).rotateRight 1
  let v2189 := (w 40).rotateRight 8
  let v2190 := v2188 ^^^ v2189
  let v2191 := (w 40) >>> 7
  let v2192 := v2190 ^^^ v2191
  let v2193 := (w 53).rotateRight 19
  let v2194 := (w 53).rotateRight 61
  let v2195 := v2193 ^^^ v2194
  let v2196 := (w 53) >>> 6
  let v2197 := v2195 ^^^ v2196
  let v2198 := v2192 + (w 39)
  let v2199 := v2198 + (w 48)
  let v2200 := v2199 + v2197
  let v2201 := s.e.rotateRight 14
  let v2202 := s.e.rotateRight 18
  let v2203 := v2201 ^^^ v2202
  let v2204 := s.e.rotateRight 41
  let v2205 := v2203 ^^^ v2204
  let v2206 := s.e &&& s.f
  let v2207 := s.e ^^^ (-1 : Word)
  let v2208 := s.g &&& v2207
  let v2209 := v2206 ||| v2208
  let v2210 := k
  let v2211 := v2200 + v2210
  let v2212 := v2211 + s.h
  let v2213 := v2212 + v2209
  let v2214 := v2213 + v2205
  let v2215 := s.a.rotateRight 28
  let v2216 := s.a.rotateRight 34
  let v2217 := v2215 ^^^ v2216
  let v2218 := s.a.rotateRight 39
  let v2219 := v2217 ^^^ v2218
  let v2220 := s.a &&& s.b
  let v2221 := s.b ^^^ s.c
  let v2222 := s.a &&& v2221
  let v2223 := v2222 ^^^ (s.b &&& s.c)
  let v2224 := v2219 + v2223
  let v2225 := v2214 + s.d
  let v2226 := v2224 + v2214
  ⟨v2226, s.a, s.b, s.c, v2225, s.e, s.f, s.g⟩

theorem fullOut55_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut55 s w k = Spec.round s (w 55) k := by
  have hw55 := hw 55 (by decide) (by decide)
  dsimp only [fullOut55, Spec.round]
  rw [hw55]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv55_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2188 E (fullEnv55 E s w k) := by
  unfold fullEnv55
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv55_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv55 E s w k) := by
  exact (fullEnv55_before E s w k).frame (by decide)

theorem full_body55 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready55 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 440#64) 64)
    (hk : state.mem.readAt (kp.add 440#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1988 |>.take 39) state =
      .value (fullEnv55 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv55, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w39, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k55, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready55 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready55 E s w) (hw : ScheduleReady w) :
    Ready56 (fullEnv55 E s w k) (Spec.round s (w 55) k) w := by
  have hb := fullEnv55_before E s w k
  have hout := fullOut55_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv55, fullOut55, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2187 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2148 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2109 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv55, fullOut55, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2186 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2147 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2108 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv55, Spec.round, mlir_env]
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
  · rw [hb.read_val 2122 (by decide) (by rfl)]; exact h.w53
  · rw [hb.read_val 2161 (by decide) (by rfl)]; exact h.w54
  · have hwr := hw 55 (by decide) (by decide)
    simp [fullEnv55, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step55 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready55 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1988 |>.take 39) state =
      .value (E', state) ∧
      Ready56 E' (Spec.round s (w 55) (constants.toList.getD 55 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 55 0
  have hf := fullEnv55_frame E s w k
  refine ⟨fullEnv55 E s w k,
    full_body55 E state s w kp k h hc (hk 55).1 (hk 55).2,
    full_ready55 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
