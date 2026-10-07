import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2027..2065: round 56. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv56 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2227 := (w 41).rotateRight 1
  let v2228 := (w 41).rotateRight 8
  let v2229 := v2227 ^^^ v2228
  let v2230 := (w 41) >>> 7
  let v2231 := v2229 ^^^ v2230
  let v2232 := (w 54).rotateRight 19
  let v2233 := (w 54).rotateRight 61
  let v2234 := v2232 ^^^ v2233
  let v2235 := (w 54) >>> 6
  let v2236 := v2234 ^^^ v2235
  let v2237 := v2231 + (w 40)
  let v2238 := v2237 + (w 49)
  let v2239 := v2238 + v2236
  let v2240 := s.e.rotateRight 14
  let v2241 := s.e.rotateRight 18
  let v2242 := v2240 ^^^ v2241
  let v2243 := s.e.rotateRight 41
  let v2244 := v2242 ^^^ v2243
  let v2245 := s.e &&& s.f
  let v2246 := s.e ^^^ (-1 : Word)
  let v2247 := s.g &&& v2246
  let v2248 := v2245 ||| v2247
  let v2249 := k
  let v2250 := v2239 + v2249
  let v2251 := v2250 + s.h
  let v2252 := v2251 + v2248
  let v2253 := v2252 + v2244
  let v2254 := s.a.rotateRight 28
  let v2255 := s.a.rotateRight 34
  let v2256 := v2254 ^^^ v2255
  let v2257 := s.a.rotateRight 39
  let v2258 := v2256 ^^^ v2257
  let v2259 := s.a &&& s.b
  let v2260 := s.b ^^^ s.c
  let v2261 := s.a &&& v2260
  let v2262 := v2261 ^^^ (s.b &&& s.c)
  let v2263 := v2258 + v2262
  let v2264 := v2253 + s.d
  let v2265 := v2263 + v2253
  E[%2227 := .value v2227,
    %2228 := .value v2228,
    %2229 := .value v2229,
    %2230 := .value v2230,
    %2231 := .value v2231,
    %2232 := .value v2232,
    %2233 := .value v2233,
    %2234 := .value v2234,
    %2235 := .value v2235,
    %2236 := .value v2236,
    %2237 := .value v2237,
    %2238 := .value v2238,
    %2239 := .value v2239,
    %2240 := .value v2240,
    %2241 := .value v2241,
    %2242 := .value v2242,
    %2243 := .value v2243,
    %2244 := .value v2244,
    %2245 := .value v2245,
    %2246 := .value v2246,
    %2247 := .value v2247,
    %2248 := .value v2248,
    %2249 := .value v2249,
    %2250 := .value v2250,
    %2251 := .value v2251,
    %2252 := .value v2252,
    %2253 := .value v2253,
    %2254 := .value v2254,
    %2255 := .value v2255,
    %2256 := .value v2256,
    %2257 := .value v2257,
    %2258 := .value v2258,
    %2259 := .value v2259,
    %2260 := .value v2260,
    %2261 := .value v2261,
    %2262 := .value v2262,
    %2263 := .value v2263,
    %2264 := .value v2264,
    %2265 := .value v2265]

def fullOut56 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2227 := (w 41).rotateRight 1
  let v2228 := (w 41).rotateRight 8
  let v2229 := v2227 ^^^ v2228
  let v2230 := (w 41) >>> 7
  let v2231 := v2229 ^^^ v2230
  let v2232 := (w 54).rotateRight 19
  let v2233 := (w 54).rotateRight 61
  let v2234 := v2232 ^^^ v2233
  let v2235 := (w 54) >>> 6
  let v2236 := v2234 ^^^ v2235
  let v2237 := v2231 + (w 40)
  let v2238 := v2237 + (w 49)
  let v2239 := v2238 + v2236
  let v2240 := s.e.rotateRight 14
  let v2241 := s.e.rotateRight 18
  let v2242 := v2240 ^^^ v2241
  let v2243 := s.e.rotateRight 41
  let v2244 := v2242 ^^^ v2243
  let v2245 := s.e &&& s.f
  let v2246 := s.e ^^^ (-1 : Word)
  let v2247 := s.g &&& v2246
  let v2248 := v2245 ||| v2247
  let v2249 := k
  let v2250 := v2239 + v2249
  let v2251 := v2250 + s.h
  let v2252 := v2251 + v2248
  let v2253 := v2252 + v2244
  let v2254 := s.a.rotateRight 28
  let v2255 := s.a.rotateRight 34
  let v2256 := v2254 ^^^ v2255
  let v2257 := s.a.rotateRight 39
  let v2258 := v2256 ^^^ v2257
  let v2259 := s.a &&& s.b
  let v2260 := s.b ^^^ s.c
  let v2261 := s.a &&& v2260
  let v2262 := v2261 ^^^ (s.b &&& s.c)
  let v2263 := v2258 + v2262
  let v2264 := v2253 + s.d
  let v2265 := v2263 + v2253
  ⟨v2265, s.a, s.b, s.c, v2264, s.e, s.f, s.g⟩

theorem fullOut56_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut56 s w k = Spec.round s (w 56) k := by
  have hw56 := hw 56 (by decide) (by decide)
  dsimp only [fullOut56, Spec.round]
  rw [hw56]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv56_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2227 E (fullEnv56 E s w k) := by
  unfold fullEnv56
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv56_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv56 E s w k) := by
  exact (fullEnv56_before E s w k).frame (by decide)

theorem full_body56 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready56 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 448#64) 64)
    (hk : state.mem.readAt (kp.add 448#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2027 |>.take 39) state =
      .value (fullEnv56 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv56, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w40, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k56, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready56 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready56 E s w) (hw : ScheduleReady w) :
    Ready57 (fullEnv56 E s w k) (Spec.round s (w 56) k) w := by
  have hb := fullEnv56_before E s w k
  have hout := fullOut56_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv56, fullOut56, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2226 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2187 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2148 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv56, fullOut56, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2225 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2186 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2147 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv56, Spec.round, mlir_env]
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
  · rw [hb.read_val 2200 (by decide) (by rfl)]; exact h.w55
  · have hwr := hw 56 (by decide) (by decide)
    simp [fullEnv56, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step56 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready56 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2027 |>.take 39) state =
      .value (E', state) ∧
      Ready57 E' (Spec.round s (w 56) (constants.toList.getD 56 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 56 0
  have hf := fullEnv56_frame E s w k
  refine ⟨fullEnv56 E s w k,
    full_body56 E state s w kp k h hc (hk 56).1 (hk 56).2,
    full_ready56 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
