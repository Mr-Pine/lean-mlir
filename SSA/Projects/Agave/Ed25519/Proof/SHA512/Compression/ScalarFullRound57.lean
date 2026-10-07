import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2066..2104: round 57. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv57 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2266 := (w 42).rotateRight 1
  let v2267 := (w 42).rotateRight 8
  let v2268 := v2266 ^^^ v2267
  let v2269 := (w 42) >>> 7
  let v2270 := v2268 ^^^ v2269
  let v2271 := (w 55).rotateRight 19
  let v2272 := (w 55).rotateRight 61
  let v2273 := v2271 ^^^ v2272
  let v2274 := (w 55) >>> 6
  let v2275 := v2273 ^^^ v2274
  let v2276 := v2270 + (w 41)
  let v2277 := v2276 + (w 50)
  let v2278 := v2277 + v2275
  let v2279 := s.e.rotateRight 14
  let v2280 := s.e.rotateRight 18
  let v2281 := v2279 ^^^ v2280
  let v2282 := s.e.rotateRight 41
  let v2283 := v2281 ^^^ v2282
  let v2284 := s.e &&& s.f
  let v2285 := s.e ^^^ (-1 : Word)
  let v2286 := s.g &&& v2285
  let v2287 := v2284 ||| v2286
  let v2288 := k
  let v2289 := v2278 + v2288
  let v2290 := v2289 + s.h
  let v2291 := v2290 + v2287
  let v2292 := v2291 + v2283
  let v2293 := s.a.rotateRight 28
  let v2294 := s.a.rotateRight 34
  let v2295 := v2293 ^^^ v2294
  let v2296 := s.a.rotateRight 39
  let v2297 := v2295 ^^^ v2296
  let v2298 := s.a &&& s.b
  let v2299 := s.b ^^^ s.c
  let v2300 := s.a &&& v2299
  let v2301 := v2300 ^^^ (s.b &&& s.c)
  let v2302 := v2297 + v2301
  let v2303 := v2292 + s.d
  let v2304 := v2302 + v2292
  E[%2266 := .value v2266,
    %2267 := .value v2267,
    %2268 := .value v2268,
    %2269 := .value v2269,
    %2270 := .value v2270,
    %2271 := .value v2271,
    %2272 := .value v2272,
    %2273 := .value v2273,
    %2274 := .value v2274,
    %2275 := .value v2275,
    %2276 := .value v2276,
    %2277 := .value v2277,
    %2278 := .value v2278,
    %2279 := .value v2279,
    %2280 := .value v2280,
    %2281 := .value v2281,
    %2282 := .value v2282,
    %2283 := .value v2283,
    %2284 := .value v2284,
    %2285 := .value v2285,
    %2286 := .value v2286,
    %2287 := .value v2287,
    %2288 := .value v2288,
    %2289 := .value v2289,
    %2290 := .value v2290,
    %2291 := .value v2291,
    %2292 := .value v2292,
    %2293 := .value v2293,
    %2294 := .value v2294,
    %2295 := .value v2295,
    %2296 := .value v2296,
    %2297 := .value v2297,
    %2298 := .value v2298,
    %2299 := .value v2299,
    %2300 := .value v2300,
    %2301 := .value v2301,
    %2302 := .value v2302,
    %2303 := .value v2303,
    %2304 := .value v2304]

def fullOut57 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2266 := (w 42).rotateRight 1
  let v2267 := (w 42).rotateRight 8
  let v2268 := v2266 ^^^ v2267
  let v2269 := (w 42) >>> 7
  let v2270 := v2268 ^^^ v2269
  let v2271 := (w 55).rotateRight 19
  let v2272 := (w 55).rotateRight 61
  let v2273 := v2271 ^^^ v2272
  let v2274 := (w 55) >>> 6
  let v2275 := v2273 ^^^ v2274
  let v2276 := v2270 + (w 41)
  let v2277 := v2276 + (w 50)
  let v2278 := v2277 + v2275
  let v2279 := s.e.rotateRight 14
  let v2280 := s.e.rotateRight 18
  let v2281 := v2279 ^^^ v2280
  let v2282 := s.e.rotateRight 41
  let v2283 := v2281 ^^^ v2282
  let v2284 := s.e &&& s.f
  let v2285 := s.e ^^^ (-1 : Word)
  let v2286 := s.g &&& v2285
  let v2287 := v2284 ||| v2286
  let v2288 := k
  let v2289 := v2278 + v2288
  let v2290 := v2289 + s.h
  let v2291 := v2290 + v2287
  let v2292 := v2291 + v2283
  let v2293 := s.a.rotateRight 28
  let v2294 := s.a.rotateRight 34
  let v2295 := v2293 ^^^ v2294
  let v2296 := s.a.rotateRight 39
  let v2297 := v2295 ^^^ v2296
  let v2298 := s.a &&& s.b
  let v2299 := s.b ^^^ s.c
  let v2300 := s.a &&& v2299
  let v2301 := v2300 ^^^ (s.b &&& s.c)
  let v2302 := v2297 + v2301
  let v2303 := v2292 + s.d
  let v2304 := v2302 + v2292
  ⟨v2304, s.a, s.b, s.c, v2303, s.e, s.f, s.g⟩

theorem fullOut57_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut57 s w k = Spec.round s (w 57) k := by
  have hw57 := hw 57 (by decide) (by decide)
  dsimp only [fullOut57, Spec.round]
  rw [hw57]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv57_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2266 E (fullEnv57 E s w k) := by
  unfold fullEnv57
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv57_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv57 E s w k) := by
  exact (fullEnv57_before E s w k).frame (by decide)

theorem full_body57 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready57 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 456#64) 64)
    (hk : state.mem.readAt (kp.add 456#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2066 |>.take 39) state =
      .value (fullEnv57 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv57, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w41, h.w42, h.w43, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k57, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready57 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready57 E s w) (hw : ScheduleReady w) :
    Ready58 (fullEnv57 E s w k) (Spec.round s (w 57) k) w := by
  have hb := fullEnv57_before E s w k
  have hout := fullOut57_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv57, fullOut57, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2265 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2226 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2187 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv57, fullOut57, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2264 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2225 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2186 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv57, Spec.round, mlir_env]
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
  · rw [hb.read_val 2239 (by decide) (by rfl)]; exact h.w56
  · have hwr := hw 57 (by decide) (by decide)
    simp [fullEnv57, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step57 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready57 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2066 |>.take 39) state =
      .value (E', state) ∧
      Ready58 E' (Spec.round s (w 57) (constants.toList.getD 57 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 57 0
  have hf := fullEnv57_frame E s w k
  refine ⟨fullEnv57 E s w k,
    full_body57 E state s w kp k h hc (hk 57).1 (hk 57).2,
    full_ready57 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
