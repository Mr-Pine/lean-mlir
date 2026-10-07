import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2183..2221: round 60. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv60 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2383 := (w 45).rotateRight 1
  let v2384 := (w 45).rotateRight 8
  let v2385 := v2383 ^^^ v2384
  let v2386 := (w 45) >>> 7
  let v2387 := v2385 ^^^ v2386
  let v2388 := (w 58).rotateRight 19
  let v2389 := (w 58).rotateRight 61
  let v2390 := v2388 ^^^ v2389
  let v2391 := (w 58) >>> 6
  let v2392 := v2390 ^^^ v2391
  let v2393 := v2387 + (w 44)
  let v2394 := v2393 + (w 53)
  let v2395 := v2394 + v2392
  let v2396 := s.e.rotateRight 14
  let v2397 := s.e.rotateRight 18
  let v2398 := v2396 ^^^ v2397
  let v2399 := s.e.rotateRight 41
  let v2400 := v2398 ^^^ v2399
  let v2401 := s.e &&& s.f
  let v2402 := s.e ^^^ (-1 : Word)
  let v2403 := s.g &&& v2402
  let v2404 := v2401 ||| v2403
  let v2405 := k
  let v2406 := v2395 + v2405
  let v2407 := v2406 + s.h
  let v2408 := v2407 + v2404
  let v2409 := v2408 + v2400
  let v2410 := s.a.rotateRight 28
  let v2411 := s.a.rotateRight 34
  let v2412 := v2410 ^^^ v2411
  let v2413 := s.a.rotateRight 39
  let v2414 := v2412 ^^^ v2413
  let v2415 := s.a &&& s.b
  let v2416 := s.b ^^^ s.c
  let v2417 := s.a &&& v2416
  let v2418 := v2417 ^^^ (s.b &&& s.c)
  let v2419 := v2414 + v2418
  let v2420 := v2409 + s.d
  let v2421 := v2419 + v2409
  E[%2383 := .value v2383,
    %2384 := .value v2384,
    %2385 := .value v2385,
    %2386 := .value v2386,
    %2387 := .value v2387,
    %2388 := .value v2388,
    %2389 := .value v2389,
    %2390 := .value v2390,
    %2391 := .value v2391,
    %2392 := .value v2392,
    %2393 := .value v2393,
    %2394 := .value v2394,
    %2395 := .value v2395,
    %2396 := .value v2396,
    %2397 := .value v2397,
    %2398 := .value v2398,
    %2399 := .value v2399,
    %2400 := .value v2400,
    %2401 := .value v2401,
    %2402 := .value v2402,
    %2403 := .value v2403,
    %2404 := .value v2404,
    %2405 := .value v2405,
    %2406 := .value v2406,
    %2407 := .value v2407,
    %2408 := .value v2408,
    %2409 := .value v2409,
    %2410 := .value v2410,
    %2411 := .value v2411,
    %2412 := .value v2412,
    %2413 := .value v2413,
    %2414 := .value v2414,
    %2415 := .value v2415,
    %2416 := .value v2416,
    %2417 := .value v2417,
    %2418 := .value v2418,
    %2419 := .value v2419,
    %2420 := .value v2420,
    %2421 := .value v2421]

def fullOut60 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2383 := (w 45).rotateRight 1
  let v2384 := (w 45).rotateRight 8
  let v2385 := v2383 ^^^ v2384
  let v2386 := (w 45) >>> 7
  let v2387 := v2385 ^^^ v2386
  let v2388 := (w 58).rotateRight 19
  let v2389 := (w 58).rotateRight 61
  let v2390 := v2388 ^^^ v2389
  let v2391 := (w 58) >>> 6
  let v2392 := v2390 ^^^ v2391
  let v2393 := v2387 + (w 44)
  let v2394 := v2393 + (w 53)
  let v2395 := v2394 + v2392
  let v2396 := s.e.rotateRight 14
  let v2397 := s.e.rotateRight 18
  let v2398 := v2396 ^^^ v2397
  let v2399 := s.e.rotateRight 41
  let v2400 := v2398 ^^^ v2399
  let v2401 := s.e &&& s.f
  let v2402 := s.e ^^^ (-1 : Word)
  let v2403 := s.g &&& v2402
  let v2404 := v2401 ||| v2403
  let v2405 := k
  let v2406 := v2395 + v2405
  let v2407 := v2406 + s.h
  let v2408 := v2407 + v2404
  let v2409 := v2408 + v2400
  let v2410 := s.a.rotateRight 28
  let v2411 := s.a.rotateRight 34
  let v2412 := v2410 ^^^ v2411
  let v2413 := s.a.rotateRight 39
  let v2414 := v2412 ^^^ v2413
  let v2415 := s.a &&& s.b
  let v2416 := s.b ^^^ s.c
  let v2417 := s.a &&& v2416
  let v2418 := v2417 ^^^ (s.b &&& s.c)
  let v2419 := v2414 + v2418
  let v2420 := v2409 + s.d
  let v2421 := v2419 + v2409
  ⟨v2421, s.a, s.b, s.c, v2420, s.e, s.f, s.g⟩

theorem fullOut60_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut60 s w k = Spec.round s (w 60) k := by
  have hw60 := hw 60 (by decide) (by decide)
  dsimp only [fullOut60, Spec.round]
  rw [hw60]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv60_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2383 E (fullEnv60 E s w k) := by
  unfold fullEnv60
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv60_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv60 E s w k) := by
  exact (fullEnv60_before E s w k).frame (by decide)

theorem full_body60 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready60 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 480#64) 64)
    (hk : state.mem.readAt (kp.add 480#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2183 |>.take 39) state =
      .value (fullEnv60 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv60, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w44, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k60, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready60 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready60 E s w) (hw : ScheduleReady w) :
    Ready61 (fullEnv60 E s w k) (Spec.round s (w 60) k) w := by
  have hb := fullEnv60_before E s w k
  have hout := fullOut60_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv60, fullOut60, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2382 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2343 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2304 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv60, fullOut60, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2381 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2342 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2303 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv60, Spec.round, mlir_env]
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
  · rw [hb.read_val 2278 (by decide) (by rfl)]; exact h.w57
  · rw [hb.read_val 2317 (by decide) (by rfl)]; exact h.w58
  · rw [hb.read_val 2356 (by decide) (by rfl)]; exact h.w59
  · have hwr := hw 60 (by decide) (by decide)
    simp [fullEnv60, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step60 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready60 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2183 |>.take 39) state =
      .value (E', state) ∧
      Ready61 E' (Spec.round s (w 60) (constants.toList.getD 60 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 60 0
  have hf := fullEnv60_frame E s w k
  refine ⟨fullEnv60 E s w k,
    full_body60 E state s w kp k h hc (hk 60).1 (hk 60).2,
    full_ready60 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
