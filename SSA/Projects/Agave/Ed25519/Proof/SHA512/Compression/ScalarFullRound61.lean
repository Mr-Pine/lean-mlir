import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2222..2260: round 61. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv61 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2422 := (w 46).rotateRight 1
  let v2423 := (w 46).rotateRight 8
  let v2424 := v2422 ^^^ v2423
  let v2425 := (w 46) >>> 7
  let v2426 := v2424 ^^^ v2425
  let v2427 := (w 59).rotateRight 19
  let v2428 := (w 59).rotateRight 61
  let v2429 := v2427 ^^^ v2428
  let v2430 := (w 59) >>> 6
  let v2431 := v2429 ^^^ v2430
  let v2432 := v2426 + (w 45)
  let v2433 := v2432 + (w 54)
  let v2434 := v2433 + v2431
  let v2435 := s.e.rotateRight 14
  let v2436 := s.e.rotateRight 18
  let v2437 := v2435 ^^^ v2436
  let v2438 := s.e.rotateRight 41
  let v2439 := v2437 ^^^ v2438
  let v2440 := s.e &&& s.f
  let v2441 := s.e ^^^ (-1 : Word)
  let v2442 := s.g &&& v2441
  let v2443 := v2440 ||| v2442
  let v2444 := k
  let v2445 := v2434 + v2444
  let v2446 := v2445 + s.h
  let v2447 := v2446 + v2443
  let v2448 := v2447 + v2439
  let v2449 := s.a.rotateRight 28
  let v2450 := s.a.rotateRight 34
  let v2451 := v2449 ^^^ v2450
  let v2452 := s.a.rotateRight 39
  let v2453 := v2451 ^^^ v2452
  let v2454 := s.a &&& s.b
  let v2455 := s.b ^^^ s.c
  let v2456 := s.a &&& v2455
  let v2457 := v2456 ^^^ (s.b &&& s.c)
  let v2458 := v2453 + v2457
  let v2459 := v2448 + s.d
  let v2460 := v2458 + v2448
  E[%2422 := .value v2422,
    %2423 := .value v2423,
    %2424 := .value v2424,
    %2425 := .value v2425,
    %2426 := .value v2426,
    %2427 := .value v2427,
    %2428 := .value v2428,
    %2429 := .value v2429,
    %2430 := .value v2430,
    %2431 := .value v2431,
    %2432 := .value v2432,
    %2433 := .value v2433,
    %2434 := .value v2434,
    %2435 := .value v2435,
    %2436 := .value v2436,
    %2437 := .value v2437,
    %2438 := .value v2438,
    %2439 := .value v2439,
    %2440 := .value v2440,
    %2441 := .value v2441,
    %2442 := .value v2442,
    %2443 := .value v2443,
    %2444 := .value v2444,
    %2445 := .value v2445,
    %2446 := .value v2446,
    %2447 := .value v2447,
    %2448 := .value v2448,
    %2449 := .value v2449,
    %2450 := .value v2450,
    %2451 := .value v2451,
    %2452 := .value v2452,
    %2453 := .value v2453,
    %2454 := .value v2454,
    %2455 := .value v2455,
    %2456 := .value v2456,
    %2457 := .value v2457,
    %2458 := .value v2458,
    %2459 := .value v2459,
    %2460 := .value v2460]

def fullOut61 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2422 := (w 46).rotateRight 1
  let v2423 := (w 46).rotateRight 8
  let v2424 := v2422 ^^^ v2423
  let v2425 := (w 46) >>> 7
  let v2426 := v2424 ^^^ v2425
  let v2427 := (w 59).rotateRight 19
  let v2428 := (w 59).rotateRight 61
  let v2429 := v2427 ^^^ v2428
  let v2430 := (w 59) >>> 6
  let v2431 := v2429 ^^^ v2430
  let v2432 := v2426 + (w 45)
  let v2433 := v2432 + (w 54)
  let v2434 := v2433 + v2431
  let v2435 := s.e.rotateRight 14
  let v2436 := s.e.rotateRight 18
  let v2437 := v2435 ^^^ v2436
  let v2438 := s.e.rotateRight 41
  let v2439 := v2437 ^^^ v2438
  let v2440 := s.e &&& s.f
  let v2441 := s.e ^^^ (-1 : Word)
  let v2442 := s.g &&& v2441
  let v2443 := v2440 ||| v2442
  let v2444 := k
  let v2445 := v2434 + v2444
  let v2446 := v2445 + s.h
  let v2447 := v2446 + v2443
  let v2448 := v2447 + v2439
  let v2449 := s.a.rotateRight 28
  let v2450 := s.a.rotateRight 34
  let v2451 := v2449 ^^^ v2450
  let v2452 := s.a.rotateRight 39
  let v2453 := v2451 ^^^ v2452
  let v2454 := s.a &&& s.b
  let v2455 := s.b ^^^ s.c
  let v2456 := s.a &&& v2455
  let v2457 := v2456 ^^^ (s.b &&& s.c)
  let v2458 := v2453 + v2457
  let v2459 := v2448 + s.d
  let v2460 := v2458 + v2448
  ⟨v2460, s.a, s.b, s.c, v2459, s.e, s.f, s.g⟩

theorem fullOut61_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut61 s w k = Spec.round s (w 61) k := by
  have hw61 := hw 61 (by decide) (by decide)
  dsimp only [fullOut61, Spec.round]
  rw [hw61]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv61_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2422 E (fullEnv61 E s w k) := by
  unfold fullEnv61
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv61_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv61 E s w k) := by
  exact (fullEnv61_before E s w k).frame (by decide)

theorem full_body61 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready61 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 488#64) 64)
    (hk : state.mem.readAt (kp.add 488#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2222 |>.take 39) state =
      .value (fullEnv61 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv61, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w45, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k61, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready61 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready61 E s w) (hw : ScheduleReady w) :
    Ready62 (fullEnv61 E s w k) (Spec.round s (w 61) k) w := by
  have hb := fullEnv61_before E s w k
  have hout := fullOut61_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv61, fullOut61, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2421 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2382 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2343 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv61, fullOut61, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2420 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2381 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2342 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv61, Spec.round, mlir_env]
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
  · rw [hb.read_val 2395 (by decide) (by rfl)]; exact h.w60
  · have hwr := hw 61 (by decide) (by decide)
    simp [fullEnv61, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step61 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready61 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2222 |>.take 39) state =
      .value (E', state) ∧
      Ready62 E' (Spec.round s (w 61) (constants.toList.getD 61 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 61 0
  have hf := fullEnv61_frame E s w k
  refine ⟨fullEnv61 E s w k,
    full_body61 E state s w kp k h hc (hk 61).1 (hk 61).2,
    full_ready61 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
