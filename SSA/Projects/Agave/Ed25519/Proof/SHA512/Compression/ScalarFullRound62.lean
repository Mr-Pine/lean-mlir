import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2261..2299: round 62. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv62 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2461 := (w 47).rotateRight 1
  let v2462 := (w 47).rotateRight 8
  let v2463 := v2461 ^^^ v2462
  let v2464 := (w 47) >>> 7
  let v2465 := v2463 ^^^ v2464
  let v2466 := (w 60).rotateRight 19
  let v2467 := (w 60).rotateRight 61
  let v2468 := v2466 ^^^ v2467
  let v2469 := (w 60) >>> 6
  let v2470 := v2468 ^^^ v2469
  let v2471 := v2465 + (w 46)
  let v2472 := v2471 + (w 55)
  let v2473 := v2472 + v2470
  let v2474 := s.e.rotateRight 14
  let v2475 := s.e.rotateRight 18
  let v2476 := v2474 ^^^ v2475
  let v2477 := s.e.rotateRight 41
  let v2478 := v2476 ^^^ v2477
  let v2479 := s.e &&& s.f
  let v2480 := s.e ^^^ (-1 : Word)
  let v2481 := s.g &&& v2480
  let v2482 := v2479 ||| v2481
  let v2483 := k
  let v2484 := v2473 + v2483
  let v2485 := v2484 + s.h
  let v2486 := v2485 + v2482
  let v2487 := v2486 + v2478
  let v2488 := s.a.rotateRight 28
  let v2489 := s.a.rotateRight 34
  let v2490 := v2488 ^^^ v2489
  let v2491 := s.a.rotateRight 39
  let v2492 := v2490 ^^^ v2491
  let v2493 := s.a &&& s.b
  let v2494 := s.b ^^^ s.c
  let v2495 := s.a &&& v2494
  let v2496 := v2495 ^^^ (s.b &&& s.c)
  let v2497 := v2492 + v2496
  let v2498 := v2487 + s.d
  let v2499 := v2497 + v2487
  E[%2461 := .value v2461,
    %2462 := .value v2462,
    %2463 := .value v2463,
    %2464 := .value v2464,
    %2465 := .value v2465,
    %2466 := .value v2466,
    %2467 := .value v2467,
    %2468 := .value v2468,
    %2469 := .value v2469,
    %2470 := .value v2470,
    %2471 := .value v2471,
    %2472 := .value v2472,
    %2473 := .value v2473,
    %2474 := .value v2474,
    %2475 := .value v2475,
    %2476 := .value v2476,
    %2477 := .value v2477,
    %2478 := .value v2478,
    %2479 := .value v2479,
    %2480 := .value v2480,
    %2481 := .value v2481,
    %2482 := .value v2482,
    %2483 := .value v2483,
    %2484 := .value v2484,
    %2485 := .value v2485,
    %2486 := .value v2486,
    %2487 := .value v2487,
    %2488 := .value v2488,
    %2489 := .value v2489,
    %2490 := .value v2490,
    %2491 := .value v2491,
    %2492 := .value v2492,
    %2493 := .value v2493,
    %2494 := .value v2494,
    %2495 := .value v2495,
    %2496 := .value v2496,
    %2497 := .value v2497,
    %2498 := .value v2498,
    %2499 := .value v2499]

def fullOut62 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2461 := (w 47).rotateRight 1
  let v2462 := (w 47).rotateRight 8
  let v2463 := v2461 ^^^ v2462
  let v2464 := (w 47) >>> 7
  let v2465 := v2463 ^^^ v2464
  let v2466 := (w 60).rotateRight 19
  let v2467 := (w 60).rotateRight 61
  let v2468 := v2466 ^^^ v2467
  let v2469 := (w 60) >>> 6
  let v2470 := v2468 ^^^ v2469
  let v2471 := v2465 + (w 46)
  let v2472 := v2471 + (w 55)
  let v2473 := v2472 + v2470
  let v2474 := s.e.rotateRight 14
  let v2475 := s.e.rotateRight 18
  let v2476 := v2474 ^^^ v2475
  let v2477 := s.e.rotateRight 41
  let v2478 := v2476 ^^^ v2477
  let v2479 := s.e &&& s.f
  let v2480 := s.e ^^^ (-1 : Word)
  let v2481 := s.g &&& v2480
  let v2482 := v2479 ||| v2481
  let v2483 := k
  let v2484 := v2473 + v2483
  let v2485 := v2484 + s.h
  let v2486 := v2485 + v2482
  let v2487 := v2486 + v2478
  let v2488 := s.a.rotateRight 28
  let v2489 := s.a.rotateRight 34
  let v2490 := v2488 ^^^ v2489
  let v2491 := s.a.rotateRight 39
  let v2492 := v2490 ^^^ v2491
  let v2493 := s.a &&& s.b
  let v2494 := s.b ^^^ s.c
  let v2495 := s.a &&& v2494
  let v2496 := v2495 ^^^ (s.b &&& s.c)
  let v2497 := v2492 + v2496
  let v2498 := v2487 + s.d
  let v2499 := v2497 + v2487
  ⟨v2499, s.a, s.b, s.c, v2498, s.e, s.f, s.g⟩

theorem fullOut62_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut62 s w k = Spec.round s (w 62) k := by
  have hw62 := hw 62 (by decide) (by decide)
  dsimp only [fullOut62, Spec.round]
  rw [hw62]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv62_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2461 E (fullEnv62 E s w k) := by
  unfold fullEnv62
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv62_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv62 E s w k) := by
  exact (fullEnv62_before E s w k).frame (by decide)

theorem full_body62 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready62 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 496#64) 64)
    (hk : state.mem.readAt (kp.add 496#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2261 |>.take 39) state =
      .value (fullEnv62 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv62, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w46, h.w47, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k62, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready62 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready62 E s w) (hw : ScheduleReady w) :
    Ready63 (fullEnv62 E s w k) (Spec.round s (w 62) k) w := by
  have hb := fullEnv62_before E s w k
  have hout := fullOut62_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv62, fullOut62, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2460 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2421 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2382 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv62, fullOut62, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2459 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2420 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2381 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv62, Spec.round, mlir_env]
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
  · rw [hb.read_val 2434 (by decide) (by rfl)]; exact h.w61
  · have hwr := hw 62 (by decide) (by decide)
    simp [fullEnv62, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step62 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready62 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2261 |>.take 39) state =
      .value (E', state) ∧
      Ready63 E' (Spec.round s (w 62) (constants.toList.getD 62 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 62 0
  have hf := fullEnv62_frame E s w k
  refine ⟨fullEnv62 E s w k,
    full_body62 E state s w kp k h hc (hk 62).1 (hk 62).2,
    full_ready62 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
