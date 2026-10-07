import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2339..2377: round 64. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv64 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2539 := (w 49).rotateRight 1
  let v2540 := (w 49).rotateRight 8
  let v2541 := v2539 ^^^ v2540
  let v2542 := (w 49) >>> 7
  let v2543 := v2541 ^^^ v2542
  let v2544 := (w 62).rotateRight 19
  let v2545 := (w 62).rotateRight 61
  let v2546 := v2544 ^^^ v2545
  let v2547 := (w 62) >>> 6
  let v2548 := v2546 ^^^ v2547
  let v2549 := v2543 + (w 48)
  let v2550 := v2549 + (w 57)
  let v2551 := v2550 + v2548
  let v2552 := s.e.rotateRight 14
  let v2553 := s.e.rotateRight 18
  let v2554 := v2552 ^^^ v2553
  let v2555 := s.e.rotateRight 41
  let v2556 := v2554 ^^^ v2555
  let v2557 := s.e &&& s.f
  let v2558 := s.e ^^^ (-1 : Word)
  let v2559 := s.g &&& v2558
  let v2560 := v2557 ||| v2559
  let v2561 := k
  let v2562 := v2551 + v2561
  let v2563 := v2562 + s.h
  let v2564 := v2563 + v2560
  let v2565 := v2564 + v2556
  let v2566 := s.a.rotateRight 28
  let v2567 := s.a.rotateRight 34
  let v2568 := v2566 ^^^ v2567
  let v2569 := s.a.rotateRight 39
  let v2570 := v2568 ^^^ v2569
  let v2571 := s.a &&& s.b
  let v2572 := s.b ^^^ s.c
  let v2573 := s.a &&& v2572
  let v2574 := v2573 ^^^ (s.b &&& s.c)
  let v2575 := v2570 + v2574
  let v2576 := v2565 + s.d
  let v2577 := v2575 + v2565
  E[%2539 := .value v2539,
    %2540 := .value v2540,
    %2541 := .value v2541,
    %2542 := .value v2542,
    %2543 := .value v2543,
    %2544 := .value v2544,
    %2545 := .value v2545,
    %2546 := .value v2546,
    %2547 := .value v2547,
    %2548 := .value v2548,
    %2549 := .value v2549,
    %2550 := .value v2550,
    %2551 := .value v2551,
    %2552 := .value v2552,
    %2553 := .value v2553,
    %2554 := .value v2554,
    %2555 := .value v2555,
    %2556 := .value v2556,
    %2557 := .value v2557,
    %2558 := .value v2558,
    %2559 := .value v2559,
    %2560 := .value v2560,
    %2561 := .value v2561,
    %2562 := .value v2562,
    %2563 := .value v2563,
    %2564 := .value v2564,
    %2565 := .value v2565,
    %2566 := .value v2566,
    %2567 := .value v2567,
    %2568 := .value v2568,
    %2569 := .value v2569,
    %2570 := .value v2570,
    %2571 := .value v2571,
    %2572 := .value v2572,
    %2573 := .value v2573,
    %2574 := .value v2574,
    %2575 := .value v2575,
    %2576 := .value v2576,
    %2577 := .value v2577]

def fullOut64 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2539 := (w 49).rotateRight 1
  let v2540 := (w 49).rotateRight 8
  let v2541 := v2539 ^^^ v2540
  let v2542 := (w 49) >>> 7
  let v2543 := v2541 ^^^ v2542
  let v2544 := (w 62).rotateRight 19
  let v2545 := (w 62).rotateRight 61
  let v2546 := v2544 ^^^ v2545
  let v2547 := (w 62) >>> 6
  let v2548 := v2546 ^^^ v2547
  let v2549 := v2543 + (w 48)
  let v2550 := v2549 + (w 57)
  let v2551 := v2550 + v2548
  let v2552 := s.e.rotateRight 14
  let v2553 := s.e.rotateRight 18
  let v2554 := v2552 ^^^ v2553
  let v2555 := s.e.rotateRight 41
  let v2556 := v2554 ^^^ v2555
  let v2557 := s.e &&& s.f
  let v2558 := s.e ^^^ (-1 : Word)
  let v2559 := s.g &&& v2558
  let v2560 := v2557 ||| v2559
  let v2561 := k
  let v2562 := v2551 + v2561
  let v2563 := v2562 + s.h
  let v2564 := v2563 + v2560
  let v2565 := v2564 + v2556
  let v2566 := s.a.rotateRight 28
  let v2567 := s.a.rotateRight 34
  let v2568 := v2566 ^^^ v2567
  let v2569 := s.a.rotateRight 39
  let v2570 := v2568 ^^^ v2569
  let v2571 := s.a &&& s.b
  let v2572 := s.b ^^^ s.c
  let v2573 := s.a &&& v2572
  let v2574 := v2573 ^^^ (s.b &&& s.c)
  let v2575 := v2570 + v2574
  let v2576 := v2565 + s.d
  let v2577 := v2575 + v2565
  ⟨v2577, s.a, s.b, s.c, v2576, s.e, s.f, s.g⟩

theorem fullOut64_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut64 s w k = Spec.round s (w 64) k := by
  have hw64 := hw 64 (by decide) (by decide)
  dsimp only [fullOut64, Spec.round]
  rw [hw64]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv64_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2539 E (fullEnv64 E s w k) := by
  unfold fullEnv64
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv64_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv64 E s w k) := by
  exact (fullEnv64_before E s w k).frame (by decide)

theorem full_body64 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready64 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 512#64) 64)
    (hk : state.mem.readAt (kp.add 512#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2339 |>.take 39) state =
      .value (fullEnv64 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv64, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w48, h.w49, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k64, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready64 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready64 E s w) (hw : ScheduleReady w) :
    Ready65 (fullEnv64 E s w k) (Spec.round s (w 64) k) w := by
  have hb := fullEnv64_before E s w k
  have hout := fullOut64_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv64, fullOut64, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2538 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2499 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2460 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv64, fullOut64, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2537 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2498 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2459 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv64, Spec.round, mlir_env]
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
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · have hwr := hw 64 (by decide) (by decide)
    simp [fullEnv64, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step64 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready64 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2339 |>.take 39) state =
      .value (E', state) ∧
      Ready65 E' (Spec.round s (w 64) (constants.toList.getD 64 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 64 0
  have hf := fullEnv64_frame E s w k
  refine ⟨fullEnv64 E s w k,
    full_body64 E state s w kp k h hc (hk 64).1 (hk 64).2,
    full_ready64 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
