import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2417..2455: round 66. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv66 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2617 := (w 51).rotateRight 1
  let v2618 := (w 51).rotateRight 8
  let v2619 := v2617 ^^^ v2618
  let v2620 := (w 51) >>> 7
  let v2621 := v2619 ^^^ v2620
  let v2622 := (w 64).rotateRight 19
  let v2623 := (w 64).rotateRight 61
  let v2624 := v2622 ^^^ v2623
  let v2625 := (w 64) >>> 6
  let v2626 := v2624 ^^^ v2625
  let v2627 := v2621 + (w 50)
  let v2628 := v2627 + (w 59)
  let v2629 := v2628 + v2626
  let v2630 := s.e.rotateRight 14
  let v2631 := s.e.rotateRight 18
  let v2632 := v2630 ^^^ v2631
  let v2633 := s.e.rotateRight 41
  let v2634 := v2632 ^^^ v2633
  let v2635 := s.e &&& s.f
  let v2636 := s.e ^^^ (-1 : Word)
  let v2637 := s.g &&& v2636
  let v2638 := v2635 ||| v2637
  let v2639 := k
  let v2640 := v2629 + v2639
  let v2641 := v2640 + s.h
  let v2642 := v2641 + v2638
  let v2643 := v2642 + v2634
  let v2644 := s.a.rotateRight 28
  let v2645 := s.a.rotateRight 34
  let v2646 := v2644 ^^^ v2645
  let v2647 := s.a.rotateRight 39
  let v2648 := v2646 ^^^ v2647
  let v2649 := s.a &&& s.b
  let v2650 := s.b ^^^ s.c
  let v2651 := s.a &&& v2650
  let v2652 := v2651 ^^^ (s.b &&& s.c)
  let v2653 := v2648 + v2652
  let v2654 := v2643 + s.d
  let v2655 := v2653 + v2643
  E[%2617 := .value v2617,
    %2618 := .value v2618,
    %2619 := .value v2619,
    %2620 := .value v2620,
    %2621 := .value v2621,
    %2622 := .value v2622,
    %2623 := .value v2623,
    %2624 := .value v2624,
    %2625 := .value v2625,
    %2626 := .value v2626,
    %2627 := .value v2627,
    %2628 := .value v2628,
    %2629 := .value v2629,
    %2630 := .value v2630,
    %2631 := .value v2631,
    %2632 := .value v2632,
    %2633 := .value v2633,
    %2634 := .value v2634,
    %2635 := .value v2635,
    %2636 := .value v2636,
    %2637 := .value v2637,
    %2638 := .value v2638,
    %2639 := .value v2639,
    %2640 := .value v2640,
    %2641 := .value v2641,
    %2642 := .value v2642,
    %2643 := .value v2643,
    %2644 := .value v2644,
    %2645 := .value v2645,
    %2646 := .value v2646,
    %2647 := .value v2647,
    %2648 := .value v2648,
    %2649 := .value v2649,
    %2650 := .value v2650,
    %2651 := .value v2651,
    %2652 := .value v2652,
    %2653 := .value v2653,
    %2654 := .value v2654,
    %2655 := .value v2655]

def fullOut66 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2617 := (w 51).rotateRight 1
  let v2618 := (w 51).rotateRight 8
  let v2619 := v2617 ^^^ v2618
  let v2620 := (w 51) >>> 7
  let v2621 := v2619 ^^^ v2620
  let v2622 := (w 64).rotateRight 19
  let v2623 := (w 64).rotateRight 61
  let v2624 := v2622 ^^^ v2623
  let v2625 := (w 64) >>> 6
  let v2626 := v2624 ^^^ v2625
  let v2627 := v2621 + (w 50)
  let v2628 := v2627 + (w 59)
  let v2629 := v2628 + v2626
  let v2630 := s.e.rotateRight 14
  let v2631 := s.e.rotateRight 18
  let v2632 := v2630 ^^^ v2631
  let v2633 := s.e.rotateRight 41
  let v2634 := v2632 ^^^ v2633
  let v2635 := s.e &&& s.f
  let v2636 := s.e ^^^ (-1 : Word)
  let v2637 := s.g &&& v2636
  let v2638 := v2635 ||| v2637
  let v2639 := k
  let v2640 := v2629 + v2639
  let v2641 := v2640 + s.h
  let v2642 := v2641 + v2638
  let v2643 := v2642 + v2634
  let v2644 := s.a.rotateRight 28
  let v2645 := s.a.rotateRight 34
  let v2646 := v2644 ^^^ v2645
  let v2647 := s.a.rotateRight 39
  let v2648 := v2646 ^^^ v2647
  let v2649 := s.a &&& s.b
  let v2650 := s.b ^^^ s.c
  let v2651 := s.a &&& v2650
  let v2652 := v2651 ^^^ (s.b &&& s.c)
  let v2653 := v2648 + v2652
  let v2654 := v2643 + s.d
  let v2655 := v2653 + v2643
  ⟨v2655, s.a, s.b, s.c, v2654, s.e, s.f, s.g⟩

theorem fullOut66_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut66 s w k = Spec.round s (w 66) k := by
  have hw66 := hw 66 (by decide) (by decide)
  dsimp only [fullOut66, Spec.round]
  rw [hw66]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv66_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2617 E (fullEnv66 E s w k) := by
  unfold fullEnv66
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv66_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv66 E s w k) := by
  exact (fullEnv66_before E s w k).frame (by decide)

theorem full_body66 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready66 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 528#64) 64)
    (hk : state.mem.readAt (kp.add 528#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2417 |>.take 39) state =
      .value (fullEnv66 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv66, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w50, h.w51, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w65, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k66, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready66 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready66 E s w) (hw : ScheduleReady w) :
    Ready67 (fullEnv66 E s w k) (Spec.round s (w 66) k) w := by
  have hb := fullEnv66_before E s w k
  have hout := fullOut66_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv66, fullOut66, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2616 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2577 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2538 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv66, fullOut66, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2615 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2576 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2537 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv66, Spec.round, mlir_env]
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
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · rw [hb.read_val 2590 (by decide) (by rfl)]; exact h.w65
  · have hwr := hw 66 (by decide) (by decide)
    simp [fullEnv66, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step66 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready66 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2417 |>.take 39) state =
      .value (E', state) ∧
      Ready67 E' (Spec.round s (w 66) (constants.toList.getD 66 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 66 0
  have hf := fullEnv66_frame E s w k
  refine ⟨fullEnv66 E s w k,
    full_body66 E state s w kp k h hc (hk 66).1 (hk 66).2,
    full_ready66 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
