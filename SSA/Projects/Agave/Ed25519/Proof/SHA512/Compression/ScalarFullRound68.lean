import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2495..2533: round 68. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv68 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2695 := (w 53).rotateRight 1
  let v2696 := (w 53).rotateRight 8
  let v2697 := v2695 ^^^ v2696
  let v2698 := (w 53) >>> 7
  let v2699 := v2697 ^^^ v2698
  let v2700 := (w 66).rotateRight 19
  let v2701 := (w 66).rotateRight 61
  let v2702 := v2700 ^^^ v2701
  let v2703 := (w 66) >>> 6
  let v2704 := v2702 ^^^ v2703
  let v2705 := v2699 + (w 52)
  let v2706 := v2705 + (w 61)
  let v2707 := v2706 + v2704
  let v2708 := s.e.rotateRight 14
  let v2709 := s.e.rotateRight 18
  let v2710 := v2708 ^^^ v2709
  let v2711 := s.e.rotateRight 41
  let v2712 := v2710 ^^^ v2711
  let v2713 := s.e &&& s.f
  let v2714 := s.e ^^^ (-1 : Word)
  let v2715 := s.g &&& v2714
  let v2716 := v2713 ||| v2715
  let v2717 := k
  let v2718 := v2707 + v2717
  let v2719 := v2718 + s.h
  let v2720 := v2719 + v2716
  let v2721 := v2720 + v2712
  let v2722 := s.a.rotateRight 28
  let v2723 := s.a.rotateRight 34
  let v2724 := v2722 ^^^ v2723
  let v2725 := s.a.rotateRight 39
  let v2726 := v2724 ^^^ v2725
  let v2727 := s.a &&& s.b
  let v2728 := s.b ^^^ s.c
  let v2729 := s.a &&& v2728
  let v2730 := v2729 ^^^ (s.b &&& s.c)
  let v2731 := v2726 + v2730
  let v2732 := v2721 + s.d
  let v2733 := v2731 + v2721
  E[%2695 := .value v2695,
    %2696 := .value v2696,
    %2697 := .value v2697,
    %2698 := .value v2698,
    %2699 := .value v2699,
    %2700 := .value v2700,
    %2701 := .value v2701,
    %2702 := .value v2702,
    %2703 := .value v2703,
    %2704 := .value v2704,
    %2705 := .value v2705,
    %2706 := .value v2706,
    %2707 := .value v2707,
    %2708 := .value v2708,
    %2709 := .value v2709,
    %2710 := .value v2710,
    %2711 := .value v2711,
    %2712 := .value v2712,
    %2713 := .value v2713,
    %2714 := .value v2714,
    %2715 := .value v2715,
    %2716 := .value v2716,
    %2717 := .value v2717,
    %2718 := .value v2718,
    %2719 := .value v2719,
    %2720 := .value v2720,
    %2721 := .value v2721,
    %2722 := .value v2722,
    %2723 := .value v2723,
    %2724 := .value v2724,
    %2725 := .value v2725,
    %2726 := .value v2726,
    %2727 := .value v2727,
    %2728 := .value v2728,
    %2729 := .value v2729,
    %2730 := .value v2730,
    %2731 := .value v2731,
    %2732 := .value v2732,
    %2733 := .value v2733]

def fullOut68 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2695 := (w 53).rotateRight 1
  let v2696 := (w 53).rotateRight 8
  let v2697 := v2695 ^^^ v2696
  let v2698 := (w 53) >>> 7
  let v2699 := v2697 ^^^ v2698
  let v2700 := (w 66).rotateRight 19
  let v2701 := (w 66).rotateRight 61
  let v2702 := v2700 ^^^ v2701
  let v2703 := (w 66) >>> 6
  let v2704 := v2702 ^^^ v2703
  let v2705 := v2699 + (w 52)
  let v2706 := v2705 + (w 61)
  let v2707 := v2706 + v2704
  let v2708 := s.e.rotateRight 14
  let v2709 := s.e.rotateRight 18
  let v2710 := v2708 ^^^ v2709
  let v2711 := s.e.rotateRight 41
  let v2712 := v2710 ^^^ v2711
  let v2713 := s.e &&& s.f
  let v2714 := s.e ^^^ (-1 : Word)
  let v2715 := s.g &&& v2714
  let v2716 := v2713 ||| v2715
  let v2717 := k
  let v2718 := v2707 + v2717
  let v2719 := v2718 + s.h
  let v2720 := v2719 + v2716
  let v2721 := v2720 + v2712
  let v2722 := s.a.rotateRight 28
  let v2723 := s.a.rotateRight 34
  let v2724 := v2722 ^^^ v2723
  let v2725 := s.a.rotateRight 39
  let v2726 := v2724 ^^^ v2725
  let v2727 := s.a &&& s.b
  let v2728 := s.b ^^^ s.c
  let v2729 := s.a &&& v2728
  let v2730 := v2729 ^^^ (s.b &&& s.c)
  let v2731 := v2726 + v2730
  let v2732 := v2721 + s.d
  let v2733 := v2731 + v2721
  ⟨v2733, s.a, s.b, s.c, v2732, s.e, s.f, s.g⟩

theorem fullOut68_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut68 s w k = Spec.round s (w 68) k := by
  have hw68 := hw 68 (by decide) (by decide)
  dsimp only [fullOut68, Spec.round]
  rw [hw68]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv68_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2695 E (fullEnv68 E s w k) := by
  unfold fullEnv68
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv68_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv68 E s w k) := by
  exact (fullEnv68_before E s w k).frame (by decide)

theorem full_body68 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready68 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 544#64) 64)
    (hk : state.mem.readAt (kp.add 544#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2495 |>.take 39) state =
      .value (fullEnv68 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv68, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w52, h.w53, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w65, h.w66, h.w67, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k68, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready68 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready68 E s w) (hw : ScheduleReady w) :
    Ready69 (fullEnv68 E s w k) (Spec.round s (w 68) k) w := by
  have hb := fullEnv68_before E s w k
  have hout := fullOut68_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv68, fullOut68, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2694 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2655 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2616 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv68, fullOut68, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2693 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2654 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2615 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv68, Spec.round, mlir_env]
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
  · rw [hb.read_val 2629 (by decide) (by rfl)]; exact h.w66
  · rw [hb.read_val 2668 (by decide) (by rfl)]; exact h.w67
  · have hwr := hw 68 (by decide) (by decide)
    simp [fullEnv68, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step68 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready68 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2495 |>.take 39) state =
      .value (E', state) ∧
      Ready69 E' (Spec.round s (w 68) (constants.toList.getD 68 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 68 0
  have hf := fullEnv68_frame E s w k
  refine ⟨fullEnv68 E s w k,
    full_body68 E state s w kp k h hc (hk 68).1 (hk 68).2,
    full_ready68 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
