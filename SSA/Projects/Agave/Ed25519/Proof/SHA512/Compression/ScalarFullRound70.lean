import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2573..2611: round 70. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv70 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2773 := (w 55).rotateRight 1
  let v2774 := (w 55).rotateRight 8
  let v2775 := v2773 ^^^ v2774
  let v2776 := (w 55) >>> 7
  let v2777 := v2775 ^^^ v2776
  let v2778 := (w 68).rotateRight 19
  let v2779 := (w 68).rotateRight 61
  let v2780 := v2778 ^^^ v2779
  let v2781 := (w 68) >>> 6
  let v2782 := v2780 ^^^ v2781
  let v2783 := v2777 + (w 54)
  let v2784 := v2783 + (w 63)
  let v2785 := v2784 + v2782
  let v2786 := s.e.rotateRight 14
  let v2787 := s.e.rotateRight 18
  let v2788 := v2786 ^^^ v2787
  let v2789 := s.e.rotateRight 41
  let v2790 := v2788 ^^^ v2789
  let v2791 := s.e &&& s.f
  let v2792 := s.e ^^^ (-1 : Word)
  let v2793 := s.g &&& v2792
  let v2794 := v2791 ||| v2793
  let v2795 := k
  let v2796 := v2785 + v2795
  let v2797 := v2796 + s.h
  let v2798 := v2797 + v2794
  let v2799 := v2798 + v2790
  let v2800 := s.a.rotateRight 28
  let v2801 := s.a.rotateRight 34
  let v2802 := v2800 ^^^ v2801
  let v2803 := s.a.rotateRight 39
  let v2804 := v2802 ^^^ v2803
  let v2805 := s.a &&& s.b
  let v2806 := s.b ^^^ s.c
  let v2807 := s.a &&& v2806
  let v2808 := v2807 ^^^ (s.b &&& s.c)
  let v2809 := v2804 + v2808
  let v2810 := v2799 + s.d
  let v2811 := v2809 + v2799
  E[%2773 := .value v2773,
    %2774 := .value v2774,
    %2775 := .value v2775,
    %2776 := .value v2776,
    %2777 := .value v2777,
    %2778 := .value v2778,
    %2779 := .value v2779,
    %2780 := .value v2780,
    %2781 := .value v2781,
    %2782 := .value v2782,
    %2783 := .value v2783,
    %2784 := .value v2784,
    %2785 := .value v2785,
    %2786 := .value v2786,
    %2787 := .value v2787,
    %2788 := .value v2788,
    %2789 := .value v2789,
    %2790 := .value v2790,
    %2791 := .value v2791,
    %2792 := .value v2792,
    %2793 := .value v2793,
    %2794 := .value v2794,
    %2795 := .value v2795,
    %2796 := .value v2796,
    %2797 := .value v2797,
    %2798 := .value v2798,
    %2799 := .value v2799,
    %2800 := .value v2800,
    %2801 := .value v2801,
    %2802 := .value v2802,
    %2803 := .value v2803,
    %2804 := .value v2804,
    %2805 := .value v2805,
    %2806 := .value v2806,
    %2807 := .value v2807,
    %2808 := .value v2808,
    %2809 := .value v2809,
    %2810 := .value v2810,
    %2811 := .value v2811]

def fullOut70 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2773 := (w 55).rotateRight 1
  let v2774 := (w 55).rotateRight 8
  let v2775 := v2773 ^^^ v2774
  let v2776 := (w 55) >>> 7
  let v2777 := v2775 ^^^ v2776
  let v2778 := (w 68).rotateRight 19
  let v2779 := (w 68).rotateRight 61
  let v2780 := v2778 ^^^ v2779
  let v2781 := (w 68) >>> 6
  let v2782 := v2780 ^^^ v2781
  let v2783 := v2777 + (w 54)
  let v2784 := v2783 + (w 63)
  let v2785 := v2784 + v2782
  let v2786 := s.e.rotateRight 14
  let v2787 := s.e.rotateRight 18
  let v2788 := v2786 ^^^ v2787
  let v2789 := s.e.rotateRight 41
  let v2790 := v2788 ^^^ v2789
  let v2791 := s.e &&& s.f
  let v2792 := s.e ^^^ (-1 : Word)
  let v2793 := s.g &&& v2792
  let v2794 := v2791 ||| v2793
  let v2795 := k
  let v2796 := v2785 + v2795
  let v2797 := v2796 + s.h
  let v2798 := v2797 + v2794
  let v2799 := v2798 + v2790
  let v2800 := s.a.rotateRight 28
  let v2801 := s.a.rotateRight 34
  let v2802 := v2800 ^^^ v2801
  let v2803 := s.a.rotateRight 39
  let v2804 := v2802 ^^^ v2803
  let v2805 := s.a &&& s.b
  let v2806 := s.b ^^^ s.c
  let v2807 := s.a &&& v2806
  let v2808 := v2807 ^^^ (s.b &&& s.c)
  let v2809 := v2804 + v2808
  let v2810 := v2799 + s.d
  let v2811 := v2809 + v2799
  ⟨v2811, s.a, s.b, s.c, v2810, s.e, s.f, s.g⟩

theorem fullOut70_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut70 s w k = Spec.round s (w 70) k := by
  have hw70 := hw 70 (by decide) (by decide)
  dsimp only [fullOut70, Spec.round]
  rw [hw70]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv70_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2773 E (fullEnv70 E s w k) := by
  unfold fullEnv70
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv70_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv70 E s w k) := by
  exact (fullEnv70_before E s w k).frame (by decide)

theorem full_body70 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready70 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 560#64) 64)
    (hk : state.mem.readAt (kp.add 560#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2573 |>.take 39) state =
      .value (fullEnv70 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv70, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w54, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w65, h.w66, h.w67, h.w68, h.w69, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k70, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready70 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready70 E s w) (hw : ScheduleReady w) :
    Ready71 (fullEnv70 E s w k) (Spec.round s (w 70) k) w := by
  have hb := fullEnv70_before E s w k
  have hout := fullOut70_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv70, fullOut70, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2772 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2733 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2694 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv70, fullOut70, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2771 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2732 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2693 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv70, Spec.round, mlir_env]
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
  · rw [hb.read_val 2707 (by decide) (by rfl)]; exact h.w68
  · rw [hb.read_val 2746 (by decide) (by rfl)]; exact h.w69
  · have hwr := hw 70 (by decide) (by decide)
    simp [fullEnv70, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step70 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready70 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2573 |>.take 39) state =
      .value (E', state) ∧
      Ready71 E' (Spec.round s (w 70) (constants.toList.getD 70 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 70 0
  have hf := fullEnv70_frame E s w k
  refine ⟨fullEnv70 E s w k,
    full_body70 E state s w kp k h hc (hk 70).1 (hk 70).2,
    full_ready70 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
