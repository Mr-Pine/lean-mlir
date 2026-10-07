import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2612..2650: round 71. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv71 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2812 := (w 56).rotateRight 1
  let v2813 := (w 56).rotateRight 8
  let v2814 := v2812 ^^^ v2813
  let v2815 := (w 56) >>> 7
  let v2816 := v2814 ^^^ v2815
  let v2817 := (w 69).rotateRight 19
  let v2818 := (w 69).rotateRight 61
  let v2819 := v2817 ^^^ v2818
  let v2820 := (w 69) >>> 6
  let v2821 := v2819 ^^^ v2820
  let v2822 := v2816 + (w 55)
  let v2823 := v2822 + (w 64)
  let v2824 := v2823 + v2821
  let v2825 := s.e.rotateRight 14
  let v2826 := s.e.rotateRight 18
  let v2827 := v2825 ^^^ v2826
  let v2828 := s.e.rotateRight 41
  let v2829 := v2827 ^^^ v2828
  let v2830 := s.e &&& s.f
  let v2831 := s.e ^^^ (-1 : Word)
  let v2832 := s.g &&& v2831
  let v2833 := v2830 ||| v2832
  let v2834 := k
  let v2835 := v2824 + v2834
  let v2836 := v2835 + s.h
  let v2837 := v2836 + v2833
  let v2838 := v2837 + v2829
  let v2839 := s.a.rotateRight 28
  let v2840 := s.a.rotateRight 34
  let v2841 := v2839 ^^^ v2840
  let v2842 := s.a.rotateRight 39
  let v2843 := v2841 ^^^ v2842
  let v2844 := s.a &&& s.b
  let v2845 := s.b ^^^ s.c
  let v2846 := s.a &&& v2845
  let v2847 := v2846 ^^^ (s.b &&& s.c)
  let v2848 := v2843 + v2847
  let v2849 := v2838 + s.d
  let v2850 := v2848 + v2838
  E[%2812 := .value v2812,
    %2813 := .value v2813,
    %2814 := .value v2814,
    %2815 := .value v2815,
    %2816 := .value v2816,
    %2817 := .value v2817,
    %2818 := .value v2818,
    %2819 := .value v2819,
    %2820 := .value v2820,
    %2821 := .value v2821,
    %2822 := .value v2822,
    %2823 := .value v2823,
    %2824 := .value v2824,
    %2825 := .value v2825,
    %2826 := .value v2826,
    %2827 := .value v2827,
    %2828 := .value v2828,
    %2829 := .value v2829,
    %2830 := .value v2830,
    %2831 := .value v2831,
    %2832 := .value v2832,
    %2833 := .value v2833,
    %2834 := .value v2834,
    %2835 := .value v2835,
    %2836 := .value v2836,
    %2837 := .value v2837,
    %2838 := .value v2838,
    %2839 := .value v2839,
    %2840 := .value v2840,
    %2841 := .value v2841,
    %2842 := .value v2842,
    %2843 := .value v2843,
    %2844 := .value v2844,
    %2845 := .value v2845,
    %2846 := .value v2846,
    %2847 := .value v2847,
    %2848 := .value v2848,
    %2849 := .value v2849,
    %2850 := .value v2850]

def fullOut71 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2812 := (w 56).rotateRight 1
  let v2813 := (w 56).rotateRight 8
  let v2814 := v2812 ^^^ v2813
  let v2815 := (w 56) >>> 7
  let v2816 := v2814 ^^^ v2815
  let v2817 := (w 69).rotateRight 19
  let v2818 := (w 69).rotateRight 61
  let v2819 := v2817 ^^^ v2818
  let v2820 := (w 69) >>> 6
  let v2821 := v2819 ^^^ v2820
  let v2822 := v2816 + (w 55)
  let v2823 := v2822 + (w 64)
  let v2824 := v2823 + v2821
  let v2825 := s.e.rotateRight 14
  let v2826 := s.e.rotateRight 18
  let v2827 := v2825 ^^^ v2826
  let v2828 := s.e.rotateRight 41
  let v2829 := v2827 ^^^ v2828
  let v2830 := s.e &&& s.f
  let v2831 := s.e ^^^ (-1 : Word)
  let v2832 := s.g &&& v2831
  let v2833 := v2830 ||| v2832
  let v2834 := k
  let v2835 := v2824 + v2834
  let v2836 := v2835 + s.h
  let v2837 := v2836 + v2833
  let v2838 := v2837 + v2829
  let v2839 := s.a.rotateRight 28
  let v2840 := s.a.rotateRight 34
  let v2841 := v2839 ^^^ v2840
  let v2842 := s.a.rotateRight 39
  let v2843 := v2841 ^^^ v2842
  let v2844 := s.a &&& s.b
  let v2845 := s.b ^^^ s.c
  let v2846 := s.a &&& v2845
  let v2847 := v2846 ^^^ (s.b &&& s.c)
  let v2848 := v2843 + v2847
  let v2849 := v2838 + s.d
  let v2850 := v2848 + v2838
  ⟨v2850, s.a, s.b, s.c, v2849, s.e, s.f, s.g⟩

theorem fullOut71_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut71 s w k = Spec.round s (w 71) k := by
  have hw71 := hw 71 (by decide) (by decide)
  dsimp only [fullOut71, Spec.round]
  rw [hw71]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv71_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2812 E (fullEnv71 E s w k) := by
  unfold fullEnv71
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv71_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv71 E s w k) := by
  exact (fullEnv71_before E s w k).frame (by decide)

theorem full_body71 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready71 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 568#64) 64)
    (hk : state.mem.readAt (kp.add 568#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2612 |>.take 39) state =
      .value (fullEnv71 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv71, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w55, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w65, h.w66, h.w67, h.w68, h.w69, h.w70, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k71, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready71 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready71 E s w) (hw : ScheduleReady w) :
    Ready72 (fullEnv71 E s w k) (Spec.round s (w 71) k) w := by
  have hb := fullEnv71_before E s w k
  have hout := fullOut71_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv71, fullOut71, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2811 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2772 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2733 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv71, fullOut71, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2810 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2771 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2732 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv71, Spec.round, mlir_env]
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
  · rw [hb.read_val 2785 (by decide) (by rfl)]; exact h.w70
  · have hwr := hw 71 (by decide) (by decide)
    simp [fullEnv71, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step71 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready71 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2612 |>.take 39) state =
      .value (E', state) ∧
      Ready72 E' (Spec.round s (w 71) (constants.toList.getD 71 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 71 0
  have hf := fullEnv71_frame E s w k
  refine ⟨fullEnv71 E s w k,
    full_body71 E state s w kp k h hc (hk 71).1 (hk 71).2,
    full_ready71 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
