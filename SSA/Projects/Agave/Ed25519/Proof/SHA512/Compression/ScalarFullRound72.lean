import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2651..2689: round 72. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv72 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2851 := (w 57).rotateRight 1
  let v2852 := (w 57).rotateRight 8
  let v2853 := v2851 ^^^ v2852
  let v2854 := (w 57) >>> 7
  let v2855 := v2853 ^^^ v2854
  let v2856 := (w 70).rotateRight 19
  let v2857 := (w 70).rotateRight 61
  let v2858 := v2856 ^^^ v2857
  let v2859 := (w 70) >>> 6
  let v2860 := v2858 ^^^ v2859
  let v2861 := v2855 + (w 56)
  let v2862 := v2861 + (w 65)
  let v2863 := v2862 + v2860
  let v2864 := s.e.rotateRight 14
  let v2865 := s.e.rotateRight 18
  let v2866 := v2864 ^^^ v2865
  let v2867 := s.e.rotateRight 41
  let v2868 := v2866 ^^^ v2867
  let v2869 := s.e &&& s.f
  let v2870 := s.e ^^^ (-1 : Word)
  let v2871 := s.g &&& v2870
  let v2872 := v2869 ||| v2871
  let v2873 := k
  let v2874 := v2863 + v2873
  let v2875 := v2874 + s.h
  let v2876 := v2875 + v2872
  let v2877 := v2876 + v2868
  let v2878 := s.a.rotateRight 28
  let v2879 := s.a.rotateRight 34
  let v2880 := v2878 ^^^ v2879
  let v2881 := s.a.rotateRight 39
  let v2882 := v2880 ^^^ v2881
  let v2883 := s.a &&& s.b
  let v2884 := s.b ^^^ s.c
  let v2885 := s.a &&& v2884
  let v2886 := v2885 ^^^ (s.b &&& s.c)
  let v2887 := v2882 + v2886
  let v2888 := v2877 + s.d
  let v2889 := v2887 + v2877
  E[%2851 := .value v2851,
    %2852 := .value v2852,
    %2853 := .value v2853,
    %2854 := .value v2854,
    %2855 := .value v2855,
    %2856 := .value v2856,
    %2857 := .value v2857,
    %2858 := .value v2858,
    %2859 := .value v2859,
    %2860 := .value v2860,
    %2861 := .value v2861,
    %2862 := .value v2862,
    %2863 := .value v2863,
    %2864 := .value v2864,
    %2865 := .value v2865,
    %2866 := .value v2866,
    %2867 := .value v2867,
    %2868 := .value v2868,
    %2869 := .value v2869,
    %2870 := .value v2870,
    %2871 := .value v2871,
    %2872 := .value v2872,
    %2873 := .value v2873,
    %2874 := .value v2874,
    %2875 := .value v2875,
    %2876 := .value v2876,
    %2877 := .value v2877,
    %2878 := .value v2878,
    %2879 := .value v2879,
    %2880 := .value v2880,
    %2881 := .value v2881,
    %2882 := .value v2882,
    %2883 := .value v2883,
    %2884 := .value v2884,
    %2885 := .value v2885,
    %2886 := .value v2886,
    %2887 := .value v2887,
    %2888 := .value v2888,
    %2889 := .value v2889]

def fullOut72 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2851 := (w 57).rotateRight 1
  let v2852 := (w 57).rotateRight 8
  let v2853 := v2851 ^^^ v2852
  let v2854 := (w 57) >>> 7
  let v2855 := v2853 ^^^ v2854
  let v2856 := (w 70).rotateRight 19
  let v2857 := (w 70).rotateRight 61
  let v2858 := v2856 ^^^ v2857
  let v2859 := (w 70) >>> 6
  let v2860 := v2858 ^^^ v2859
  let v2861 := v2855 + (w 56)
  let v2862 := v2861 + (w 65)
  let v2863 := v2862 + v2860
  let v2864 := s.e.rotateRight 14
  let v2865 := s.e.rotateRight 18
  let v2866 := v2864 ^^^ v2865
  let v2867 := s.e.rotateRight 41
  let v2868 := v2866 ^^^ v2867
  let v2869 := s.e &&& s.f
  let v2870 := s.e ^^^ (-1 : Word)
  let v2871 := s.g &&& v2870
  let v2872 := v2869 ||| v2871
  let v2873 := k
  let v2874 := v2863 + v2873
  let v2875 := v2874 + s.h
  let v2876 := v2875 + v2872
  let v2877 := v2876 + v2868
  let v2878 := s.a.rotateRight 28
  let v2879 := s.a.rotateRight 34
  let v2880 := v2878 ^^^ v2879
  let v2881 := s.a.rotateRight 39
  let v2882 := v2880 ^^^ v2881
  let v2883 := s.a &&& s.b
  let v2884 := s.b ^^^ s.c
  let v2885 := s.a &&& v2884
  let v2886 := v2885 ^^^ (s.b &&& s.c)
  let v2887 := v2882 + v2886
  let v2888 := v2877 + s.d
  let v2889 := v2887 + v2877
  ⟨v2889, s.a, s.b, s.c, v2888, s.e, s.f, s.g⟩

theorem fullOut72_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut72 s w k = Spec.round s (w 72) k := by
  have hw72 := hw 72 (by decide) (by decide)
  dsimp only [fullOut72, Spec.round]
  rw [hw72]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv72_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2851 E (fullEnv72 E s w k) := by
  unfold fullEnv72
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv72_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv72 E s w k) := by
  exact (fullEnv72_before E s w k).frame (by decide)

theorem full_body72 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready72 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 576#64) 64)
    (hk : state.mem.readAt (kp.add 576#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2651 |>.take 39) state =
      .value (fullEnv72 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv72, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w56, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w65, h.w66, h.w67, h.w68, h.w69, h.w70, h.w71, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k72, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready72 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready72 E s w) (hw : ScheduleReady w) :
    Ready73 (fullEnv72 E s w k) (Spec.round s (w 72) k) w := by
  have hb := fullEnv72_before E s w k
  have hout := fullOut72_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv72, fullOut72, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2850 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2811 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2772 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv72, fullOut72, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2849 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2810 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2771 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv72, Spec.round, mlir_env]
  · rw [hb.read_val 2278 (by decide) (by rfl)]; exact h.w57
  · rw [hb.read_val 2317 (by decide) (by rfl)]; exact h.w58
  · rw [hb.read_val 2356 (by decide) (by rfl)]; exact h.w59
  · rw [hb.read_val 2395 (by decide) (by rfl)]; exact h.w60
  · rw [hb.read_val 2434 (by decide) (by rfl)]; exact h.w61
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · rw [hb.read_val 2629 (by decide) (by rfl)]; exact h.w66
  · rw [hb.read_val 2668 (by decide) (by rfl)]; exact h.w67
  · rw [hb.read_val 2707 (by decide) (by rfl)]; exact h.w68
  · rw [hb.read_val 2746 (by decide) (by rfl)]; exact h.w69
  · rw [hb.read_val 2785 (by decide) (by rfl)]; exact h.w70
  · rw [hb.read_val 2824 (by decide) (by rfl)]; exact h.w71
  · have hwr := hw 72 (by decide) (by decide)
    simp [fullEnv72, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step72 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready72 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2651 |>.take 39) state =
      .value (E', state) ∧
      Ready73 E' (Spec.round s (w 72) (constants.toList.getD 72 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 72 0
  have hf := fullEnv72_frame E s w k
  refine ⟨fullEnv72 E s w k,
    full_body72 E state s w kp k h hc (hk 72).1 (hk 72).2,
    full_ready72 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
