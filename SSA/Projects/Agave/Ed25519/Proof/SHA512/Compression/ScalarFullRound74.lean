import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2729..2767: round 74. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv74 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2929 := (w 59).rotateRight 1
  let v2930 := (w 59).rotateRight 8
  let v2931 := v2929 ^^^ v2930
  let v2932 := (w 59) >>> 7
  let v2933 := v2931 ^^^ v2932
  let v2934 := (w 72).rotateRight 19
  let v2935 := (w 72).rotateRight 61
  let v2936 := v2934 ^^^ v2935
  let v2937 := (w 72) >>> 6
  let v2938 := v2936 ^^^ v2937
  let v2939 := v2933 + (w 58)
  let v2940 := v2939 + (w 67)
  let v2941 := v2940 + v2938
  let v2942 := s.e.rotateRight 14
  let v2943 := s.e.rotateRight 18
  let v2944 := v2942 ^^^ v2943
  let v2945 := s.e.rotateRight 41
  let v2946 := v2944 ^^^ v2945
  let v2947 := s.e &&& s.f
  let v2948 := s.e ^^^ (-1 : Word)
  let v2949 := s.g &&& v2948
  let v2950 := v2947 ||| v2949
  let v2951 := k
  let v2952 := v2941 + v2951
  let v2953 := v2952 + s.h
  let v2954 := v2953 + v2950
  let v2955 := v2954 + v2946
  let v2956 := s.a.rotateRight 28
  let v2957 := s.a.rotateRight 34
  let v2958 := v2956 ^^^ v2957
  let v2959 := s.a.rotateRight 39
  let v2960 := v2958 ^^^ v2959
  let v2961 := s.a &&& s.b
  let v2962 := s.b ^^^ s.c
  let v2963 := s.a &&& v2962
  let v2964 := v2963 ^^^ (s.b &&& s.c)
  let v2965 := v2960 + v2964
  let v2966 := v2955 + s.d
  let v2967 := v2965 + v2955
  E[%2929 := .value v2929,
    %2930 := .value v2930,
    %2931 := .value v2931,
    %2932 := .value v2932,
    %2933 := .value v2933,
    %2934 := .value v2934,
    %2935 := .value v2935,
    %2936 := .value v2936,
    %2937 := .value v2937,
    %2938 := .value v2938,
    %2939 := .value v2939,
    %2940 := .value v2940,
    %2941 := .value v2941,
    %2942 := .value v2942,
    %2943 := .value v2943,
    %2944 := .value v2944,
    %2945 := .value v2945,
    %2946 := .value v2946,
    %2947 := .value v2947,
    %2948 := .value v2948,
    %2949 := .value v2949,
    %2950 := .value v2950,
    %2951 := .value v2951,
    %2952 := .value v2952,
    %2953 := .value v2953,
    %2954 := .value v2954,
    %2955 := .value v2955,
    %2956 := .value v2956,
    %2957 := .value v2957,
    %2958 := .value v2958,
    %2959 := .value v2959,
    %2960 := .value v2960,
    %2961 := .value v2961,
    %2962 := .value v2962,
    %2963 := .value v2963,
    %2964 := .value v2964,
    %2965 := .value v2965,
    %2966 := .value v2966,
    %2967 := .value v2967]

def fullOut74 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2929 := (w 59).rotateRight 1
  let v2930 := (w 59).rotateRight 8
  let v2931 := v2929 ^^^ v2930
  let v2932 := (w 59) >>> 7
  let v2933 := v2931 ^^^ v2932
  let v2934 := (w 72).rotateRight 19
  let v2935 := (w 72).rotateRight 61
  let v2936 := v2934 ^^^ v2935
  let v2937 := (w 72) >>> 6
  let v2938 := v2936 ^^^ v2937
  let v2939 := v2933 + (w 58)
  let v2940 := v2939 + (w 67)
  let v2941 := v2940 + v2938
  let v2942 := s.e.rotateRight 14
  let v2943 := s.e.rotateRight 18
  let v2944 := v2942 ^^^ v2943
  let v2945 := s.e.rotateRight 41
  let v2946 := v2944 ^^^ v2945
  let v2947 := s.e &&& s.f
  let v2948 := s.e ^^^ (-1 : Word)
  let v2949 := s.g &&& v2948
  let v2950 := v2947 ||| v2949
  let v2951 := k
  let v2952 := v2941 + v2951
  let v2953 := v2952 + s.h
  let v2954 := v2953 + v2950
  let v2955 := v2954 + v2946
  let v2956 := s.a.rotateRight 28
  let v2957 := s.a.rotateRight 34
  let v2958 := v2956 ^^^ v2957
  let v2959 := s.a.rotateRight 39
  let v2960 := v2958 ^^^ v2959
  let v2961 := s.a &&& s.b
  let v2962 := s.b ^^^ s.c
  let v2963 := s.a &&& v2962
  let v2964 := v2963 ^^^ (s.b &&& s.c)
  let v2965 := v2960 + v2964
  let v2966 := v2955 + s.d
  let v2967 := v2965 + v2955
  ⟨v2967, s.a, s.b, s.c, v2966, s.e, s.f, s.g⟩

theorem fullOut74_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut74 s w k = Spec.round s (w 74) k := by
  have hw74 := hw 74 (by decide) (by decide)
  dsimp only [fullOut74, Spec.round]
  rw [hw74]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv74_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2929 E (fullEnv74 E s w k) := by
  unfold fullEnv74
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv74_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv74 E s w k) := by
  exact (fullEnv74_before E s w k).frame (by decide)

theorem full_body74 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready74 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 592#64) 64)
    (hk : state.mem.readAt (kp.add 592#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2729 |>.take 39) state =
      .value (fullEnv74 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv74, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w67, h.w68, h.w69, h.w70, h.w71, h.w72, h.w73, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k74, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready74 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready74 E s w) (hw : ScheduleReady w) :
    Ready75 (fullEnv74 E s w k) (Spec.round s (w 74) k) w := by
  have hb := fullEnv74_before E s w k
  have hout := fullOut74_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv74, fullOut74, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2928 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2889 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2850 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv74, fullOut74, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2927 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2888 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2849 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv74, Spec.round, mlir_env]
  · rw [hb.read_val 2356 (by decide) (by rfl)]; exact h.w59
  · rw [hb.read_val 2395 (by decide) (by rfl)]; exact h.w60
  · rw [hb.read_val 2434 (by decide) (by rfl)]; exact h.w61
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · rw [hb.read_val 2707 (by decide) (by rfl)]; exact h.w68
  · rw [hb.read_val 2746 (by decide) (by rfl)]; exact h.w69
  · rw [hb.read_val 2785 (by decide) (by rfl)]; exact h.w70
  · rw [hb.read_val 2824 (by decide) (by rfl)]; exact h.w71
  · rw [hb.read_val 2863 (by decide) (by rfl)]; exact h.w72
  · rw [hb.read_val 2902 (by decide) (by rfl)]; exact h.w73
  · have hwr := hw 74 (by decide) (by decide)
    simp [fullEnv74, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step74 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready74 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2729 |>.take 39) state =
      .value (E', state) ∧
      Ready75 E' (Spec.round s (w 74) (constants.toList.getD 74 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 74 0
  have hf := fullEnv74_frame E s w k
  refine ⟨fullEnv74 E s w k,
    full_body74 E state s w kp k h hc (hk 74).1 (hk 74).2,
    full_ready74 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
