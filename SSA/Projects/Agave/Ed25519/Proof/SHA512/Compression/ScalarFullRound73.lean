import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2690..2728: round 73. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv73 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2890 := (w 58).rotateRight 1
  let v2891 := (w 58).rotateRight 8
  let v2892 := v2890 ^^^ v2891
  let v2893 := (w 58) >>> 7
  let v2894 := v2892 ^^^ v2893
  let v2895 := (w 71).rotateRight 19
  let v2896 := (w 71).rotateRight 61
  let v2897 := v2895 ^^^ v2896
  let v2898 := (w 71) >>> 6
  let v2899 := v2897 ^^^ v2898
  let v2900 := v2894 + (w 57)
  let v2901 := v2900 + (w 66)
  let v2902 := v2901 + v2899
  let v2903 := s.e.rotateRight 14
  let v2904 := s.e.rotateRight 18
  let v2905 := v2903 ^^^ v2904
  let v2906 := s.e.rotateRight 41
  let v2907 := v2905 ^^^ v2906
  let v2908 := s.e &&& s.f
  let v2909 := s.e ^^^ (-1 : Word)
  let v2910 := s.g &&& v2909
  let v2911 := v2908 ||| v2910
  let v2912 := k
  let v2913 := v2902 + v2912
  let v2914 := v2913 + s.h
  let v2915 := v2914 + v2911
  let v2916 := v2915 + v2907
  let v2917 := s.a.rotateRight 28
  let v2918 := s.a.rotateRight 34
  let v2919 := v2917 ^^^ v2918
  let v2920 := s.a.rotateRight 39
  let v2921 := v2919 ^^^ v2920
  let v2922 := s.a &&& s.b
  let v2923 := s.b ^^^ s.c
  let v2924 := s.a &&& v2923
  let v2925 := v2924 ^^^ (s.b &&& s.c)
  let v2926 := v2921 + v2925
  let v2927 := v2916 + s.d
  let v2928 := v2926 + v2916
  E[%2890 := .value v2890,
    %2891 := .value v2891,
    %2892 := .value v2892,
    %2893 := .value v2893,
    %2894 := .value v2894,
    %2895 := .value v2895,
    %2896 := .value v2896,
    %2897 := .value v2897,
    %2898 := .value v2898,
    %2899 := .value v2899,
    %2900 := .value v2900,
    %2901 := .value v2901,
    %2902 := .value v2902,
    %2903 := .value v2903,
    %2904 := .value v2904,
    %2905 := .value v2905,
    %2906 := .value v2906,
    %2907 := .value v2907,
    %2908 := .value v2908,
    %2909 := .value v2909,
    %2910 := .value v2910,
    %2911 := .value v2911,
    %2912 := .value v2912,
    %2913 := .value v2913,
    %2914 := .value v2914,
    %2915 := .value v2915,
    %2916 := .value v2916,
    %2917 := .value v2917,
    %2918 := .value v2918,
    %2919 := .value v2919,
    %2920 := .value v2920,
    %2921 := .value v2921,
    %2922 := .value v2922,
    %2923 := .value v2923,
    %2924 := .value v2924,
    %2925 := .value v2925,
    %2926 := .value v2926,
    %2927 := .value v2927,
    %2928 := .value v2928]

def fullOut73 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2890 := (w 58).rotateRight 1
  let v2891 := (w 58).rotateRight 8
  let v2892 := v2890 ^^^ v2891
  let v2893 := (w 58) >>> 7
  let v2894 := v2892 ^^^ v2893
  let v2895 := (w 71).rotateRight 19
  let v2896 := (w 71).rotateRight 61
  let v2897 := v2895 ^^^ v2896
  let v2898 := (w 71) >>> 6
  let v2899 := v2897 ^^^ v2898
  let v2900 := v2894 + (w 57)
  let v2901 := v2900 + (w 66)
  let v2902 := v2901 + v2899
  let v2903 := s.e.rotateRight 14
  let v2904 := s.e.rotateRight 18
  let v2905 := v2903 ^^^ v2904
  let v2906 := s.e.rotateRight 41
  let v2907 := v2905 ^^^ v2906
  let v2908 := s.e &&& s.f
  let v2909 := s.e ^^^ (-1 : Word)
  let v2910 := s.g &&& v2909
  let v2911 := v2908 ||| v2910
  let v2912 := k
  let v2913 := v2902 + v2912
  let v2914 := v2913 + s.h
  let v2915 := v2914 + v2911
  let v2916 := v2915 + v2907
  let v2917 := s.a.rotateRight 28
  let v2918 := s.a.rotateRight 34
  let v2919 := v2917 ^^^ v2918
  let v2920 := s.a.rotateRight 39
  let v2921 := v2919 ^^^ v2920
  let v2922 := s.a &&& s.b
  let v2923 := s.b ^^^ s.c
  let v2924 := s.a &&& v2923
  let v2925 := v2924 ^^^ (s.b &&& s.c)
  let v2926 := v2921 + v2925
  let v2927 := v2916 + s.d
  let v2928 := v2926 + v2916
  ⟨v2928, s.a, s.b, s.c, v2927, s.e, s.f, s.g⟩

theorem fullOut73_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut73 s w k = Spec.round s (w 73) k := by
  have hw73 := hw 73 (by decide) (by decide)
  dsimp only [fullOut73, Spec.round]
  rw [hw73]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv73_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2890 E (fullEnv73 E s w k) := by
  unfold fullEnv73
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv73_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv73 E s w k) := by
  exact (fullEnv73_before E s w k).frame (by decide)

theorem full_body73 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready73 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 584#64) 64)
    (hk : state.mem.readAt (kp.add 584#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2690 |>.take 39) state =
      .value (fullEnv73 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv73, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w57, h.w58, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w66, h.w67, h.w68, h.w69, h.w70, h.w71, h.w72, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k73, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready73 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready73 E s w) (hw : ScheduleReady w) :
    Ready74 (fullEnv73 E s w k) (Spec.round s (w 73) k) w := by
  have hb := fullEnv73_before E s w k
  have hout := fullOut73_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv73, fullOut73, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2889 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2850 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2811 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv73, fullOut73, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2888 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2849 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2810 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv73, Spec.round, mlir_env]
  · rw [hb.read_val 2317 (by decide) (by rfl)]; exact h.w58
  · rw [hb.read_val 2356 (by decide) (by rfl)]; exact h.w59
  · rw [hb.read_val 2395 (by decide) (by rfl)]; exact h.w60
  · rw [hb.read_val 2434 (by decide) (by rfl)]; exact h.w61
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · rw [hb.read_val 2668 (by decide) (by rfl)]; exact h.w67
  · rw [hb.read_val 2707 (by decide) (by rfl)]; exact h.w68
  · rw [hb.read_val 2746 (by decide) (by rfl)]; exact h.w69
  · rw [hb.read_val 2785 (by decide) (by rfl)]; exact h.w70
  · rw [hb.read_val 2824 (by decide) (by rfl)]; exact h.w71
  · rw [hb.read_val 2863 (by decide) (by rfl)]; exact h.w72
  · have hwr := hw 73 (by decide) (by decide)
    simp [fullEnv73, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step73 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready73 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2690 |>.take 39) state =
      .value (E', state) ∧
      Ready74 E' (Spec.round s (w 73) (constants.toList.getD 73 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 73 0
  have hf := fullEnv73_frame E s w k
  refine ⟨fullEnv73 E s w k,
    full_body73 E state s w kp k h hc (hk 73).1 (hk 73).2,
    full_ready73 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
