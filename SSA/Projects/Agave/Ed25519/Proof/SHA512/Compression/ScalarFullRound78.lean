import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2885..2923: round 78. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv78 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v3085 := (w 63).rotateRight 1
  let v3086 := (w 63).rotateRight 8
  let v3087 := v3085 ^^^ v3086
  let v3088 := (w 63) >>> 7
  let v3089 := v3087 ^^^ v3088
  let v3090 := (w 76).rotateRight 19
  let v3091 := (w 76).rotateRight 61
  let v3092 := v3090 ^^^ v3091
  let v3093 := (w 76) >>> 6
  let v3094 := v3092 ^^^ v3093
  let v3095 := s.e.rotateRight 14
  let v3096 := s.e.rotateRight 18
  let v3097 := v3095 ^^^ v3096
  let v3098 := s.e.rotateRight 41
  let v3099 := v3097 ^^^ v3098
  let v3100 := s.e &&& s.f
  let v3101 := s.e ^^^ (-1 : Word)
  let v3102 := s.g &&& v3101
  let v3103 := v3100 ||| v3102
  let v3104 := k
  let v3105 := (w 62) + v3104
  let v3106 := v3105 + v3089
  let v3107 := v3106 + (w 71)
  let v3108 := v3107 + v3094
  let v3109 := v3108 + s.h
  let v3110 := v3109 + v3103
  let v3111 := v3110 + v3099
  let v3112 := s.a.rotateRight 28
  let v3113 := s.a.rotateRight 34
  let v3114 := v3112 ^^^ v3113
  let v3115 := s.a.rotateRight 39
  let v3116 := v3114 ^^^ v3115
  let v3117 := s.a &&& s.b
  let v3118 := s.b ^^^ s.c
  let v3119 := s.a &&& v3118
  let v3120 := v3119 ^^^ (s.b &&& s.c)
  let v3121 := v3116 + v3120
  let v3122 := v3111 + s.d
  let v3123 := v3121 + v3111
  E[%3085 := .value v3085,
    %3086 := .value v3086,
    %3087 := .value v3087,
    %3088 := .value v3088,
    %3089 := .value v3089,
    %3090 := .value v3090,
    %3091 := .value v3091,
    %3092 := .value v3092,
    %3093 := .value v3093,
    %3094 := .value v3094,
    %3095 := .value v3095,
    %3096 := .value v3096,
    %3097 := .value v3097,
    %3098 := .value v3098,
    %3099 := .value v3099,
    %3100 := .value v3100,
    %3101 := .value v3101,
    %3102 := .value v3102,
    %3103 := .value v3103,
    %3104 := .value v3104,
    %3105 := .value v3105,
    %3106 := .value v3106,
    %3107 := .value v3107,
    %3108 := .value v3108,
    %3109 := .value v3109,
    %3110 := .value v3110,
    %3111 := .value v3111,
    %3112 := .value v3112,
    %3113 := .value v3113,
    %3114 := .value v3114,
    %3115 := .value v3115,
    %3116 := .value v3116,
    %3117 := .value v3117,
    %3118 := .value v3118,
    %3119 := .value v3119,
    %3120 := .value v3120,
    %3121 := .value v3121,
    %3122 := .value v3122,
    %3123 := .value v3123]

def fullOut78 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v3085 := (w 63).rotateRight 1
  let v3086 := (w 63).rotateRight 8
  let v3087 := v3085 ^^^ v3086
  let v3088 := (w 63) >>> 7
  let v3089 := v3087 ^^^ v3088
  let v3090 := (w 76).rotateRight 19
  let v3091 := (w 76).rotateRight 61
  let v3092 := v3090 ^^^ v3091
  let v3093 := (w 76) >>> 6
  let v3094 := v3092 ^^^ v3093
  let v3095 := s.e.rotateRight 14
  let v3096 := s.e.rotateRight 18
  let v3097 := v3095 ^^^ v3096
  let v3098 := s.e.rotateRight 41
  let v3099 := v3097 ^^^ v3098
  let v3100 := s.e &&& s.f
  let v3101 := s.e ^^^ (-1 : Word)
  let v3102 := s.g &&& v3101
  let v3103 := v3100 ||| v3102
  let v3104 := k
  let v3105 := (w 62) + v3104
  let v3106 := v3105 + v3089
  let v3107 := v3106 + (w 71)
  let v3108 := v3107 + v3094
  let v3109 := v3108 + s.h
  let v3110 := v3109 + v3103
  let v3111 := v3110 + v3099
  let v3112 := s.a.rotateRight 28
  let v3113 := s.a.rotateRight 34
  let v3114 := v3112 ^^^ v3113
  let v3115 := s.a.rotateRight 39
  let v3116 := v3114 ^^^ v3115
  let v3117 := s.a &&& s.b
  let v3118 := s.b ^^^ s.c
  let v3119 := s.a &&& v3118
  let v3120 := v3119 ^^^ (s.b &&& s.c)
  let v3121 := v3116 + v3120
  let v3122 := v3111 + s.d
  let v3123 := v3121 + v3111
  ⟨v3123, s.a, s.b, s.c, v3122, s.e, s.f, s.g⟩

theorem fullOut78_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut78 s w k = Spec.round s (w 78) k := by
  have hw78 := hw 78 (by decide) (by decide)
  dsimp only [fullOut78, Spec.round]
  rw [hw78]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv78_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 3085 E (fullEnv78 E s w k) := by
  unfold fullEnv78
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv78_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv78 E s w k) := by
  exact (fullEnv78_before E s w k).frame (by decide)

theorem full_body78 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready78 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 624#64) 64)
    (hk : state.mem.readAt (kp.add 624#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2885 |>.take 39) state =
      .value (fullEnv78 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv78, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w62, h.w63, h.w64, h.w71, h.w72, h.w76, h.w77, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k78, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready78 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready78 E s w) (hw : ScheduleReady w) :
    Ready79 (fullEnv78 E s w k) (Spec.round s (w 78) k) w := by
  have hb := fullEnv78_before E s w k
  have hout := fullOut78_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv78, fullOut78, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 3084 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 3045 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 3006 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv78, fullOut78, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 3083 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 3044 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 3005 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv78, Spec.round, mlir_env]
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · rw [hb.read_val 2863 (by decide) (by rfl)]; exact h.w72
  · rw [hb.read_val 3058 (by decide) (by rfl)]; exact h.w77

theorem full_step78 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready78 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2885 |>.take 39) state =
      .value (E', state) ∧
      Ready79 E' (Spec.round s (w 78) (constants.toList.getD 78 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 78 0
  have hf := fullEnv78_frame E s w k
  refine ⟨fullEnv78 E s w k,
    full_body78 E state s w kp k h hc (hk 78).1 (hk 78).2,
    full_ready78 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
