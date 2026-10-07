import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2846..2884: round 77. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv77 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v3046 := (w 62).rotateRight 1
  let v3047 := (w 62).rotateRight 8
  let v3048 := v3046 ^^^ v3047
  let v3049 := (w 62) >>> 7
  let v3050 := v3048 ^^^ v3049
  let v3051 := (w 75).rotateRight 19
  let v3052 := (w 75).rotateRight 61
  let v3053 := v3051 ^^^ v3052
  let v3054 := (w 75) >>> 6
  let v3055 := v3053 ^^^ v3054
  let v3056 := v3050 + (w 61)
  let v3057 := v3056 + (w 70)
  let v3058 := v3057 + v3055
  let v3059 := s.e.rotateRight 14
  let v3060 := s.e.rotateRight 18
  let v3061 := v3059 ^^^ v3060
  let v3062 := s.e.rotateRight 41
  let v3063 := v3061 ^^^ v3062
  let v3064 := s.e &&& s.f
  let v3065 := s.e ^^^ (-1 : Word)
  let v3066 := s.g &&& v3065
  let v3067 := v3064 ||| v3066
  let v3068 := k
  let v3069 := v3058 + v3068
  let v3070 := v3069 + s.h
  let v3071 := v3070 + v3067
  let v3072 := v3071 + v3063
  let v3073 := s.a.rotateRight 28
  let v3074 := s.a.rotateRight 34
  let v3075 := v3073 ^^^ v3074
  let v3076 := s.a.rotateRight 39
  let v3077 := v3075 ^^^ v3076
  let v3078 := s.a &&& s.b
  let v3079 := s.b ^^^ s.c
  let v3080 := s.a &&& v3079
  let v3081 := v3080 ^^^ (s.b &&& s.c)
  let v3082 := v3077 + v3081
  let v3083 := v3072 + s.d
  let v3084 := v3082 + v3072
  E[%3046 := .value v3046,
    %3047 := .value v3047,
    %3048 := .value v3048,
    %3049 := .value v3049,
    %3050 := .value v3050,
    %3051 := .value v3051,
    %3052 := .value v3052,
    %3053 := .value v3053,
    %3054 := .value v3054,
    %3055 := .value v3055,
    %3056 := .value v3056,
    %3057 := .value v3057,
    %3058 := .value v3058,
    %3059 := .value v3059,
    %3060 := .value v3060,
    %3061 := .value v3061,
    %3062 := .value v3062,
    %3063 := .value v3063,
    %3064 := .value v3064,
    %3065 := .value v3065,
    %3066 := .value v3066,
    %3067 := .value v3067,
    %3068 := .value v3068,
    %3069 := .value v3069,
    %3070 := .value v3070,
    %3071 := .value v3071,
    %3072 := .value v3072,
    %3073 := .value v3073,
    %3074 := .value v3074,
    %3075 := .value v3075,
    %3076 := .value v3076,
    %3077 := .value v3077,
    %3078 := .value v3078,
    %3079 := .value v3079,
    %3080 := .value v3080,
    %3081 := .value v3081,
    %3082 := .value v3082,
    %3083 := .value v3083,
    %3084 := .value v3084]

def fullOut77 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v3046 := (w 62).rotateRight 1
  let v3047 := (w 62).rotateRight 8
  let v3048 := v3046 ^^^ v3047
  let v3049 := (w 62) >>> 7
  let v3050 := v3048 ^^^ v3049
  let v3051 := (w 75).rotateRight 19
  let v3052 := (w 75).rotateRight 61
  let v3053 := v3051 ^^^ v3052
  let v3054 := (w 75) >>> 6
  let v3055 := v3053 ^^^ v3054
  let v3056 := v3050 + (w 61)
  let v3057 := v3056 + (w 70)
  let v3058 := v3057 + v3055
  let v3059 := s.e.rotateRight 14
  let v3060 := s.e.rotateRight 18
  let v3061 := v3059 ^^^ v3060
  let v3062 := s.e.rotateRight 41
  let v3063 := v3061 ^^^ v3062
  let v3064 := s.e &&& s.f
  let v3065 := s.e ^^^ (-1 : Word)
  let v3066 := s.g &&& v3065
  let v3067 := v3064 ||| v3066
  let v3068 := k
  let v3069 := v3058 + v3068
  let v3070 := v3069 + s.h
  let v3071 := v3070 + v3067
  let v3072 := v3071 + v3063
  let v3073 := s.a.rotateRight 28
  let v3074 := s.a.rotateRight 34
  let v3075 := v3073 ^^^ v3074
  let v3076 := s.a.rotateRight 39
  let v3077 := v3075 ^^^ v3076
  let v3078 := s.a &&& s.b
  let v3079 := s.b ^^^ s.c
  let v3080 := s.a &&& v3079
  let v3081 := v3080 ^^^ (s.b &&& s.c)
  let v3082 := v3077 + v3081
  let v3083 := v3072 + s.d
  let v3084 := v3082 + v3072
  ⟨v3084, s.a, s.b, s.c, v3083, s.e, s.f, s.g⟩

theorem fullOut77_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut77 s w k = Spec.round s (w 77) k := by
  have hw77 := hw 77 (by decide) (by decide)
  dsimp only [fullOut77, Spec.round]
  rw [hw77]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv77_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 3046 E (fullEnv77 E s w k) := by
  unfold fullEnv77
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv77_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv77 E s w k) := by
  exact (fullEnv77_before E s w k).frame (by decide)

theorem full_body77 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready77 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 616#64) 64)
    (hk : state.mem.readAt (kp.add 616#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2846 |>.take 39) state =
      .value (fullEnv77 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv77, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w61, h.w62, h.w63, h.w64, h.w70, h.w71, h.w72, h.w75, h.w76, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k77, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready77 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready77 E s w) (hw : ScheduleReady w) :
    Ready78 (fullEnv77 E s w k) (Spec.round s (w 77) k) w := by
  have hb := fullEnv77_before E s w k
  have hout := fullOut77_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv77, fullOut77, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 3045 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 3006 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2967 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv77, fullOut77, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 3044 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 3005 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2966 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv77, Spec.round, mlir_env]
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · rw [hb.read_val 2824 (by decide) (by rfl)]; exact h.w71
  · rw [hb.read_val 2863 (by decide) (by rfl)]; exact h.w72
  · rw [hb.read_val 3019 (by decide) (by rfl)]; exact h.w76
  · have hwr := hw 77 (by decide) (by decide)
    simp [fullEnv77, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step77 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready77 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2846 |>.take 39) state =
      .value (E', state) ∧
      Ready78 E' (Spec.round s (w 77) (constants.toList.getD 77 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 77 0
  have hf := fullEnv77_frame E s w k
  refine ⟨fullEnv77 E s w k,
    full_body77 E state s w kp k h hc (hk 77).1 (hk 77).2,
    full_ready77 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
