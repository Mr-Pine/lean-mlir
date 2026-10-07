import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2807..2845: round 76. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv76 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v3007 := (w 61).rotateRight 1
  let v3008 := (w 61).rotateRight 8
  let v3009 := v3007 ^^^ v3008
  let v3010 := (w 61) >>> 7
  let v3011 := v3009 ^^^ v3010
  let v3012 := (w 74).rotateRight 19
  let v3013 := (w 74).rotateRight 61
  let v3014 := v3012 ^^^ v3013
  let v3015 := (w 74) >>> 6
  let v3016 := v3014 ^^^ v3015
  let v3017 := v3011 + (w 60)
  let v3018 := v3017 + (w 69)
  let v3019 := v3018 + v3016
  let v3020 := s.e.rotateRight 14
  let v3021 := s.e.rotateRight 18
  let v3022 := v3020 ^^^ v3021
  let v3023 := s.e.rotateRight 41
  let v3024 := v3022 ^^^ v3023
  let v3025 := s.e &&& s.f
  let v3026 := s.e ^^^ (-1 : Word)
  let v3027 := s.g &&& v3026
  let v3028 := v3025 ||| v3027
  let v3029 := k
  let v3030 := v3019 + v3029
  let v3031 := v3030 + s.h
  let v3032 := v3031 + v3028
  let v3033 := v3032 + v3024
  let v3034 := s.a.rotateRight 28
  let v3035 := s.a.rotateRight 34
  let v3036 := v3034 ^^^ v3035
  let v3037 := s.a.rotateRight 39
  let v3038 := v3036 ^^^ v3037
  let v3039 := s.a &&& s.b
  let v3040 := s.b ^^^ s.c
  let v3041 := s.a &&& v3040
  let v3042 := v3041 ^^^ (s.b &&& s.c)
  let v3043 := v3038 + v3042
  let v3044 := v3033 + s.d
  let v3045 := v3043 + v3033
  E[%3007 := .value v3007,
    %3008 := .value v3008,
    %3009 := .value v3009,
    %3010 := .value v3010,
    %3011 := .value v3011,
    %3012 := .value v3012,
    %3013 := .value v3013,
    %3014 := .value v3014,
    %3015 := .value v3015,
    %3016 := .value v3016,
    %3017 := .value v3017,
    %3018 := .value v3018,
    %3019 := .value v3019,
    %3020 := .value v3020,
    %3021 := .value v3021,
    %3022 := .value v3022,
    %3023 := .value v3023,
    %3024 := .value v3024,
    %3025 := .value v3025,
    %3026 := .value v3026,
    %3027 := .value v3027,
    %3028 := .value v3028,
    %3029 := .value v3029,
    %3030 := .value v3030,
    %3031 := .value v3031,
    %3032 := .value v3032,
    %3033 := .value v3033,
    %3034 := .value v3034,
    %3035 := .value v3035,
    %3036 := .value v3036,
    %3037 := .value v3037,
    %3038 := .value v3038,
    %3039 := .value v3039,
    %3040 := .value v3040,
    %3041 := .value v3041,
    %3042 := .value v3042,
    %3043 := .value v3043,
    %3044 := .value v3044,
    %3045 := .value v3045]

def fullOut76 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v3007 := (w 61).rotateRight 1
  let v3008 := (w 61).rotateRight 8
  let v3009 := v3007 ^^^ v3008
  let v3010 := (w 61) >>> 7
  let v3011 := v3009 ^^^ v3010
  let v3012 := (w 74).rotateRight 19
  let v3013 := (w 74).rotateRight 61
  let v3014 := v3012 ^^^ v3013
  let v3015 := (w 74) >>> 6
  let v3016 := v3014 ^^^ v3015
  let v3017 := v3011 + (w 60)
  let v3018 := v3017 + (w 69)
  let v3019 := v3018 + v3016
  let v3020 := s.e.rotateRight 14
  let v3021 := s.e.rotateRight 18
  let v3022 := v3020 ^^^ v3021
  let v3023 := s.e.rotateRight 41
  let v3024 := v3022 ^^^ v3023
  let v3025 := s.e &&& s.f
  let v3026 := s.e ^^^ (-1 : Word)
  let v3027 := s.g &&& v3026
  let v3028 := v3025 ||| v3027
  let v3029 := k
  let v3030 := v3019 + v3029
  let v3031 := v3030 + s.h
  let v3032 := v3031 + v3028
  let v3033 := v3032 + v3024
  let v3034 := s.a.rotateRight 28
  let v3035 := s.a.rotateRight 34
  let v3036 := v3034 ^^^ v3035
  let v3037 := s.a.rotateRight 39
  let v3038 := v3036 ^^^ v3037
  let v3039 := s.a &&& s.b
  let v3040 := s.b ^^^ s.c
  let v3041 := s.a &&& v3040
  let v3042 := v3041 ^^^ (s.b &&& s.c)
  let v3043 := v3038 + v3042
  let v3044 := v3033 + s.d
  let v3045 := v3043 + v3033
  ⟨v3045, s.a, s.b, s.c, v3044, s.e, s.f, s.g⟩

theorem fullOut76_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut76 s w k = Spec.round s (w 76) k := by
  have hw76 := hw 76 (by decide) (by decide)
  dsimp only [fullOut76, Spec.round]
  rw [hw76]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv76_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 3007 E (fullEnv76 E s w k) := by
  unfold fullEnv76
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv76_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv76 E s w k) := by
  exact (fullEnv76_before E s w k).frame (by decide)

theorem full_body76 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready76 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 608#64) 64)
    (hk : state.mem.readAt (kp.add 608#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2807 |>.take 39) state =
      .value (fullEnv76 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv76, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w60, h.w61, h.w62, h.w63, h.w64, h.w69, h.w70, h.w71, h.w72, h.w74, h.w75, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k76, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready76 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready76 E s w) (hw : ScheduleReady w) :
    Ready77 (fullEnv76 E s w k) (Spec.round s (w 76) k) w := by
  have hb := fullEnv76_before E s w k
  have hout := fullOut76_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv76, fullOut76, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 3006 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2967 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2928 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv76, fullOut76, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 3005 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2966 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2927 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv76, Spec.round, mlir_env]
  · rw [hb.read_val 2434 (by decide) (by rfl)]; exact h.w61
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · rw [hb.read_val 2785 (by decide) (by rfl)]; exact h.w70
  · rw [hb.read_val 2824 (by decide) (by rfl)]; exact h.w71
  · rw [hb.read_val 2863 (by decide) (by rfl)]; exact h.w72
  · rw [hb.read_val 2980 (by decide) (by rfl)]; exact h.w75
  · have hwr := hw 76 (by decide) (by decide)
    simp [fullEnv76, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step76 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready76 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2807 |>.take 39) state =
      .value (E', state) ∧
      Ready77 E' (Spec.round s (w 76) (constants.toList.getD 76 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 76 0
  have hf := fullEnv76_frame E s w k
  refine ⟨fullEnv76 E s w k,
    full_body76 E state s w kp k h hc (hk 76).1 (hk 76).2,
    full_ready76 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
