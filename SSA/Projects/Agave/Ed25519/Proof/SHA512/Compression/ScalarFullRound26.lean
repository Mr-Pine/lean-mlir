import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 857..895: round 26. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv26 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1057 := (w 11).rotateRight 1
  let v1058 := (w 11).rotateRight 8
  let v1059 := v1057 ^^^ v1058
  let v1060 := (w 11) >>> 7
  let v1061 := v1059 ^^^ v1060
  let v1062 := (w 24).rotateRight 19
  let v1063 := (w 24).rotateRight 61
  let v1064 := v1062 ^^^ v1063
  let v1065 := (w 24) >>> 6
  let v1066 := v1064 ^^^ v1065
  let v1067 := v1061 + (w 10)
  let v1068 := v1067 + (w 19)
  let v1069 := v1068 + v1066
  let v1070 := s.e.rotateRight 14
  let v1071 := s.e.rotateRight 18
  let v1072 := v1070 ^^^ v1071
  let v1073 := s.e.rotateRight 41
  let v1074 := v1072 ^^^ v1073
  let v1075 := s.e &&& s.f
  let v1076 := s.e ^^^ (-1 : Word)
  let v1077 := s.g &&& v1076
  let v1078 := v1075 ||| v1077
  let v1079 := k
  let v1080 := v1079 + v1069
  let v1081 := v1080 + s.h
  let v1082 := v1081 + v1078
  let v1083 := v1082 + v1074
  let v1084 := s.a.rotateRight 28
  let v1085 := s.a.rotateRight 34
  let v1086 := v1084 ^^^ v1085
  let v1087 := s.a.rotateRight 39
  let v1088 := v1086 ^^^ v1087
  let v1089 := s.a &&& s.b
  let v1090 := s.b ^^^ s.c
  let v1091 := s.a &&& v1090
  let v1092 := v1091 ^^^ (s.b &&& s.c)
  let v1093 := v1088 + v1092
  let v1094 := v1083 + s.d
  let v1095 := v1093 + v1083
  E[%1057 := .value v1057,
    %1058 := .value v1058,
    %1059 := .value v1059,
    %1060 := .value v1060,
    %1061 := .value v1061,
    %1062 := .value v1062,
    %1063 := .value v1063,
    %1064 := .value v1064,
    %1065 := .value v1065,
    %1066 := .value v1066,
    %1067 := .value v1067,
    %1068 := .value v1068,
    %1069 := .value v1069,
    %1070 := .value v1070,
    %1071 := .value v1071,
    %1072 := .value v1072,
    %1073 := .value v1073,
    %1074 := .value v1074,
    %1075 := .value v1075,
    %1076 := .value v1076,
    %1077 := .value v1077,
    %1078 := .value v1078,
    %1079 := .value v1079,
    %1080 := .value v1080,
    %1081 := .value v1081,
    %1082 := .value v1082,
    %1083 := .value v1083,
    %1084 := .value v1084,
    %1085 := .value v1085,
    %1086 := .value v1086,
    %1087 := .value v1087,
    %1088 := .value v1088,
    %1089 := .value v1089,
    %1090 := .value v1090,
    %1091 := .value v1091,
    %1092 := .value v1092,
    %1093 := .value v1093,
    %1094 := .value v1094,
    %1095 := .value v1095]

def fullOut26 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1057 := (w 11).rotateRight 1
  let v1058 := (w 11).rotateRight 8
  let v1059 := v1057 ^^^ v1058
  let v1060 := (w 11) >>> 7
  let v1061 := v1059 ^^^ v1060
  let v1062 := (w 24).rotateRight 19
  let v1063 := (w 24).rotateRight 61
  let v1064 := v1062 ^^^ v1063
  let v1065 := (w 24) >>> 6
  let v1066 := v1064 ^^^ v1065
  let v1067 := v1061 + (w 10)
  let v1068 := v1067 + (w 19)
  let v1069 := v1068 + v1066
  let v1070 := s.e.rotateRight 14
  let v1071 := s.e.rotateRight 18
  let v1072 := v1070 ^^^ v1071
  let v1073 := s.e.rotateRight 41
  let v1074 := v1072 ^^^ v1073
  let v1075 := s.e &&& s.f
  let v1076 := s.e ^^^ (-1 : Word)
  let v1077 := s.g &&& v1076
  let v1078 := v1075 ||| v1077
  let v1079 := k
  let v1080 := v1079 + v1069
  let v1081 := v1080 + s.h
  let v1082 := v1081 + v1078
  let v1083 := v1082 + v1074
  let v1084 := s.a.rotateRight 28
  let v1085 := s.a.rotateRight 34
  let v1086 := v1084 ^^^ v1085
  let v1087 := s.a.rotateRight 39
  let v1088 := v1086 ^^^ v1087
  let v1089 := s.a &&& s.b
  let v1090 := s.b ^^^ s.c
  let v1091 := s.a &&& v1090
  let v1092 := v1091 ^^^ (s.b &&& s.c)
  let v1093 := v1088 + v1092
  let v1094 := v1083 + s.d
  let v1095 := v1093 + v1083
  ⟨v1095, s.a, s.b, s.c, v1094, s.e, s.f, s.g⟩

theorem fullOut26_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut26 s w k = Spec.round s (w 26) k := by
  have hw26 := hw 26 (by decide) (by decide)
  dsimp only [fullOut26, Spec.round]
  rw [hw26]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv26_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1057 E (fullEnv26 E s w k) := by
  unfold fullEnv26
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv26_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv26 E s w k) := by
  exact (fullEnv26_before E s w k).frame (by decide)

theorem full_body26 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready26 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 208#64) 64)
    (hk : state.mem.readAt (kp.add 208#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 857 |>.take 39) state =
      .value (fullEnv26 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv26, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k26, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready26 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready26 E s w) (hw : ScheduleReady w) :
    Ready27 (fullEnv26 E s w k) (Spec.round s (w 26) k) w := by
  have hb := fullEnv26_before E s w k
  have hout := fullOut26_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv26, fullOut26, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1056 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1017 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 978 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv26, fullOut26, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1055 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1016 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 977 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv26, Spec.round, mlir_env]
  · rw [hb.read_val 237 (by decide) (by rfl)]; exact h.w11
  · rw [hb.read_val 240 (by decide) (by rfl)]; exact h.w12
  · rw [hb.read_val 243 (by decide) (by rfl)]; exact h.w13
  · rw [hb.read_val 246 (by decide) (by rfl)]; exact h.w14
  · rw [hb.read_val 249 (by decide) (by rfl)]; exact h.w15
  · rw [hb.read_val 679 (by decide) (by rfl)]; exact h.w16
  · rw [hb.read_val 718 (by decide) (by rfl)]; exact h.w17
  · rw [hb.read_val 757 (by decide) (by rfl)]; exact h.w18
  · rw [hb.read_val 796 (by decide) (by rfl)]; exact h.w19
  · rw [hb.read_val 835 (by decide) (by rfl)]; exact h.w20
  · rw [hb.read_val 874 (by decide) (by rfl)]; exact h.w21
  · rw [hb.read_val 913 (by decide) (by rfl)]; exact h.w22
  · rw [hb.read_val 952 (by decide) (by rfl)]; exact h.w23
  · rw [hb.read_val 991 (by decide) (by rfl)]; exact h.w24
  · rw [hb.read_val 1030 (by decide) (by rfl)]; exact h.w25
  · have hwr := hw 26 (by decide) (by decide)
    simp [fullEnv26, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step26 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready26 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 857 |>.take 39) state =
      .value (E', state) ∧
      Ready27 E' (Spec.round s (w 26) (constants.toList.getD 26 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 26 0
  have hf := fullEnv26_frame E s w k
  refine ⟨fullEnv26 E s w k,
    full_body26 E state s w kp k h hc (hk 26).1 (hk 26).2,
    full_ready26 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
