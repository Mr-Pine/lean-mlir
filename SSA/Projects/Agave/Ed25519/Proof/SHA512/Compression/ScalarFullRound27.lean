import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 896..934: round 27. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv27 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1096 := (w 12).rotateRight 1
  let v1097 := (w 12).rotateRight 8
  let v1098 := v1096 ^^^ v1097
  let v1099 := (w 12) >>> 7
  let v1100 := v1098 ^^^ v1099
  let v1101 := (w 25).rotateRight 19
  let v1102 := (w 25).rotateRight 61
  let v1103 := v1101 ^^^ v1102
  let v1104 := (w 25) >>> 6
  let v1105 := v1103 ^^^ v1104
  let v1106 := v1100 + (w 11)
  let v1107 := v1106 + (w 20)
  let v1108 := v1107 + v1105
  let v1109 := s.e.rotateRight 14
  let v1110 := s.e.rotateRight 18
  let v1111 := v1109 ^^^ v1110
  let v1112 := s.e.rotateRight 41
  let v1113 := v1111 ^^^ v1112
  let v1114 := s.e &&& s.f
  let v1115 := s.e ^^^ (-1 : Word)
  let v1116 := s.g &&& v1115
  let v1117 := v1114 ||| v1116
  let v1118 := k
  let v1119 := v1118 + v1108
  let v1120 := v1119 + s.h
  let v1121 := v1120 + v1117
  let v1122 := v1121 + v1113
  let v1123 := s.a.rotateRight 28
  let v1124 := s.a.rotateRight 34
  let v1125 := v1123 ^^^ v1124
  let v1126 := s.a.rotateRight 39
  let v1127 := v1125 ^^^ v1126
  let v1128 := s.a &&& s.b
  let v1129 := s.b ^^^ s.c
  let v1130 := s.a &&& v1129
  let v1131 := v1130 ^^^ (s.b &&& s.c)
  let v1132 := v1127 + v1131
  let v1133 := v1122 + s.d
  let v1134 := v1132 + v1122
  E[%1096 := .value v1096,
    %1097 := .value v1097,
    %1098 := .value v1098,
    %1099 := .value v1099,
    %1100 := .value v1100,
    %1101 := .value v1101,
    %1102 := .value v1102,
    %1103 := .value v1103,
    %1104 := .value v1104,
    %1105 := .value v1105,
    %1106 := .value v1106,
    %1107 := .value v1107,
    %1108 := .value v1108,
    %1109 := .value v1109,
    %1110 := .value v1110,
    %1111 := .value v1111,
    %1112 := .value v1112,
    %1113 := .value v1113,
    %1114 := .value v1114,
    %1115 := .value v1115,
    %1116 := .value v1116,
    %1117 := .value v1117,
    %1118 := .value v1118,
    %1119 := .value v1119,
    %1120 := .value v1120,
    %1121 := .value v1121,
    %1122 := .value v1122,
    %1123 := .value v1123,
    %1124 := .value v1124,
    %1125 := .value v1125,
    %1126 := .value v1126,
    %1127 := .value v1127,
    %1128 := .value v1128,
    %1129 := .value v1129,
    %1130 := .value v1130,
    %1131 := .value v1131,
    %1132 := .value v1132,
    %1133 := .value v1133,
    %1134 := .value v1134]

def fullOut27 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1096 := (w 12).rotateRight 1
  let v1097 := (w 12).rotateRight 8
  let v1098 := v1096 ^^^ v1097
  let v1099 := (w 12) >>> 7
  let v1100 := v1098 ^^^ v1099
  let v1101 := (w 25).rotateRight 19
  let v1102 := (w 25).rotateRight 61
  let v1103 := v1101 ^^^ v1102
  let v1104 := (w 25) >>> 6
  let v1105 := v1103 ^^^ v1104
  let v1106 := v1100 + (w 11)
  let v1107 := v1106 + (w 20)
  let v1108 := v1107 + v1105
  let v1109 := s.e.rotateRight 14
  let v1110 := s.e.rotateRight 18
  let v1111 := v1109 ^^^ v1110
  let v1112 := s.e.rotateRight 41
  let v1113 := v1111 ^^^ v1112
  let v1114 := s.e &&& s.f
  let v1115 := s.e ^^^ (-1 : Word)
  let v1116 := s.g &&& v1115
  let v1117 := v1114 ||| v1116
  let v1118 := k
  let v1119 := v1118 + v1108
  let v1120 := v1119 + s.h
  let v1121 := v1120 + v1117
  let v1122 := v1121 + v1113
  let v1123 := s.a.rotateRight 28
  let v1124 := s.a.rotateRight 34
  let v1125 := v1123 ^^^ v1124
  let v1126 := s.a.rotateRight 39
  let v1127 := v1125 ^^^ v1126
  let v1128 := s.a &&& s.b
  let v1129 := s.b ^^^ s.c
  let v1130 := s.a &&& v1129
  let v1131 := v1130 ^^^ (s.b &&& s.c)
  let v1132 := v1127 + v1131
  let v1133 := v1122 + s.d
  let v1134 := v1132 + v1122
  ⟨v1134, s.a, s.b, s.c, v1133, s.e, s.f, s.g⟩

theorem fullOut27_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut27 s w k = Spec.round s (w 27) k := by
  have hw27 := hw 27 (by decide) (by decide)
  dsimp only [fullOut27, Spec.round]
  rw [hw27]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv27_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1096 E (fullEnv27 E s w k) := by
  unfold fullEnv27
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv27_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv27 E s w k) := by
  exact (fullEnv27_before E s w k).frame (by decide)

theorem full_body27 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready27 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 216#64) 64)
    (hk : state.mem.readAt (kp.add 216#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 896 |>.take 39) state =
      .value (fullEnv27 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv27, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k27, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready27 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready27 E s w) (hw : ScheduleReady w) :
    Ready28 (fullEnv27 E s w k) (Spec.round s (w 27) k) w := by
  have hb := fullEnv27_before E s w k
  have hout := fullOut27_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv27, fullOut27, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1095 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1056 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1017 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv27, fullOut27, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1094 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1055 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1016 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv27, Spec.round, mlir_env]
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
  · rw [hb.read_val 1069 (by decide) (by rfl)]; exact h.w26
  · have hwr := hw 27 (by decide) (by decide)
    simp [fullEnv27, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step27 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready27 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 896 |>.take 39) state =
      .value (E', state) ∧
      Ready28 E' (Spec.round s (w 27) (constants.toList.getD 27 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 27 0
  have hf := fullEnv27_frame E s w k
  refine ⟨fullEnv27 E s w k,
    full_body27 E state s w kp k h hc (hk 27).1 (hk 27).2,
    full_ready27 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
