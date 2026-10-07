import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 935..973: round 28. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv28 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1135 := (w 13).rotateRight 1
  let v1136 := (w 13).rotateRight 8
  let v1137 := v1135 ^^^ v1136
  let v1138 := (w 13) >>> 7
  let v1139 := v1137 ^^^ v1138
  let v1140 := (w 26).rotateRight 19
  let v1141 := (w 26).rotateRight 61
  let v1142 := v1140 ^^^ v1141
  let v1143 := (w 26) >>> 6
  let v1144 := v1142 ^^^ v1143
  let v1145 := v1139 + (w 12)
  let v1146 := v1145 + (w 21)
  let v1147 := v1146 + v1144
  let v1148 := s.e.rotateRight 14
  let v1149 := s.e.rotateRight 18
  let v1150 := v1148 ^^^ v1149
  let v1151 := s.e.rotateRight 41
  let v1152 := v1150 ^^^ v1151
  let v1153 := s.e &&& s.f
  let v1154 := s.e ^^^ (-1 : Word)
  let v1155 := s.g &&& v1154
  let v1156 := v1153 ||| v1155
  let v1157 := k
  let v1158 := v1157 + v1147
  let v1159 := v1158 + s.h
  let v1160 := v1159 + v1156
  let v1161 := v1160 + v1152
  let v1162 := s.a.rotateRight 28
  let v1163 := s.a.rotateRight 34
  let v1164 := v1162 ^^^ v1163
  let v1165 := s.a.rotateRight 39
  let v1166 := v1164 ^^^ v1165
  let v1167 := s.a &&& s.b
  let v1168 := s.b ^^^ s.c
  let v1169 := s.a &&& v1168
  let v1170 := v1169 ^^^ (s.b &&& s.c)
  let v1171 := v1166 + v1170
  let v1172 := v1161 + s.d
  let v1173 := v1171 + v1161
  E[%1135 := .value v1135,
    %1136 := .value v1136,
    %1137 := .value v1137,
    %1138 := .value v1138,
    %1139 := .value v1139,
    %1140 := .value v1140,
    %1141 := .value v1141,
    %1142 := .value v1142,
    %1143 := .value v1143,
    %1144 := .value v1144,
    %1145 := .value v1145,
    %1146 := .value v1146,
    %1147 := .value v1147,
    %1148 := .value v1148,
    %1149 := .value v1149,
    %1150 := .value v1150,
    %1151 := .value v1151,
    %1152 := .value v1152,
    %1153 := .value v1153,
    %1154 := .value v1154,
    %1155 := .value v1155,
    %1156 := .value v1156,
    %1157 := .value v1157,
    %1158 := .value v1158,
    %1159 := .value v1159,
    %1160 := .value v1160,
    %1161 := .value v1161,
    %1162 := .value v1162,
    %1163 := .value v1163,
    %1164 := .value v1164,
    %1165 := .value v1165,
    %1166 := .value v1166,
    %1167 := .value v1167,
    %1168 := .value v1168,
    %1169 := .value v1169,
    %1170 := .value v1170,
    %1171 := .value v1171,
    %1172 := .value v1172,
    %1173 := .value v1173]

def fullOut28 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1135 := (w 13).rotateRight 1
  let v1136 := (w 13).rotateRight 8
  let v1137 := v1135 ^^^ v1136
  let v1138 := (w 13) >>> 7
  let v1139 := v1137 ^^^ v1138
  let v1140 := (w 26).rotateRight 19
  let v1141 := (w 26).rotateRight 61
  let v1142 := v1140 ^^^ v1141
  let v1143 := (w 26) >>> 6
  let v1144 := v1142 ^^^ v1143
  let v1145 := v1139 + (w 12)
  let v1146 := v1145 + (w 21)
  let v1147 := v1146 + v1144
  let v1148 := s.e.rotateRight 14
  let v1149 := s.e.rotateRight 18
  let v1150 := v1148 ^^^ v1149
  let v1151 := s.e.rotateRight 41
  let v1152 := v1150 ^^^ v1151
  let v1153 := s.e &&& s.f
  let v1154 := s.e ^^^ (-1 : Word)
  let v1155 := s.g &&& v1154
  let v1156 := v1153 ||| v1155
  let v1157 := k
  let v1158 := v1157 + v1147
  let v1159 := v1158 + s.h
  let v1160 := v1159 + v1156
  let v1161 := v1160 + v1152
  let v1162 := s.a.rotateRight 28
  let v1163 := s.a.rotateRight 34
  let v1164 := v1162 ^^^ v1163
  let v1165 := s.a.rotateRight 39
  let v1166 := v1164 ^^^ v1165
  let v1167 := s.a &&& s.b
  let v1168 := s.b ^^^ s.c
  let v1169 := s.a &&& v1168
  let v1170 := v1169 ^^^ (s.b &&& s.c)
  let v1171 := v1166 + v1170
  let v1172 := v1161 + s.d
  let v1173 := v1171 + v1161
  ⟨v1173, s.a, s.b, s.c, v1172, s.e, s.f, s.g⟩

theorem fullOut28_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut28 s w k = Spec.round s (w 28) k := by
  have hw28 := hw 28 (by decide) (by decide)
  dsimp only [fullOut28, Spec.round]
  rw [hw28]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv28_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1135 E (fullEnv28 E s w k) := by
  unfold fullEnv28
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv28_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv28 E s w k) := by
  exact (fullEnv28_before E s w k).frame (by decide)

theorem full_body28 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready28 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 224#64) 64)
    (hk : state.mem.readAt (kp.add 224#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 935 |>.take 39) state =
      .value (fullEnv28 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv28, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k28, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready28 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready28 E s w) (hw : ScheduleReady w) :
    Ready29 (fullEnv28 E s w k) (Spec.round s (w 28) k) w := by
  have hb := fullEnv28_before E s w k
  have hout := fullOut28_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv28, fullOut28, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1134 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1095 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1056 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv28, fullOut28, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1133 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1094 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1055 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv28, Spec.round, mlir_env]
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
  · rw [hb.read_val 1108 (by decide) (by rfl)]; exact h.w27
  · have hwr := hw 28 (by decide) (by decide)
    simp [fullEnv28, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step28 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready28 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 935 |>.take 39) state =
      .value (E', state) ∧
      Ready29 E' (Spec.round s (w 28) (constants.toList.getD 28 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 28 0
  have hf := fullEnv28_frame E s w k
  refine ⟨fullEnv28 E s w k,
    full_body28 E state s w kp k h hc (hk 28).1 (hk 28).2,
    full_ready28 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
