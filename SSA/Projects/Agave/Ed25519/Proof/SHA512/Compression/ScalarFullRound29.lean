import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 974..1012: round 29. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv29 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1174 := (w 14).rotateRight 1
  let v1175 := (w 14).rotateRight 8
  let v1176 := v1174 ^^^ v1175
  let v1177 := (w 14) >>> 7
  let v1178 := v1176 ^^^ v1177
  let v1179 := (w 27).rotateRight 19
  let v1180 := (w 27).rotateRight 61
  let v1181 := v1179 ^^^ v1180
  let v1182 := (w 27) >>> 6
  let v1183 := v1181 ^^^ v1182
  let v1184 := v1178 + (w 13)
  let v1185 := v1184 + (w 22)
  let v1186 := v1185 + v1183
  let v1187 := s.e.rotateRight 14
  let v1188 := s.e.rotateRight 18
  let v1189 := v1187 ^^^ v1188
  let v1190 := s.e.rotateRight 41
  let v1191 := v1189 ^^^ v1190
  let v1192 := s.e &&& s.f
  let v1193 := s.e ^^^ (-1 : Word)
  let v1194 := s.g &&& v1193
  let v1195 := v1192 ||| v1194
  let v1196 := k
  let v1197 := v1196 + v1186
  let v1198 := v1197 + s.h
  let v1199 := v1198 + v1195
  let v1200 := v1199 + v1191
  let v1201 := s.a.rotateRight 28
  let v1202 := s.a.rotateRight 34
  let v1203 := v1201 ^^^ v1202
  let v1204 := s.a.rotateRight 39
  let v1205 := v1203 ^^^ v1204
  let v1206 := s.a &&& s.b
  let v1207 := s.b ^^^ s.c
  let v1208 := s.a &&& v1207
  let v1209 := v1208 ^^^ (s.b &&& s.c)
  let v1210 := v1205 + v1209
  let v1211 := v1200 + s.d
  let v1212 := v1210 + v1200
  E[%1174 := .value v1174,
    %1175 := .value v1175,
    %1176 := .value v1176,
    %1177 := .value v1177,
    %1178 := .value v1178,
    %1179 := .value v1179,
    %1180 := .value v1180,
    %1181 := .value v1181,
    %1182 := .value v1182,
    %1183 := .value v1183,
    %1184 := .value v1184,
    %1185 := .value v1185,
    %1186 := .value v1186,
    %1187 := .value v1187,
    %1188 := .value v1188,
    %1189 := .value v1189,
    %1190 := .value v1190,
    %1191 := .value v1191,
    %1192 := .value v1192,
    %1193 := .value v1193,
    %1194 := .value v1194,
    %1195 := .value v1195,
    %1196 := .value v1196,
    %1197 := .value v1197,
    %1198 := .value v1198,
    %1199 := .value v1199,
    %1200 := .value v1200,
    %1201 := .value v1201,
    %1202 := .value v1202,
    %1203 := .value v1203,
    %1204 := .value v1204,
    %1205 := .value v1205,
    %1206 := .value v1206,
    %1207 := .value v1207,
    %1208 := .value v1208,
    %1209 := .value v1209,
    %1210 := .value v1210,
    %1211 := .value v1211,
    %1212 := .value v1212]

def fullOut29 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1174 := (w 14).rotateRight 1
  let v1175 := (w 14).rotateRight 8
  let v1176 := v1174 ^^^ v1175
  let v1177 := (w 14) >>> 7
  let v1178 := v1176 ^^^ v1177
  let v1179 := (w 27).rotateRight 19
  let v1180 := (w 27).rotateRight 61
  let v1181 := v1179 ^^^ v1180
  let v1182 := (w 27) >>> 6
  let v1183 := v1181 ^^^ v1182
  let v1184 := v1178 + (w 13)
  let v1185 := v1184 + (w 22)
  let v1186 := v1185 + v1183
  let v1187 := s.e.rotateRight 14
  let v1188 := s.e.rotateRight 18
  let v1189 := v1187 ^^^ v1188
  let v1190 := s.e.rotateRight 41
  let v1191 := v1189 ^^^ v1190
  let v1192 := s.e &&& s.f
  let v1193 := s.e ^^^ (-1 : Word)
  let v1194 := s.g &&& v1193
  let v1195 := v1192 ||| v1194
  let v1196 := k
  let v1197 := v1196 + v1186
  let v1198 := v1197 + s.h
  let v1199 := v1198 + v1195
  let v1200 := v1199 + v1191
  let v1201 := s.a.rotateRight 28
  let v1202 := s.a.rotateRight 34
  let v1203 := v1201 ^^^ v1202
  let v1204 := s.a.rotateRight 39
  let v1205 := v1203 ^^^ v1204
  let v1206 := s.a &&& s.b
  let v1207 := s.b ^^^ s.c
  let v1208 := s.a &&& v1207
  let v1209 := v1208 ^^^ (s.b &&& s.c)
  let v1210 := v1205 + v1209
  let v1211 := v1200 + s.d
  let v1212 := v1210 + v1200
  ⟨v1212, s.a, s.b, s.c, v1211, s.e, s.f, s.g⟩

theorem fullOut29_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut29 s w k = Spec.round s (w 29) k := by
  have hw29 := hw 29 (by decide) (by decide)
  dsimp only [fullOut29, Spec.round]
  rw [hw29]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv29_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1174 E (fullEnv29 E s w k) := by
  unfold fullEnv29
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv29_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv29 E s w k) := by
  exact (fullEnv29_before E s w k).frame (by decide)

theorem full_body29 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready29 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 232#64) 64)
    (hk : state.mem.readAt (kp.add 232#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 974 |>.take 39) state =
      .value (fullEnv29 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv29, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k29, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready29 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready29 E s w) (hw : ScheduleReady w) :
    Ready30 (fullEnv29 E s w k) (Spec.round s (w 29) k) w := by
  have hb := fullEnv29_before E s w k
  have hout := fullOut29_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv29, fullOut29, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1173 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1134 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1095 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv29, fullOut29, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1172 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1133 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1094 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv29, Spec.round, mlir_env]
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
  · rw [hb.read_val 1147 (by decide) (by rfl)]; exact h.w28
  · have hwr := hw 29 (by decide) (by decide)
    simp [fullEnv29, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step29 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready29 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 974 |>.take 39) state =
      .value (E', state) ∧
      Ready30 E' (Spec.round s (w 29) (constants.toList.getD 29 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 29 0
  have hf := fullEnv29_frame E s w k
  refine ⟨fullEnv29 E s w k,
    full_body29 E state s w kp k h hc (hk 29).1 (hk 29).2,
    full_ready29 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
