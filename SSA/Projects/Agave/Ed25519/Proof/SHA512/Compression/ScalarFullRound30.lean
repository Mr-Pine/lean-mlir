import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1013..1051: round 30. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv30 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1213 := (w 15).rotateRight 1
  let v1214 := (w 15).rotateRight 8
  let v1215 := v1213 ^^^ v1214
  let v1216 := (w 15) >>> 7
  let v1217 := v1215 ^^^ v1216
  let v1218 := (w 28).rotateRight 19
  let v1219 := (w 28).rotateRight 61
  let v1220 := v1218 ^^^ v1219
  let v1221 := (w 28) >>> 6
  let v1222 := v1220 ^^^ v1221
  let v1223 := v1217 + (w 14)
  let v1224 := v1223 + (w 23)
  let v1225 := v1224 + v1222
  let v1226 := s.e.rotateRight 14
  let v1227 := s.e.rotateRight 18
  let v1228 := v1226 ^^^ v1227
  let v1229 := s.e.rotateRight 41
  let v1230 := v1228 ^^^ v1229
  let v1231 := s.e &&& s.f
  let v1232 := s.e ^^^ (-1 : Word)
  let v1233 := s.g &&& v1232
  let v1234 := v1231 ||| v1233
  let v1235 := k
  let v1236 := v1225 + v1235
  let v1237 := v1236 + s.h
  let v1238 := v1237 + v1234
  let v1239 := v1238 + v1230
  let v1240 := s.a.rotateRight 28
  let v1241 := s.a.rotateRight 34
  let v1242 := v1240 ^^^ v1241
  let v1243 := s.a.rotateRight 39
  let v1244 := v1242 ^^^ v1243
  let v1245 := s.a &&& s.b
  let v1246 := s.b ^^^ s.c
  let v1247 := s.a &&& v1246
  let v1248 := v1247 ^^^ (s.b &&& s.c)
  let v1249 := v1244 + v1248
  let v1250 := v1239 + s.d
  let v1251 := v1249 + v1239
  E[%1213 := .value v1213,
    %1214 := .value v1214,
    %1215 := .value v1215,
    %1216 := .value v1216,
    %1217 := .value v1217,
    %1218 := .value v1218,
    %1219 := .value v1219,
    %1220 := .value v1220,
    %1221 := .value v1221,
    %1222 := .value v1222,
    %1223 := .value v1223,
    %1224 := .value v1224,
    %1225 := .value v1225,
    %1226 := .value v1226,
    %1227 := .value v1227,
    %1228 := .value v1228,
    %1229 := .value v1229,
    %1230 := .value v1230,
    %1231 := .value v1231,
    %1232 := .value v1232,
    %1233 := .value v1233,
    %1234 := .value v1234,
    %1235 := .value v1235,
    %1236 := .value v1236,
    %1237 := .value v1237,
    %1238 := .value v1238,
    %1239 := .value v1239,
    %1240 := .value v1240,
    %1241 := .value v1241,
    %1242 := .value v1242,
    %1243 := .value v1243,
    %1244 := .value v1244,
    %1245 := .value v1245,
    %1246 := .value v1246,
    %1247 := .value v1247,
    %1248 := .value v1248,
    %1249 := .value v1249,
    %1250 := .value v1250,
    %1251 := .value v1251]

def fullOut30 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1213 := (w 15).rotateRight 1
  let v1214 := (w 15).rotateRight 8
  let v1215 := v1213 ^^^ v1214
  let v1216 := (w 15) >>> 7
  let v1217 := v1215 ^^^ v1216
  let v1218 := (w 28).rotateRight 19
  let v1219 := (w 28).rotateRight 61
  let v1220 := v1218 ^^^ v1219
  let v1221 := (w 28) >>> 6
  let v1222 := v1220 ^^^ v1221
  let v1223 := v1217 + (w 14)
  let v1224 := v1223 + (w 23)
  let v1225 := v1224 + v1222
  let v1226 := s.e.rotateRight 14
  let v1227 := s.e.rotateRight 18
  let v1228 := v1226 ^^^ v1227
  let v1229 := s.e.rotateRight 41
  let v1230 := v1228 ^^^ v1229
  let v1231 := s.e &&& s.f
  let v1232 := s.e ^^^ (-1 : Word)
  let v1233 := s.g &&& v1232
  let v1234 := v1231 ||| v1233
  let v1235 := k
  let v1236 := v1225 + v1235
  let v1237 := v1236 + s.h
  let v1238 := v1237 + v1234
  let v1239 := v1238 + v1230
  let v1240 := s.a.rotateRight 28
  let v1241 := s.a.rotateRight 34
  let v1242 := v1240 ^^^ v1241
  let v1243 := s.a.rotateRight 39
  let v1244 := v1242 ^^^ v1243
  let v1245 := s.a &&& s.b
  let v1246 := s.b ^^^ s.c
  let v1247 := s.a &&& v1246
  let v1248 := v1247 ^^^ (s.b &&& s.c)
  let v1249 := v1244 + v1248
  let v1250 := v1239 + s.d
  let v1251 := v1249 + v1239
  ⟨v1251, s.a, s.b, s.c, v1250, s.e, s.f, s.g⟩

theorem fullOut30_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut30 s w k = Spec.round s (w 30) k := by
  have hw30 := hw 30 (by decide) (by decide)
  dsimp only [fullOut30, Spec.round]
  rw [hw30]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv30_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1213 E (fullEnv30 E s w k) := by
  unfold fullEnv30
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv30_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv30 E s w k) := by
  exact (fullEnv30_before E s w k).frame (by decide)

theorem full_body30 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready30 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 240#64) 64)
    (hk : state.mem.readAt (kp.add 240#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1013 |>.take 39) state =
      .value (fullEnv30 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv30, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k30, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready30 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready30 E s w) (hw : ScheduleReady w) :
    Ready31 (fullEnv30 E s w k) (Spec.round s (w 30) k) w := by
  have hb := fullEnv30_before E s w k
  have hout := fullOut30_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv30, fullOut30, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1212 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1173 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1134 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv30, fullOut30, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1211 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1172 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1133 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv30, Spec.round, mlir_env]
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
  · rw [hb.read_val 1186 (by decide) (by rfl)]; exact h.w29
  · have hwr := hw 30 (by decide) (by decide)
    simp [fullEnv30, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step30 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready30 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1013 |>.take 39) state =
      .value (E', state) ∧
      Ready31 E' (Spec.round s (w 30) (constants.toList.getD 30 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 30 0
  have hf := fullEnv30_frame E s w k
  refine ⟨fullEnv30 E s w k,
    full_body30 E state s w kp k h hc (hk 30).1 (hk 30).2,
    full_ready30 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
