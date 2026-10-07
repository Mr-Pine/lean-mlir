import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1052..1090: round 31. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv31 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1252 := (w 16).rotateRight 1
  let v1253 := (w 16).rotateRight 8
  let v1254 := v1252 ^^^ v1253
  let v1255 := (w 16) >>> 7
  let v1256 := v1254 ^^^ v1255
  let v1257 := (w 29).rotateRight 19
  let v1258 := (w 29).rotateRight 61
  let v1259 := v1257 ^^^ v1258
  let v1260 := (w 29) >>> 6
  let v1261 := v1259 ^^^ v1260
  let v1262 := v1256 + (w 15)
  let v1263 := v1262 + (w 24)
  let v1264 := v1263 + v1261
  let v1265 := s.e.rotateRight 14
  let v1266 := s.e.rotateRight 18
  let v1267 := v1265 ^^^ v1266
  let v1268 := s.e.rotateRight 41
  let v1269 := v1267 ^^^ v1268
  let v1270 := s.e &&& s.f
  let v1271 := s.e ^^^ (-1 : Word)
  let v1272 := s.g &&& v1271
  let v1273 := v1270 ||| v1272
  let v1274 := k
  let v1275 := v1264 + v1274
  let v1276 := v1275 + s.h
  let v1277 := v1276 + v1273
  let v1278 := v1277 + v1269
  let v1279 := s.a.rotateRight 28
  let v1280 := s.a.rotateRight 34
  let v1281 := v1279 ^^^ v1280
  let v1282 := s.a.rotateRight 39
  let v1283 := v1281 ^^^ v1282
  let v1284 := s.a &&& s.b
  let v1285 := s.b ^^^ s.c
  let v1286 := s.a &&& v1285
  let v1287 := v1286 ^^^ (s.b &&& s.c)
  let v1288 := v1283 + v1287
  let v1289 := v1278 + s.d
  let v1290 := v1288 + v1278
  E[%1252 := .value v1252,
    %1253 := .value v1253,
    %1254 := .value v1254,
    %1255 := .value v1255,
    %1256 := .value v1256,
    %1257 := .value v1257,
    %1258 := .value v1258,
    %1259 := .value v1259,
    %1260 := .value v1260,
    %1261 := .value v1261,
    %1262 := .value v1262,
    %1263 := .value v1263,
    %1264 := .value v1264,
    %1265 := .value v1265,
    %1266 := .value v1266,
    %1267 := .value v1267,
    %1268 := .value v1268,
    %1269 := .value v1269,
    %1270 := .value v1270,
    %1271 := .value v1271,
    %1272 := .value v1272,
    %1273 := .value v1273,
    %1274 := .value v1274,
    %1275 := .value v1275,
    %1276 := .value v1276,
    %1277 := .value v1277,
    %1278 := .value v1278,
    %1279 := .value v1279,
    %1280 := .value v1280,
    %1281 := .value v1281,
    %1282 := .value v1282,
    %1283 := .value v1283,
    %1284 := .value v1284,
    %1285 := .value v1285,
    %1286 := .value v1286,
    %1287 := .value v1287,
    %1288 := .value v1288,
    %1289 := .value v1289,
    %1290 := .value v1290]

def fullOut31 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1252 := (w 16).rotateRight 1
  let v1253 := (w 16).rotateRight 8
  let v1254 := v1252 ^^^ v1253
  let v1255 := (w 16) >>> 7
  let v1256 := v1254 ^^^ v1255
  let v1257 := (w 29).rotateRight 19
  let v1258 := (w 29).rotateRight 61
  let v1259 := v1257 ^^^ v1258
  let v1260 := (w 29) >>> 6
  let v1261 := v1259 ^^^ v1260
  let v1262 := v1256 + (w 15)
  let v1263 := v1262 + (w 24)
  let v1264 := v1263 + v1261
  let v1265 := s.e.rotateRight 14
  let v1266 := s.e.rotateRight 18
  let v1267 := v1265 ^^^ v1266
  let v1268 := s.e.rotateRight 41
  let v1269 := v1267 ^^^ v1268
  let v1270 := s.e &&& s.f
  let v1271 := s.e ^^^ (-1 : Word)
  let v1272 := s.g &&& v1271
  let v1273 := v1270 ||| v1272
  let v1274 := k
  let v1275 := v1264 + v1274
  let v1276 := v1275 + s.h
  let v1277 := v1276 + v1273
  let v1278 := v1277 + v1269
  let v1279 := s.a.rotateRight 28
  let v1280 := s.a.rotateRight 34
  let v1281 := v1279 ^^^ v1280
  let v1282 := s.a.rotateRight 39
  let v1283 := v1281 ^^^ v1282
  let v1284 := s.a &&& s.b
  let v1285 := s.b ^^^ s.c
  let v1286 := s.a &&& v1285
  let v1287 := v1286 ^^^ (s.b &&& s.c)
  let v1288 := v1283 + v1287
  let v1289 := v1278 + s.d
  let v1290 := v1288 + v1278
  ⟨v1290, s.a, s.b, s.c, v1289, s.e, s.f, s.g⟩

theorem fullOut31_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut31 s w k = Spec.round s (w 31) k := by
  have hw31 := hw 31 (by decide) (by decide)
  dsimp only [fullOut31, Spec.round]
  rw [hw31]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv31_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1252 E (fullEnv31 E s w k) := by
  unfold fullEnv31
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv31_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv31 E s w k) := by
  exact (fullEnv31_before E s w k).frame (by decide)

theorem full_body31 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready31 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 248#64) 64)
    (hk : state.mem.readAt (kp.add 248#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1052 |>.take 39) state =
      .value (fullEnv31 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv31, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k31, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready31 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready31 E s w) (hw : ScheduleReady w) :
    Ready32 (fullEnv31 E s w k) (Spec.round s (w 31) k) w := by
  have hb := fullEnv31_before E s w k
  have hout := fullOut31_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv31, fullOut31, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1251 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1212 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1173 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv31, fullOut31, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1250 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1211 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1172 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv31, Spec.round, mlir_env]
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
  · rw [hb.read_val 1225 (by decide) (by rfl)]; exact h.w30
  · have hwr := hw 31 (by decide) (by decide)
    simp [fullEnv31, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step31 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready31 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1052 |>.take 39) state =
      .value (E', state) ∧
      Ready32 E' (Spec.round s (w 31) (constants.toList.getD 31 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 31 0
  have hf := fullEnv31_frame E s w k
  refine ⟨fullEnv31 E s w k,
    full_body31 E state s w kp k h hc (hk 31).1 (hk 31).2,
    full_ready31 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
