import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1091..1129: round 32. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv32 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1291 := (w 17).rotateRight 1
  let v1292 := (w 17).rotateRight 8
  let v1293 := v1291 ^^^ v1292
  let v1294 := (w 17) >>> 7
  let v1295 := v1293 ^^^ v1294
  let v1296 := (w 30).rotateRight 19
  let v1297 := (w 30).rotateRight 61
  let v1298 := v1296 ^^^ v1297
  let v1299 := (w 30) >>> 6
  let v1300 := v1298 ^^^ v1299
  let v1301 := v1295 + (w 16)
  let v1302 := v1301 + (w 25)
  let v1303 := v1302 + v1300
  let v1304 := s.e.rotateRight 14
  let v1305 := s.e.rotateRight 18
  let v1306 := v1304 ^^^ v1305
  let v1307 := s.e.rotateRight 41
  let v1308 := v1306 ^^^ v1307
  let v1309 := s.e &&& s.f
  let v1310 := s.e ^^^ (-1 : Word)
  let v1311 := s.g &&& v1310
  let v1312 := v1309 ||| v1311
  let v1313 := k
  let v1314 := v1303 + v1313
  let v1315 := v1314 + s.h
  let v1316 := v1315 + v1312
  let v1317 := v1316 + v1308
  let v1318 := s.a.rotateRight 28
  let v1319 := s.a.rotateRight 34
  let v1320 := v1318 ^^^ v1319
  let v1321 := s.a.rotateRight 39
  let v1322 := v1320 ^^^ v1321
  let v1323 := s.a &&& s.b
  let v1324 := s.b ^^^ s.c
  let v1325 := s.a &&& v1324
  let v1326 := v1325 ^^^ (s.b &&& s.c)
  let v1327 := v1322 + v1326
  let v1328 := v1317 + s.d
  let v1329 := v1327 + v1317
  E[%1291 := .value v1291,
    %1292 := .value v1292,
    %1293 := .value v1293,
    %1294 := .value v1294,
    %1295 := .value v1295,
    %1296 := .value v1296,
    %1297 := .value v1297,
    %1298 := .value v1298,
    %1299 := .value v1299,
    %1300 := .value v1300,
    %1301 := .value v1301,
    %1302 := .value v1302,
    %1303 := .value v1303,
    %1304 := .value v1304,
    %1305 := .value v1305,
    %1306 := .value v1306,
    %1307 := .value v1307,
    %1308 := .value v1308,
    %1309 := .value v1309,
    %1310 := .value v1310,
    %1311 := .value v1311,
    %1312 := .value v1312,
    %1313 := .value v1313,
    %1314 := .value v1314,
    %1315 := .value v1315,
    %1316 := .value v1316,
    %1317 := .value v1317,
    %1318 := .value v1318,
    %1319 := .value v1319,
    %1320 := .value v1320,
    %1321 := .value v1321,
    %1322 := .value v1322,
    %1323 := .value v1323,
    %1324 := .value v1324,
    %1325 := .value v1325,
    %1326 := .value v1326,
    %1327 := .value v1327,
    %1328 := .value v1328,
    %1329 := .value v1329]

def fullOut32 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1291 := (w 17).rotateRight 1
  let v1292 := (w 17).rotateRight 8
  let v1293 := v1291 ^^^ v1292
  let v1294 := (w 17) >>> 7
  let v1295 := v1293 ^^^ v1294
  let v1296 := (w 30).rotateRight 19
  let v1297 := (w 30).rotateRight 61
  let v1298 := v1296 ^^^ v1297
  let v1299 := (w 30) >>> 6
  let v1300 := v1298 ^^^ v1299
  let v1301 := v1295 + (w 16)
  let v1302 := v1301 + (w 25)
  let v1303 := v1302 + v1300
  let v1304 := s.e.rotateRight 14
  let v1305 := s.e.rotateRight 18
  let v1306 := v1304 ^^^ v1305
  let v1307 := s.e.rotateRight 41
  let v1308 := v1306 ^^^ v1307
  let v1309 := s.e &&& s.f
  let v1310 := s.e ^^^ (-1 : Word)
  let v1311 := s.g &&& v1310
  let v1312 := v1309 ||| v1311
  let v1313 := k
  let v1314 := v1303 + v1313
  let v1315 := v1314 + s.h
  let v1316 := v1315 + v1312
  let v1317 := v1316 + v1308
  let v1318 := s.a.rotateRight 28
  let v1319 := s.a.rotateRight 34
  let v1320 := v1318 ^^^ v1319
  let v1321 := s.a.rotateRight 39
  let v1322 := v1320 ^^^ v1321
  let v1323 := s.a &&& s.b
  let v1324 := s.b ^^^ s.c
  let v1325 := s.a &&& v1324
  let v1326 := v1325 ^^^ (s.b &&& s.c)
  let v1327 := v1322 + v1326
  let v1328 := v1317 + s.d
  let v1329 := v1327 + v1317
  ⟨v1329, s.a, s.b, s.c, v1328, s.e, s.f, s.g⟩

theorem fullOut32_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut32 s w k = Spec.round s (w 32) k := by
  have hw32 := hw 32 (by decide) (by decide)
  dsimp only [fullOut32, Spec.round]
  rw [hw32]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv32_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1291 E (fullEnv32 E s w k) := by
  unfold fullEnv32
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv32_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv32 E s w k) := by
  exact (fullEnv32_before E s w k).frame (by decide)

theorem full_body32 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready32 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 256#64) 64)
    (hk : state.mem.readAt (kp.add 256#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1091 |>.take 39) state =
      .value (fullEnv32 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv32, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k32, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready32 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready32 E s w) (hw : ScheduleReady w) :
    Ready33 (fullEnv32 E s w k) (Spec.round s (w 32) k) w := by
  have hb := fullEnv32_before E s w k
  have hout := fullOut32_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv32, fullOut32, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1290 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1251 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1212 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv32, fullOut32, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1289 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1250 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1211 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv32, Spec.round, mlir_env]
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
  · rw [hb.read_val 1264 (by decide) (by rfl)]; exact h.w31
  · have hwr := hw 32 (by decide) (by decide)
    simp [fullEnv32, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step32 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready32 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1091 |>.take 39) state =
      .value (E', state) ∧
      Ready33 E' (Spec.round s (w 32) (constants.toList.getD 32 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 32 0
  have hf := fullEnv32_frame E s w k
  refine ⟨fullEnv32 E s w k,
    full_body32 E state s w kp k h hc (hk 32).1 (hk 32).2,
    full_ready32 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
