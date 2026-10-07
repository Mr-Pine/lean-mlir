import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1130..1168: round 33. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv33 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1330 := (w 18).rotateRight 1
  let v1331 := (w 18).rotateRight 8
  let v1332 := v1330 ^^^ v1331
  let v1333 := (w 18) >>> 7
  let v1334 := v1332 ^^^ v1333
  let v1335 := (w 31).rotateRight 19
  let v1336 := (w 31).rotateRight 61
  let v1337 := v1335 ^^^ v1336
  let v1338 := (w 31) >>> 6
  let v1339 := v1337 ^^^ v1338
  let v1340 := v1334 + (w 17)
  let v1341 := v1340 + (w 26)
  let v1342 := v1341 + v1339
  let v1343 := s.e.rotateRight 14
  let v1344 := s.e.rotateRight 18
  let v1345 := v1343 ^^^ v1344
  let v1346 := s.e.rotateRight 41
  let v1347 := v1345 ^^^ v1346
  let v1348 := s.e &&& s.f
  let v1349 := s.e ^^^ (-1 : Word)
  let v1350 := s.g &&& v1349
  let v1351 := v1348 ||| v1350
  let v1352 := k
  let v1353 := v1342 + v1352
  let v1354 := v1353 + s.h
  let v1355 := v1354 + v1351
  let v1356 := v1355 + v1347
  let v1357 := s.a.rotateRight 28
  let v1358 := s.a.rotateRight 34
  let v1359 := v1357 ^^^ v1358
  let v1360 := s.a.rotateRight 39
  let v1361 := v1359 ^^^ v1360
  let v1362 := s.a &&& s.b
  let v1363 := s.b ^^^ s.c
  let v1364 := s.a &&& v1363
  let v1365 := v1364 ^^^ (s.b &&& s.c)
  let v1366 := v1361 + v1365
  let v1367 := v1356 + s.d
  let v1368 := v1366 + v1356
  E[%1330 := .value v1330,
    %1331 := .value v1331,
    %1332 := .value v1332,
    %1333 := .value v1333,
    %1334 := .value v1334,
    %1335 := .value v1335,
    %1336 := .value v1336,
    %1337 := .value v1337,
    %1338 := .value v1338,
    %1339 := .value v1339,
    %1340 := .value v1340,
    %1341 := .value v1341,
    %1342 := .value v1342,
    %1343 := .value v1343,
    %1344 := .value v1344,
    %1345 := .value v1345,
    %1346 := .value v1346,
    %1347 := .value v1347,
    %1348 := .value v1348,
    %1349 := .value v1349,
    %1350 := .value v1350,
    %1351 := .value v1351,
    %1352 := .value v1352,
    %1353 := .value v1353,
    %1354 := .value v1354,
    %1355 := .value v1355,
    %1356 := .value v1356,
    %1357 := .value v1357,
    %1358 := .value v1358,
    %1359 := .value v1359,
    %1360 := .value v1360,
    %1361 := .value v1361,
    %1362 := .value v1362,
    %1363 := .value v1363,
    %1364 := .value v1364,
    %1365 := .value v1365,
    %1366 := .value v1366,
    %1367 := .value v1367,
    %1368 := .value v1368]

def fullOut33 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1330 := (w 18).rotateRight 1
  let v1331 := (w 18).rotateRight 8
  let v1332 := v1330 ^^^ v1331
  let v1333 := (w 18) >>> 7
  let v1334 := v1332 ^^^ v1333
  let v1335 := (w 31).rotateRight 19
  let v1336 := (w 31).rotateRight 61
  let v1337 := v1335 ^^^ v1336
  let v1338 := (w 31) >>> 6
  let v1339 := v1337 ^^^ v1338
  let v1340 := v1334 + (w 17)
  let v1341 := v1340 + (w 26)
  let v1342 := v1341 + v1339
  let v1343 := s.e.rotateRight 14
  let v1344 := s.e.rotateRight 18
  let v1345 := v1343 ^^^ v1344
  let v1346 := s.e.rotateRight 41
  let v1347 := v1345 ^^^ v1346
  let v1348 := s.e &&& s.f
  let v1349 := s.e ^^^ (-1 : Word)
  let v1350 := s.g &&& v1349
  let v1351 := v1348 ||| v1350
  let v1352 := k
  let v1353 := v1342 + v1352
  let v1354 := v1353 + s.h
  let v1355 := v1354 + v1351
  let v1356 := v1355 + v1347
  let v1357 := s.a.rotateRight 28
  let v1358 := s.a.rotateRight 34
  let v1359 := v1357 ^^^ v1358
  let v1360 := s.a.rotateRight 39
  let v1361 := v1359 ^^^ v1360
  let v1362 := s.a &&& s.b
  let v1363 := s.b ^^^ s.c
  let v1364 := s.a &&& v1363
  let v1365 := v1364 ^^^ (s.b &&& s.c)
  let v1366 := v1361 + v1365
  let v1367 := v1356 + s.d
  let v1368 := v1366 + v1356
  ⟨v1368, s.a, s.b, s.c, v1367, s.e, s.f, s.g⟩

theorem fullOut33_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut33 s w k = Spec.round s (w 33) k := by
  have hw33 := hw 33 (by decide) (by decide)
  dsimp only [fullOut33, Spec.round]
  rw [hw33]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv33_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1330 E (fullEnv33 E s w k) := by
  unfold fullEnv33
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv33_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv33 E s w k) := by
  exact (fullEnv33_before E s w k).frame (by decide)

theorem full_body33 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready33 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 264#64) 64)
    (hk : state.mem.readAt (kp.add 264#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1130 |>.take 39) state =
      .value (fullEnv33 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv33, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k33, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready33 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready33 E s w) (hw : ScheduleReady w) :
    Ready34 (fullEnv33 E s w k) (Spec.round s (w 33) k) w := by
  have hb := fullEnv33_before E s w k
  have hout := fullOut33_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv33, fullOut33, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1329 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1290 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1251 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv33, fullOut33, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1328 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1289 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1250 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv33, Spec.round, mlir_env]
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
  · rw [hb.read_val 1303 (by decide) (by rfl)]; exact h.w32
  · have hwr := hw 33 (by decide) (by decide)
    simp [fullEnv33, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step33 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready33 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1130 |>.take 39) state =
      .value (E', state) ∧
      Ready34 E' (Spec.round s (w 33) (constants.toList.getD 33 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 33 0
  have hf := fullEnv33_frame E s w k
  refine ⟨fullEnv33 E s w k,
    full_body33 E state s w kp k h hc (hk 33).1 (hk 33).2,
    full_ready33 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
