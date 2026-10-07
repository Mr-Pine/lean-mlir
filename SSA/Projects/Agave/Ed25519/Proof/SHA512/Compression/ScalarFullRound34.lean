import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 1169..1207: round 34. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv34 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1369 := (w 19).rotateRight 1
  let v1370 := (w 19).rotateRight 8
  let v1371 := v1369 ^^^ v1370
  let v1372 := (w 19) >>> 7
  let v1373 := v1371 ^^^ v1372
  let v1374 := (w 32).rotateRight 19
  let v1375 := (w 32).rotateRight 61
  let v1376 := v1374 ^^^ v1375
  let v1377 := (w 32) >>> 6
  let v1378 := v1376 ^^^ v1377
  let v1379 := v1373 + (w 18)
  let v1380 := v1379 + (w 27)
  let v1381 := v1380 + v1378
  let v1382 := s.e.rotateRight 14
  let v1383 := s.e.rotateRight 18
  let v1384 := v1382 ^^^ v1383
  let v1385 := s.e.rotateRight 41
  let v1386 := v1384 ^^^ v1385
  let v1387 := s.e &&& s.f
  let v1388 := s.e ^^^ (-1 : Word)
  let v1389 := s.g &&& v1388
  let v1390 := v1387 ||| v1389
  let v1391 := k
  let v1392 := v1381 + v1391
  let v1393 := v1392 + s.h
  let v1394 := v1393 + v1390
  let v1395 := v1394 + v1386
  let v1396 := s.a.rotateRight 28
  let v1397 := s.a.rotateRight 34
  let v1398 := v1396 ^^^ v1397
  let v1399 := s.a.rotateRight 39
  let v1400 := v1398 ^^^ v1399
  let v1401 := s.a &&& s.b
  let v1402 := s.b ^^^ s.c
  let v1403 := s.a &&& v1402
  let v1404 := v1403 ^^^ (s.b &&& s.c)
  let v1405 := v1400 + v1404
  let v1406 := v1395 + s.d
  let v1407 := v1405 + v1395
  E[%1369 := .value v1369,
    %1370 := .value v1370,
    %1371 := .value v1371,
    %1372 := .value v1372,
    %1373 := .value v1373,
    %1374 := .value v1374,
    %1375 := .value v1375,
    %1376 := .value v1376,
    %1377 := .value v1377,
    %1378 := .value v1378,
    %1379 := .value v1379,
    %1380 := .value v1380,
    %1381 := .value v1381,
    %1382 := .value v1382,
    %1383 := .value v1383,
    %1384 := .value v1384,
    %1385 := .value v1385,
    %1386 := .value v1386,
    %1387 := .value v1387,
    %1388 := .value v1388,
    %1389 := .value v1389,
    %1390 := .value v1390,
    %1391 := .value v1391,
    %1392 := .value v1392,
    %1393 := .value v1393,
    %1394 := .value v1394,
    %1395 := .value v1395,
    %1396 := .value v1396,
    %1397 := .value v1397,
    %1398 := .value v1398,
    %1399 := .value v1399,
    %1400 := .value v1400,
    %1401 := .value v1401,
    %1402 := .value v1402,
    %1403 := .value v1403,
    %1404 := .value v1404,
    %1405 := .value v1405,
    %1406 := .value v1406,
    %1407 := .value v1407]

def fullOut34 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1369 := (w 19).rotateRight 1
  let v1370 := (w 19).rotateRight 8
  let v1371 := v1369 ^^^ v1370
  let v1372 := (w 19) >>> 7
  let v1373 := v1371 ^^^ v1372
  let v1374 := (w 32).rotateRight 19
  let v1375 := (w 32).rotateRight 61
  let v1376 := v1374 ^^^ v1375
  let v1377 := (w 32) >>> 6
  let v1378 := v1376 ^^^ v1377
  let v1379 := v1373 + (w 18)
  let v1380 := v1379 + (w 27)
  let v1381 := v1380 + v1378
  let v1382 := s.e.rotateRight 14
  let v1383 := s.e.rotateRight 18
  let v1384 := v1382 ^^^ v1383
  let v1385 := s.e.rotateRight 41
  let v1386 := v1384 ^^^ v1385
  let v1387 := s.e &&& s.f
  let v1388 := s.e ^^^ (-1 : Word)
  let v1389 := s.g &&& v1388
  let v1390 := v1387 ||| v1389
  let v1391 := k
  let v1392 := v1381 + v1391
  let v1393 := v1392 + s.h
  let v1394 := v1393 + v1390
  let v1395 := v1394 + v1386
  let v1396 := s.a.rotateRight 28
  let v1397 := s.a.rotateRight 34
  let v1398 := v1396 ^^^ v1397
  let v1399 := s.a.rotateRight 39
  let v1400 := v1398 ^^^ v1399
  let v1401 := s.a &&& s.b
  let v1402 := s.b ^^^ s.c
  let v1403 := s.a &&& v1402
  let v1404 := v1403 ^^^ (s.b &&& s.c)
  let v1405 := v1400 + v1404
  let v1406 := v1395 + s.d
  let v1407 := v1405 + v1395
  ⟨v1407, s.a, s.b, s.c, v1406, s.e, s.f, s.g⟩

theorem fullOut34_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut34 s w k = Spec.round s (w 34) k := by
  have hw34 := hw 34 (by decide) (by decide)
  dsimp only [fullOut34, Spec.round]
  rw [hw34]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv34_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1369 E (fullEnv34 E s w k) := by
  unfold fullEnv34
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv34_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv34 E s w k) := by
  exact (fullEnv34_before E s w k).frame (by decide)

theorem full_body34 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready34 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 272#64) 64)
    (hk : state.mem.readAt (kp.add 272#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 1169 |>.take 39) state =
      .value (fullEnv34 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv34, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, h.w25, h.w26, h.w27, h.w28, h.w29, h.w30, h.w31, h.w32, h.w33, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k34, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready34 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready34 E s w) (hw : ScheduleReady w) :
    Ready35 (fullEnv34 E s w k) (Spec.round s (w 34) k) w := by
  have hb := fullEnv34_before E s w k
  have hout := fullOut34_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv34, fullOut34, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1368 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 1329 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 1290 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv34, fullOut34, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1367 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 1328 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 1289 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv34, Spec.round, mlir_env]
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
  · rw [hb.read_val 1342 (by decide) (by rfl)]; exact h.w33
  · have hwr := hw 34 (by decide) (by decide)
    simp [fullEnv34, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step34 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready34 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 1169 |>.take 39) state =
      .value (E', state) ∧
      Ready35 E' (Spec.round s (w 34) (constants.toList.getD 34 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 34 0
  have hf := fullEnv34_frame E s w k
  refine ⟨fullEnv34 E s w k,
    full_body34 E state s w kp k h hc (hk 34).1 (hk 34).2,
    full_ready34 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
