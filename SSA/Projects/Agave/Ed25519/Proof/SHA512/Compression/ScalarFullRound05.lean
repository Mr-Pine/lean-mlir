import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 181..206: round 5. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv05 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v381 := s.e.rotateRight 14
  let v382 := s.e.rotateRight 18
  let v383 := v381 ^^^ v382
  let v384 := s.e.rotateRight 41
  let v385 := v383 ^^^ v384
  let v386 := s.e &&& s.f
  let v387 := s.e ^^^ (-1 : Word)
  let v388 := s.g &&& v387
  let v389 := k
  let v390 := v389 + (w 5)
  let v391 := v390 + s.h
  let v392 := v391 + v388
  let v393 := v392 + v386
  let v394 := v393 + v385
  let v395 := s.a.rotateRight 28
  let v396 := s.a.rotateRight 34
  let v397 := v395 ^^^ v396
  let v398 := s.a.rotateRight 39
  let v399 := v397 ^^^ v398
  let v400 := s.a &&& s.b
  let v401 := s.b ^^^ s.c
  let v402 := s.a &&& v401
  let v403 := v402 ^^^ (s.b &&& s.c)
  let v404 := v399 + v403
  let v405 := v394 + s.d
  let v406 := v404 + v394
  E[%381 := .value v381,
    %382 := .value v382,
    %383 := .value v383,
    %384 := .value v384,
    %385 := .value v385,
    %386 := .value v386,
    %387 := .value v387,
    %388 := .value v388,
    %389 := .value v389,
    %390 := .value v390,
    %391 := .value v391,
    %392 := .value v392,
    %393 := .value v393,
    %394 := .value v394,
    %395 := .value v395,
    %396 := .value v396,
    %397 := .value v397,
    %398 := .value v398,
    %399 := .value v399,
    %400 := .value v400,
    %401 := .value v401,
    %402 := .value v402,
    %403 := .value v403,
    %404 := .value v404,
    %405 := .value v405,
    %406 := .value v406]

def fullOut05 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v381 := s.e.rotateRight 14
  let v382 := s.e.rotateRight 18
  let v383 := v381 ^^^ v382
  let v384 := s.e.rotateRight 41
  let v385 := v383 ^^^ v384
  let v386 := s.e &&& s.f
  let v387 := s.e ^^^ (-1 : Word)
  let v388 := s.g &&& v387
  let v389 := k
  let v390 := v389 + (w 5)
  let v391 := v390 + s.h
  let v392 := v391 + v388
  let v393 := v392 + v386
  let v394 := v393 + v385
  let v395 := s.a.rotateRight 28
  let v396 := s.a.rotateRight 34
  let v397 := v395 ^^^ v396
  let v398 := s.a.rotateRight 39
  let v399 := v397 ^^^ v398
  let v400 := s.a &&& s.b
  let v401 := s.b ^^^ s.c
  let v402 := s.a &&& v401
  let v403 := v402 ^^^ (s.b &&& s.c)
  let v404 := v399 + v403
  let v405 := v394 + s.d
  let v406 := v404 + v394
  ⟨v406, s.a, s.b, s.c, v405, s.e, s.f, s.g⟩

theorem fullOut05_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut05 s w k = Spec.round s (w 5) k := by
  dsimp only [fullOut05, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv05_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 381 E (fullEnv05 E s w k) := by
  unfold fullEnv05
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv05_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv05 E s w k) := by
  exact (fullEnv05_before E s w k).frame (by decide)

theorem full_body05 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready05 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 40#64) 64)
    (hk : state.mem.readAt (kp.add 40#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 181 |>.take 26) state =
      .value (fullEnv05 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv05, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k05, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready05 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready05 E s w) (hw : ScheduleReady w) :
    Ready06 (fullEnv05 E s w k) (Spec.round s (w 5) k) w := by
  have hb := fullEnv05_before E s w k
  have hout := fullOut05_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv05, fullOut05, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 380 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 354 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 328 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv05, fullOut05, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 379 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 353 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 327 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv05, Spec.round, mlir_env]
  · rw [hb.read_val 204 (by decide) (by rfl)]; exact h.w0
  · rw [hb.read_val 207 (by decide) (by rfl)]; exact h.w1
  · rw [hb.read_val 210 (by decide) (by rfl)]; exact h.w2
  · rw [hb.read_val 213 (by decide) (by rfl)]; exact h.w3
  · rw [hb.read_val 216 (by decide) (by rfl)]; exact h.w4
  · rw [hb.read_val 219 (by decide) (by rfl)]; exact h.w5
  · rw [hb.read_val 222 (by decide) (by rfl)]; exact h.w6
  · rw [hb.read_val 225 (by decide) (by rfl)]; exact h.w7
  · rw [hb.read_val 228 (by decide) (by rfl)]; exact h.w8
  · rw [hb.read_val 231 (by decide) (by rfl)]; exact h.w9
  · rw [hb.read_val 234 (by decide) (by rfl)]; exact h.w10
  · rw [hb.read_val 237 (by decide) (by rfl)]; exact h.w11
  · rw [hb.read_val 240 (by decide) (by rfl)]; exact h.w12
  · rw [hb.read_val 243 (by decide) (by rfl)]; exact h.w13
  · rw [hb.read_val 246 (by decide) (by rfl)]; exact h.w14
  · rw [hb.read_val 249 (by decide) (by rfl)]; exact h.w15

theorem full_step05 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready05 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 181 |>.take 26) state =
      .value (E', state) ∧
      Ready06 E' (Spec.round s (w 5) (constants.toList.getD 5 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 5 0
  have hf := fullEnv05_frame E s w k
  refine ⟨fullEnv05 E s w k,
    full_body05 E state s w kp k h hc (hk 5).1 (hk 5).2,
    full_ready05 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
