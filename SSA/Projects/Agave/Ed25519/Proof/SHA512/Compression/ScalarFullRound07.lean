import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 233..258: round 7. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv07 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v433 := s.e.rotateRight 14
  let v434 := s.e.rotateRight 18
  let v435 := v433 ^^^ v434
  let v436 := s.e.rotateRight 41
  let v437 := v435 ^^^ v436
  let v438 := s.e &&& s.f
  let v439 := s.e ^^^ (-1 : Word)
  let v440 := s.g &&& v439
  let v441 := k
  let v442 := v441 + (w 7)
  let v443 := v442 + s.h
  let v444 := v443 + v440
  let v445 := v444 + v438
  let v446 := v445 + v437
  let v447 := s.a.rotateRight 28
  let v448 := s.a.rotateRight 34
  let v449 := v447 ^^^ v448
  let v450 := s.a.rotateRight 39
  let v451 := v449 ^^^ v450
  let v452 := s.a &&& s.b
  let v453 := s.b ^^^ s.c
  let v454 := s.a &&& v453
  let v455 := v454 ^^^ (s.b &&& s.c)
  let v456 := v451 + v455
  let v457 := v446 + s.d
  let v458 := v456 + v446
  E[%433 := .value v433,
    %434 := .value v434,
    %435 := .value v435,
    %436 := .value v436,
    %437 := .value v437,
    %438 := .value v438,
    %439 := .value v439,
    %440 := .value v440,
    %441 := .value v441,
    %442 := .value v442,
    %443 := .value v443,
    %444 := .value v444,
    %445 := .value v445,
    %446 := .value v446,
    %447 := .value v447,
    %448 := .value v448,
    %449 := .value v449,
    %450 := .value v450,
    %451 := .value v451,
    %452 := .value v452,
    %453 := .value v453,
    %454 := .value v454,
    %455 := .value v455,
    %456 := .value v456,
    %457 := .value v457,
    %458 := .value v458]

def fullOut07 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v433 := s.e.rotateRight 14
  let v434 := s.e.rotateRight 18
  let v435 := v433 ^^^ v434
  let v436 := s.e.rotateRight 41
  let v437 := v435 ^^^ v436
  let v438 := s.e &&& s.f
  let v439 := s.e ^^^ (-1 : Word)
  let v440 := s.g &&& v439
  let v441 := k
  let v442 := v441 + (w 7)
  let v443 := v442 + s.h
  let v444 := v443 + v440
  let v445 := v444 + v438
  let v446 := v445 + v437
  let v447 := s.a.rotateRight 28
  let v448 := s.a.rotateRight 34
  let v449 := v447 ^^^ v448
  let v450 := s.a.rotateRight 39
  let v451 := v449 ^^^ v450
  let v452 := s.a &&& s.b
  let v453 := s.b ^^^ s.c
  let v454 := s.a &&& v453
  let v455 := v454 ^^^ (s.b &&& s.c)
  let v456 := v451 + v455
  let v457 := v446 + s.d
  let v458 := v456 + v446
  ⟨v458, s.a, s.b, s.c, v457, s.e, s.f, s.g⟩

theorem fullOut07_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut07 s w k = Spec.round s (w 7) k := by
  dsimp only [fullOut07, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv07_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 433 E (fullEnv07 E s w k) := by
  unfold fullEnv07
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv07_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv07 E s w k) := by
  exact (fullEnv07_before E s w k).frame (by decide)

theorem full_body07 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready07 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 56#64) 64)
    (hk : state.mem.readAt (kp.add 56#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 233 |>.take 26) state =
      .value (fullEnv07 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv07, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k07, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready07 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready07 E s w) (hw : ScheduleReady w) :
    Ready08 (fullEnv07 E s w k) (Spec.round s (w 7) k) w := by
  have hb := fullEnv07_before E s w k
  have hout := fullOut07_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv07, fullOut07, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 432 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 406 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 380 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv07, fullOut07, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 431 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 405 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 379 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv07, Spec.round, mlir_env]
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

theorem full_step07 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready07 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 233 |>.take 26) state =
      .value (E', state) ∧
      Ready08 E' (Spec.round s (w 7) (constants.toList.getD 7 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 7 0
  have hf := fullEnv07_frame E s w k
  refine ⟨fullEnv07 E s w k,
    full_body07 E state s w kp k h hc (hk 7).1 (hk 7).2,
    full_ready07 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
