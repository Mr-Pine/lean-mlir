import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 259..284: round 8. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv08 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v459 := s.e.rotateRight 14
  let v460 := s.e.rotateRight 18
  let v461 := v459 ^^^ v460
  let v462 := s.e.rotateRight 41
  let v463 := v461 ^^^ v462
  let v464 := s.e &&& s.f
  let v465 := s.e ^^^ (-1 : Word)
  let v466 := s.g &&& v465
  let v467 := k
  let v468 := v467 + (w 8)
  let v469 := v468 + s.h
  let v470 := v469 + v466
  let v471 := v470 + v464
  let v472 := v471 + v463
  let v473 := s.a.rotateRight 28
  let v474 := s.a.rotateRight 34
  let v475 := v473 ^^^ v474
  let v476 := s.a.rotateRight 39
  let v477 := v475 ^^^ v476
  let v478 := s.a &&& s.b
  let v479 := s.b ^^^ s.c
  let v480 := s.a &&& v479
  let v481 := v480 ^^^ (s.b &&& s.c)
  let v482 := v477 + v481
  let v483 := v472 + s.d
  let v484 := v482 + v472
  E[%459 := .value v459,
    %460 := .value v460,
    %461 := .value v461,
    %462 := .value v462,
    %463 := .value v463,
    %464 := .value v464,
    %465 := .value v465,
    %466 := .value v466,
    %467 := .value v467,
    %468 := .value v468,
    %469 := .value v469,
    %470 := .value v470,
    %471 := .value v471,
    %472 := .value v472,
    %473 := .value v473,
    %474 := .value v474,
    %475 := .value v475,
    %476 := .value v476,
    %477 := .value v477,
    %478 := .value v478,
    %479 := .value v479,
    %480 := .value v480,
    %481 := .value v481,
    %482 := .value v482,
    %483 := .value v483,
    %484 := .value v484]

def fullOut08 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v459 := s.e.rotateRight 14
  let v460 := s.e.rotateRight 18
  let v461 := v459 ^^^ v460
  let v462 := s.e.rotateRight 41
  let v463 := v461 ^^^ v462
  let v464 := s.e &&& s.f
  let v465 := s.e ^^^ (-1 : Word)
  let v466 := s.g &&& v465
  let v467 := k
  let v468 := v467 + (w 8)
  let v469 := v468 + s.h
  let v470 := v469 + v466
  let v471 := v470 + v464
  let v472 := v471 + v463
  let v473 := s.a.rotateRight 28
  let v474 := s.a.rotateRight 34
  let v475 := v473 ^^^ v474
  let v476 := s.a.rotateRight 39
  let v477 := v475 ^^^ v476
  let v478 := s.a &&& s.b
  let v479 := s.b ^^^ s.c
  let v480 := s.a &&& v479
  let v481 := v480 ^^^ (s.b &&& s.c)
  let v482 := v477 + v481
  let v483 := v472 + s.d
  let v484 := v482 + v472
  ⟨v484, s.a, s.b, s.c, v483, s.e, s.f, s.g⟩

theorem fullOut08_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut08 s w k = Spec.round s (w 8) k := by
  dsimp only [fullOut08, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv08_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 459 E (fullEnv08 E s w k) := by
  unfold fullEnv08
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv08_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv08 E s w k) := by
  exact (fullEnv08_before E s w k).frame (by decide)

theorem full_body08 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready08 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 64#64) 64)
    (hk : state.mem.readAt (kp.add 64#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 259 |>.take 26) state =
      .value (fullEnv08 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv08, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k08, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready08 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready08 E s w) (hw : ScheduleReady w) :
    Ready09 (fullEnv08 E s w k) (Spec.round s (w 8) k) w := by
  have hb := fullEnv08_before E s w k
  have hout := fullOut08_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv08, fullOut08, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 458 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 432 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 406 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv08, fullOut08, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 457 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 431 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 405 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv08, Spec.round, mlir_env]
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

theorem full_step08 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready08 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 259 |>.take 26) state =
      .value (E', state) ∧
      Ready09 E' (Spec.round s (w 8) (constants.toList.getD 8 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 8 0
  have hf := fullEnv08_frame E s w k
  refine ⟨fullEnv08 E s w k,
    full_body08 E state s w kp k h hc (hk 8).1 (hk 8).2,
    full_ready08 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
