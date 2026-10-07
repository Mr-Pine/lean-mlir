import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 285..310: round 9. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv09 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v485 := s.e.rotateRight 14
  let v486 := s.e.rotateRight 18
  let v487 := v485 ^^^ v486
  let v488 := s.e.rotateRight 41
  let v489 := v487 ^^^ v488
  let v490 := s.e &&& s.f
  let v491 := s.e ^^^ (-1 : Word)
  let v492 := s.g &&& v491
  let v493 := k
  let v494 := v493 + (w 9)
  let v495 := v494 + s.h
  let v496 := v495 + v492
  let v497 := v496 + v490
  let v498 := v497 + v489
  let v499 := s.a.rotateRight 28
  let v500 := s.a.rotateRight 34
  let v501 := v499 ^^^ v500
  let v502 := s.a.rotateRight 39
  let v503 := v501 ^^^ v502
  let v504 := s.a &&& s.b
  let v505 := s.b ^^^ s.c
  let v506 := s.a &&& v505
  let v507 := v506 ^^^ (s.b &&& s.c)
  let v508 := v503 + v507
  let v509 := v498 + s.d
  let v510 := v508 + v498
  E[%485 := .value v485,
    %486 := .value v486,
    %487 := .value v487,
    %488 := .value v488,
    %489 := .value v489,
    %490 := .value v490,
    %491 := .value v491,
    %492 := .value v492,
    %493 := .value v493,
    %494 := .value v494,
    %495 := .value v495,
    %496 := .value v496,
    %497 := .value v497,
    %498 := .value v498,
    %499 := .value v499,
    %500 := .value v500,
    %501 := .value v501,
    %502 := .value v502,
    %503 := .value v503,
    %504 := .value v504,
    %505 := .value v505,
    %506 := .value v506,
    %507 := .value v507,
    %508 := .value v508,
    %509 := .value v509,
    %510 := .value v510]

def fullOut09 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v485 := s.e.rotateRight 14
  let v486 := s.e.rotateRight 18
  let v487 := v485 ^^^ v486
  let v488 := s.e.rotateRight 41
  let v489 := v487 ^^^ v488
  let v490 := s.e &&& s.f
  let v491 := s.e ^^^ (-1 : Word)
  let v492 := s.g &&& v491
  let v493 := k
  let v494 := v493 + (w 9)
  let v495 := v494 + s.h
  let v496 := v495 + v492
  let v497 := v496 + v490
  let v498 := v497 + v489
  let v499 := s.a.rotateRight 28
  let v500 := s.a.rotateRight 34
  let v501 := v499 ^^^ v500
  let v502 := s.a.rotateRight 39
  let v503 := v501 ^^^ v502
  let v504 := s.a &&& s.b
  let v505 := s.b ^^^ s.c
  let v506 := s.a &&& v505
  let v507 := v506 ^^^ (s.b &&& s.c)
  let v508 := v503 + v507
  let v509 := v498 + s.d
  let v510 := v508 + v498
  ⟨v510, s.a, s.b, s.c, v509, s.e, s.f, s.g⟩

theorem fullOut09_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut09 s w k = Spec.round s (w 9) k := by
  dsimp only [fullOut09, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv09_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 485 E (fullEnv09 E s w k) := by
  unfold fullEnv09
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv09_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv09 E s w k) := by
  exact (fullEnv09_before E s w k).frame (by decide)

theorem full_body09 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready09 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 72#64) 64)
    (hk : state.mem.readAt (kp.add 72#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 285 |>.take 26) state =
      .value (fullEnv09 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv09, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k09, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready09 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready09 E s w) (hw : ScheduleReady w) :
    Ready10 (fullEnv09 E s w k) (Spec.round s (w 9) k) w := by
  have hb := fullEnv09_before E s w k
  have hout := fullOut09_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv09, fullOut09, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 484 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 458 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 432 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv09, fullOut09, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 483 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 457 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 431 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv09, Spec.round, mlir_env]
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

theorem full_step09 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready09 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 285 |>.take 26) state =
      .value (E', state) ∧
      Ready10 E' (Spec.round s (w 9) (constants.toList.getD 9 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 9 0
  have hf := fullEnv09_frame E s w k
  refine ⟨fullEnv09 E s w k,
    full_body09 E state s w kp k h hc (hk 9).1 (hk 9).2,
    full_ready09 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
