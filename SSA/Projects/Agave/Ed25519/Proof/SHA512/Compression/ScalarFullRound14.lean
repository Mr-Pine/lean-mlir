import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 415..440: round 14. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv14 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v615 := s.e.rotateRight 14
  let v616 := s.e.rotateRight 18
  let v617 := v615 ^^^ v616
  let v618 := s.e.rotateRight 41
  let v619 := v617 ^^^ v618
  let v620 := s.e &&& s.f
  let v621 := s.e ^^^ (-1 : Word)
  let v622 := s.g &&& v621
  let v623 := k
  let v624 := v623 + (w 14)
  let v625 := v624 + s.h
  let v626 := v625 + v622
  let v627 := v626 + v620
  let v628 := v627 + v619
  let v629 := s.a.rotateRight 28
  let v630 := s.a.rotateRight 34
  let v631 := v629 ^^^ v630
  let v632 := s.a.rotateRight 39
  let v633 := v631 ^^^ v632
  let v634 := s.a &&& s.b
  let v635 := s.b ^^^ s.c
  let v636 := s.a &&& v635
  let v637 := v636 ^^^ (s.b &&& s.c)
  let v638 := v633 + v637
  let v639 := v628 + s.d
  let v640 := v638 + v628
  E[%615 := .value v615,
    %616 := .value v616,
    %617 := .value v617,
    %618 := .value v618,
    %619 := .value v619,
    %620 := .value v620,
    %621 := .value v621,
    %622 := .value v622,
    %623 := .value v623,
    %624 := .value v624,
    %625 := .value v625,
    %626 := .value v626,
    %627 := .value v627,
    %628 := .value v628,
    %629 := .value v629,
    %630 := .value v630,
    %631 := .value v631,
    %632 := .value v632,
    %633 := .value v633,
    %634 := .value v634,
    %635 := .value v635,
    %636 := .value v636,
    %637 := .value v637,
    %638 := .value v638,
    %639 := .value v639,
    %640 := .value v640]

def fullOut14 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v615 := s.e.rotateRight 14
  let v616 := s.e.rotateRight 18
  let v617 := v615 ^^^ v616
  let v618 := s.e.rotateRight 41
  let v619 := v617 ^^^ v618
  let v620 := s.e &&& s.f
  let v621 := s.e ^^^ (-1 : Word)
  let v622 := s.g &&& v621
  let v623 := k
  let v624 := v623 + (w 14)
  let v625 := v624 + s.h
  let v626 := v625 + v622
  let v627 := v626 + v620
  let v628 := v627 + v619
  let v629 := s.a.rotateRight 28
  let v630 := s.a.rotateRight 34
  let v631 := v629 ^^^ v630
  let v632 := s.a.rotateRight 39
  let v633 := v631 ^^^ v632
  let v634 := s.a &&& s.b
  let v635 := s.b ^^^ s.c
  let v636 := s.a &&& v635
  let v637 := v636 ^^^ (s.b &&& s.c)
  let v638 := v633 + v637
  let v639 := v628 + s.d
  let v640 := v638 + v628
  ⟨v640, s.a, s.b, s.c, v639, s.e, s.f, s.g⟩

theorem fullOut14_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut14 s w k = Spec.round s (w 14) k := by
  dsimp only [fullOut14, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv14_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 615 E (fullEnv14 E s w k) := by
  unfold fullEnv14
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv14_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv14 E s w k) := by
  exact (fullEnv14_before E s w k).frame (by decide)

theorem full_body14 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready14 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 112#64) 64)
    (hk : state.mem.readAt (kp.add 112#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 415 |>.take 26) state =
      .value (fullEnv14 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv14, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k14, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready14 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready14 E s w) (hw : ScheduleReady w) :
    Ready15 (fullEnv14 E s w k) (Spec.round s (w 14) k) w := by
  have hb := fullEnv14_before E s w k
  have hout := fullOut14_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv14, fullOut14, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 614 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 588 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 562 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv14, fullOut14, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 613 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 587 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 561 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv14, Spec.round, mlir_env]
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

theorem full_step14 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready14 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 415 |>.take 26) state =
      .value (E', state) ∧
      Ready15 E' (Spec.round s (w 14) (constants.toList.getD 14 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 14 0
  have hf := fullEnv14_frame E s w k
  refine ⟨fullEnv14 E s w k,
    full_body14 E state s w kp k h hc (hk 14).1 (hk 14).2,
    full_ready14 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
