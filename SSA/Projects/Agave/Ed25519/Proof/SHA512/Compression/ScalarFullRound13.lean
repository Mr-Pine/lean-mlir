import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 389..414: round 13. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv13 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v589 := s.e.rotateRight 14
  let v590 := s.e.rotateRight 18
  let v591 := v589 ^^^ v590
  let v592 := s.e.rotateRight 41
  let v593 := v591 ^^^ v592
  let v594 := s.e &&& s.f
  let v595 := s.e ^^^ (-1 : Word)
  let v596 := s.g &&& v595
  let v597 := k
  let v598 := v597 + (w 13)
  let v599 := v598 + s.h
  let v600 := v599 + v596
  let v601 := v600 + v594
  let v602 := v601 + v593
  let v603 := s.a.rotateRight 28
  let v604 := s.a.rotateRight 34
  let v605 := v603 ^^^ v604
  let v606 := s.a.rotateRight 39
  let v607 := v605 ^^^ v606
  let v608 := s.a &&& s.b
  let v609 := s.b ^^^ s.c
  let v610 := s.a &&& v609
  let v611 := v610 ^^^ (s.b &&& s.c)
  let v612 := v607 + v611
  let v613 := v602 + s.d
  let v614 := v612 + v602
  E[%589 := .value v589,
    %590 := .value v590,
    %591 := .value v591,
    %592 := .value v592,
    %593 := .value v593,
    %594 := .value v594,
    %595 := .value v595,
    %596 := .value v596,
    %597 := .value v597,
    %598 := .value v598,
    %599 := .value v599,
    %600 := .value v600,
    %601 := .value v601,
    %602 := .value v602,
    %603 := .value v603,
    %604 := .value v604,
    %605 := .value v605,
    %606 := .value v606,
    %607 := .value v607,
    %608 := .value v608,
    %609 := .value v609,
    %610 := .value v610,
    %611 := .value v611,
    %612 := .value v612,
    %613 := .value v613,
    %614 := .value v614]

def fullOut13 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v589 := s.e.rotateRight 14
  let v590 := s.e.rotateRight 18
  let v591 := v589 ^^^ v590
  let v592 := s.e.rotateRight 41
  let v593 := v591 ^^^ v592
  let v594 := s.e &&& s.f
  let v595 := s.e ^^^ (-1 : Word)
  let v596 := s.g &&& v595
  let v597 := k
  let v598 := v597 + (w 13)
  let v599 := v598 + s.h
  let v600 := v599 + v596
  let v601 := v600 + v594
  let v602 := v601 + v593
  let v603 := s.a.rotateRight 28
  let v604 := s.a.rotateRight 34
  let v605 := v603 ^^^ v604
  let v606 := s.a.rotateRight 39
  let v607 := v605 ^^^ v606
  let v608 := s.a &&& s.b
  let v609 := s.b ^^^ s.c
  let v610 := s.a &&& v609
  let v611 := v610 ^^^ (s.b &&& s.c)
  let v612 := v607 + v611
  let v613 := v602 + s.d
  let v614 := v612 + v602
  ⟨v614, s.a, s.b, s.c, v613, s.e, s.f, s.g⟩

theorem fullOut13_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut13 s w k = Spec.round s (w 13) k := by
  dsimp only [fullOut13, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv13_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 589 E (fullEnv13 E s w k) := by
  unfold fullEnv13
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv13_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv13 E s w k) := by
  exact (fullEnv13_before E s w k).frame (by decide)

theorem full_body13 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready13 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 104#64) 64)
    (hk : state.mem.readAt (kp.add 104#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 389 |>.take 26) state =
      .value (fullEnv13 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv13, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k13, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready13 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready13 E s w) (hw : ScheduleReady w) :
    Ready14 (fullEnv13 E s w k) (Spec.round s (w 13) k) w := by
  have hb := fullEnv13_before E s w k
  have hout := fullOut13_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv13, fullOut13, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 588 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 562 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 536 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv13, fullOut13, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 587 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 561 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 535 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv13, Spec.round, mlir_env]
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

theorem full_step13 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready13 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 389 |>.take 26) state =
      .value (E', state) ∧
      Ready14 E' (Spec.round s (w 13) (constants.toList.getD 13 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 13 0
  have hf := fullEnv13_frame E s w k
  refine ⟨fullEnv13 E s w k,
    full_body13 E state s w kp k h hc (hk 13).1 (hk 13).2,
    full_ready13 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
