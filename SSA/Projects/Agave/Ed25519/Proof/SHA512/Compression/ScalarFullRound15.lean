import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 441..466: round 15. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv15 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v641 := s.e.rotateRight 14
  let v642 := s.e.rotateRight 18
  let v643 := v641 ^^^ v642
  let v644 := s.e.rotateRight 41
  let v645 := v643 ^^^ v644
  let v646 := s.e &&& s.f
  let v647 := s.e ^^^ (-1 : Word)
  let v648 := s.g &&& v647
  let v649 := k
  let v650 := v649 + (w 15)
  let v651 := v650 + s.h
  let v652 := v651 + v648
  let v653 := v652 + v646
  let v654 := v653 + v645
  let v655 := s.a.rotateRight 28
  let v656 := s.a.rotateRight 34
  let v657 := v655 ^^^ v656
  let v658 := s.a.rotateRight 39
  let v659 := v657 ^^^ v658
  let v660 := s.a &&& s.b
  let v661 := s.b ^^^ s.c
  let v662 := s.a &&& v661
  let v663 := v662 ^^^ (s.b &&& s.c)
  let v664 := v659 + v663
  let v665 := v654 + s.d
  let v666 := v664 + v654
  E[%641 := .value v641,
    %642 := .value v642,
    %643 := .value v643,
    %644 := .value v644,
    %645 := .value v645,
    %646 := .value v646,
    %647 := .value v647,
    %648 := .value v648,
    %649 := .value v649,
    %650 := .value v650,
    %651 := .value v651,
    %652 := .value v652,
    %653 := .value v653,
    %654 := .value v654,
    %655 := .value v655,
    %656 := .value v656,
    %657 := .value v657,
    %658 := .value v658,
    %659 := .value v659,
    %660 := .value v660,
    %661 := .value v661,
    %662 := .value v662,
    %663 := .value v663,
    %664 := .value v664,
    %665 := .value v665,
    %666 := .value v666]

def fullOut15 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v641 := s.e.rotateRight 14
  let v642 := s.e.rotateRight 18
  let v643 := v641 ^^^ v642
  let v644 := s.e.rotateRight 41
  let v645 := v643 ^^^ v644
  let v646 := s.e &&& s.f
  let v647 := s.e ^^^ (-1 : Word)
  let v648 := s.g &&& v647
  let v649 := k
  let v650 := v649 + (w 15)
  let v651 := v650 + s.h
  let v652 := v651 + v648
  let v653 := v652 + v646
  let v654 := v653 + v645
  let v655 := s.a.rotateRight 28
  let v656 := s.a.rotateRight 34
  let v657 := v655 ^^^ v656
  let v658 := s.a.rotateRight 39
  let v659 := v657 ^^^ v658
  let v660 := s.a &&& s.b
  let v661 := s.b ^^^ s.c
  let v662 := s.a &&& v661
  let v663 := v662 ^^^ (s.b &&& s.c)
  let v664 := v659 + v663
  let v665 := v654 + s.d
  let v666 := v664 + v654
  ⟨v666, s.a, s.b, s.c, v665, s.e, s.f, s.g⟩

theorem fullOut15_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut15 s w k = Spec.round s (w 15) k := by
  dsimp only [fullOut15, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv15_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 641 E (fullEnv15 E s w k) := by
  unfold fullEnv15
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv15_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv15 E s w k) := by
  exact (fullEnv15_before E s w k).frame (by decide)

theorem full_body15 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready15 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 120#64) 64)
    (hk : state.mem.readAt (kp.add 120#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 441 |>.take 26) state =
      .value (fullEnv15 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv15, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k15, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready15 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready15 E s w) (hw : ScheduleReady w) :
    Ready16 (fullEnv15 E s w k) (Spec.round s (w 15) k) w := by
  have hb := fullEnv15_before E s w k
  have hout := fullOut15_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv15, fullOut15, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 640 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 614 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 588 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv15, fullOut15, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 639 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 613 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 587 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv15, Spec.round, mlir_env]
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

theorem full_step15 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready15 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 441 |>.take 26) state =
      .value (E', state) ∧
      Ready16 E' (Spec.round s (w 15) (constants.toList.getD 15 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 15 0
  have hf := fullEnv15_frame E s w k
  refine ⟨fullEnv15 E s w k,
    full_body15 E state s w kp k h hc (hk 15).1 (hk 15).2,
    full_ready15 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
