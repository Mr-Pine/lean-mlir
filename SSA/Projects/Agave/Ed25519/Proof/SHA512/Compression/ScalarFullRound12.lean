import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 363..388: round 12. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv12 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v563 := s.e.rotateRight 14
  let v564 := s.e.rotateRight 18
  let v565 := v563 ^^^ v564
  let v566 := s.e.rotateRight 41
  let v567 := v565 ^^^ v566
  let v568 := s.e &&& s.f
  let v569 := s.e ^^^ (-1 : Word)
  let v570 := s.g &&& v569
  let v571 := k
  let v572 := v571 + (w 12)
  let v573 := v572 + s.h
  let v574 := v573 + v570
  let v575 := v574 + v568
  let v576 := v575 + v567
  let v577 := s.a.rotateRight 28
  let v578 := s.a.rotateRight 34
  let v579 := v577 ^^^ v578
  let v580 := s.a.rotateRight 39
  let v581 := v579 ^^^ v580
  let v582 := s.a &&& s.b
  let v583 := s.b ^^^ s.c
  let v584 := s.a &&& v583
  let v585 := v584 ^^^ (s.b &&& s.c)
  let v586 := v581 + v585
  let v587 := v576 + s.d
  let v588 := v586 + v576
  E[%563 := .value v563,
    %564 := .value v564,
    %565 := .value v565,
    %566 := .value v566,
    %567 := .value v567,
    %568 := .value v568,
    %569 := .value v569,
    %570 := .value v570,
    %571 := .value v571,
    %572 := .value v572,
    %573 := .value v573,
    %574 := .value v574,
    %575 := .value v575,
    %576 := .value v576,
    %577 := .value v577,
    %578 := .value v578,
    %579 := .value v579,
    %580 := .value v580,
    %581 := .value v581,
    %582 := .value v582,
    %583 := .value v583,
    %584 := .value v584,
    %585 := .value v585,
    %586 := .value v586,
    %587 := .value v587,
    %588 := .value v588]

def fullOut12 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v563 := s.e.rotateRight 14
  let v564 := s.e.rotateRight 18
  let v565 := v563 ^^^ v564
  let v566 := s.e.rotateRight 41
  let v567 := v565 ^^^ v566
  let v568 := s.e &&& s.f
  let v569 := s.e ^^^ (-1 : Word)
  let v570 := s.g &&& v569
  let v571 := k
  let v572 := v571 + (w 12)
  let v573 := v572 + s.h
  let v574 := v573 + v570
  let v575 := v574 + v568
  let v576 := v575 + v567
  let v577 := s.a.rotateRight 28
  let v578 := s.a.rotateRight 34
  let v579 := v577 ^^^ v578
  let v580 := s.a.rotateRight 39
  let v581 := v579 ^^^ v580
  let v582 := s.a &&& s.b
  let v583 := s.b ^^^ s.c
  let v584 := s.a &&& v583
  let v585 := v584 ^^^ (s.b &&& s.c)
  let v586 := v581 + v585
  let v587 := v576 + s.d
  let v588 := v586 + v576
  ⟨v588, s.a, s.b, s.c, v587, s.e, s.f, s.g⟩

theorem fullOut12_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut12 s w k = Spec.round s (w 12) k := by
  dsimp only [fullOut12, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv12_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 563 E (fullEnv12 E s w k) := by
  unfold fullEnv12
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv12_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv12 E s w k) := by
  exact (fullEnv12_before E s w k).frame (by decide)

theorem full_body12 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready12 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 96#64) 64)
    (hk : state.mem.readAt (kp.add 96#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 363 |>.take 26) state =
      .value (fullEnv12 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv12, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k12, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready12 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready12 E s w) (hw : ScheduleReady w) :
    Ready13 (fullEnv12 E s w k) (Spec.round s (w 12) k) w := by
  have hb := fullEnv12_before E s w k
  have hout := fullOut12_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv12, fullOut12, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 562 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 536 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 510 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv12, fullOut12, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 561 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 535 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 509 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv12, Spec.round, mlir_env]
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

theorem full_step12 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready12 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 363 |>.take 26) state =
      .value (E', state) ∧
      Ready13 E' (Spec.round s (w 12) (constants.toList.getD 12 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 12 0
  have hf := fullEnv12_frame E s w k
  refine ⟨fullEnv12 E s w k,
    full_body12 E state s w kp k h hc (hk 12).1 (hk 12).2,
    full_ready12 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
