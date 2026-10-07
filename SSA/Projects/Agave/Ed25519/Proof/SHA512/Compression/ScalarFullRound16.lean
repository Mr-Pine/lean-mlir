import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 467..505: round 16. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv16 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v667 := (w 1).rotateRight 1
  let v668 := (w 1).rotateRight 8
  let v669 := v667 ^^^ v668
  let v670 := (w 1) >>> 7
  let v671 := v669 ^^^ v670
  let v672 := (w 14).rotateRight 19
  let v673 := (w 14).rotateRight 61
  let v674 := v672 ^^^ v673
  let v675 := (w 14) >>> 6
  let v676 := v674 ^^^ v675
  let v677 := v671 + (w 0)
  let v678 := v677 + (w 9)
  let v679 := v678 + v676
  let v680 := s.e.rotateRight 14
  let v681 := s.e.rotateRight 18
  let v682 := v680 ^^^ v681
  let v683 := s.e.rotateRight 41
  let v684 := v682 ^^^ v683
  let v685 := s.e &&& s.f
  let v686 := s.e ^^^ (-1 : Word)
  let v687 := s.g &&& v686
  let v688 := v685 ||| v687
  let v689 := k
  let v690 := v689 + v679
  let v691 := v690 + s.h
  let v692 := v691 + v688
  let v693 := v692 + v684
  let v694 := s.a.rotateRight 28
  let v695 := s.a.rotateRight 34
  let v696 := v694 ^^^ v695
  let v697 := s.a.rotateRight 39
  let v698 := v696 ^^^ v697
  let v699 := s.a &&& s.b
  let v700 := s.b ^^^ s.c
  let v701 := s.a &&& v700
  let v702 := v701 ^^^ (s.b &&& s.c)
  let v703 := v698 + v702
  let v704 := v693 + s.d
  let v705 := v703 + v693
  E[%667 := .value v667,
    %668 := .value v668,
    %669 := .value v669,
    %670 := .value v670,
    %671 := .value v671,
    %672 := .value v672,
    %673 := .value v673,
    %674 := .value v674,
    %675 := .value v675,
    %676 := .value v676,
    %677 := .value v677,
    %678 := .value v678,
    %679 := .value v679,
    %680 := .value v680,
    %681 := .value v681,
    %682 := .value v682,
    %683 := .value v683,
    %684 := .value v684,
    %685 := .value v685,
    %686 := .value v686,
    %687 := .value v687,
    %688 := .value v688,
    %689 := .value v689,
    %690 := .value v690,
    %691 := .value v691,
    %692 := .value v692,
    %693 := .value v693,
    %694 := .value v694,
    %695 := .value v695,
    %696 := .value v696,
    %697 := .value v697,
    %698 := .value v698,
    %699 := .value v699,
    %700 := .value v700,
    %701 := .value v701,
    %702 := .value v702,
    %703 := .value v703,
    %704 := .value v704,
    %705 := .value v705]

def fullOut16 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v667 := (w 1).rotateRight 1
  let v668 := (w 1).rotateRight 8
  let v669 := v667 ^^^ v668
  let v670 := (w 1) >>> 7
  let v671 := v669 ^^^ v670
  let v672 := (w 14).rotateRight 19
  let v673 := (w 14).rotateRight 61
  let v674 := v672 ^^^ v673
  let v675 := (w 14) >>> 6
  let v676 := v674 ^^^ v675
  let v677 := v671 + (w 0)
  let v678 := v677 + (w 9)
  let v679 := v678 + v676
  let v680 := s.e.rotateRight 14
  let v681 := s.e.rotateRight 18
  let v682 := v680 ^^^ v681
  let v683 := s.e.rotateRight 41
  let v684 := v682 ^^^ v683
  let v685 := s.e &&& s.f
  let v686 := s.e ^^^ (-1 : Word)
  let v687 := s.g &&& v686
  let v688 := v685 ||| v687
  let v689 := k
  let v690 := v689 + v679
  let v691 := v690 + s.h
  let v692 := v691 + v688
  let v693 := v692 + v684
  let v694 := s.a.rotateRight 28
  let v695 := s.a.rotateRight 34
  let v696 := v694 ^^^ v695
  let v697 := s.a.rotateRight 39
  let v698 := v696 ^^^ v697
  let v699 := s.a &&& s.b
  let v700 := s.b ^^^ s.c
  let v701 := s.a &&& v700
  let v702 := v701 ^^^ (s.b &&& s.c)
  let v703 := v698 + v702
  let v704 := v693 + s.d
  let v705 := v703 + v693
  ⟨v705, s.a, s.b, s.c, v704, s.e, s.f, s.g⟩

theorem fullOut16_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut16 s w k = Spec.round s (w 16) k := by
  have hw16 := hw 16 (by decide) (by decide)
  dsimp only [fullOut16, Spec.round]
  rw [hw16]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv16_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 667 E (fullEnv16 E s w k) := by
  unfold fullEnv16
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv16_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv16 E s w k) := by
  exact (fullEnv16_before E s w k).frame (by decide)

theorem full_body16 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready16 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 128#64) 64)
    (hk : state.mem.readAt (kp.add 128#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 467 |>.take 39) state =
      .value (fullEnv16 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv16, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k16, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready16 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready16 E s w) (hw : ScheduleReady w) :
    Ready17 (fullEnv16 E s w k) (Spec.round s (w 16) k) w := by
  have hb := fullEnv16_before E s w k
  have hout := fullOut16_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv16, fullOut16, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 666 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 640 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 614 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv16, fullOut16, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 665 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 639 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 613 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv16, Spec.round, mlir_env]
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
  · have hwr := hw 16 (by decide) (by decide)
    simp [fullEnv16, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step16 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready16 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 467 |>.take 39) state =
      .value (E', state) ∧
      Ready17 E' (Spec.round s (w 16) (constants.toList.getD 16 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 16 0
  have hf := fullEnv16_frame E s w k
  refine ⟨fullEnv16 E s w k,
    full_body16 E state s w kp k h hc (hk 16).1 (hk 16).2,
    full_ready16 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
