import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 545..583: round 18. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv18 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v745 := (w 3).rotateRight 1
  let v746 := (w 3).rotateRight 8
  let v747 := v745 ^^^ v746
  let v748 := (w 3) >>> 7
  let v749 := v747 ^^^ v748
  let v750 := (w 16).rotateRight 19
  let v751 := (w 16).rotateRight 61
  let v752 := v750 ^^^ v751
  let v753 := (w 16) >>> 6
  let v754 := v752 ^^^ v753
  let v755 := v749 + (w 2)
  let v756 := v755 + (w 11)
  let v757 := v756 + v754
  let v758 := s.e.rotateRight 14
  let v759 := s.e.rotateRight 18
  let v760 := v758 ^^^ v759
  let v761 := s.e.rotateRight 41
  let v762 := v760 ^^^ v761
  let v763 := s.e &&& s.f
  let v764 := s.e ^^^ (-1 : Word)
  let v765 := s.g &&& v764
  let v766 := v763 ||| v765
  let v767 := k
  let v768 := v767 + v757
  let v769 := v768 + s.h
  let v770 := v769 + v766
  let v771 := v770 + v762
  let v772 := s.a.rotateRight 28
  let v773 := s.a.rotateRight 34
  let v774 := v772 ^^^ v773
  let v775 := s.a.rotateRight 39
  let v776 := v774 ^^^ v775
  let v777 := s.a &&& s.b
  let v778 := s.b ^^^ s.c
  let v779 := s.a &&& v778
  let v780 := v779 ^^^ (s.b &&& s.c)
  let v781 := v776 + v780
  let v782 := v771 + s.d
  let v783 := v781 + v771
  E[%745 := .value v745,
    %746 := .value v746,
    %747 := .value v747,
    %748 := .value v748,
    %749 := .value v749,
    %750 := .value v750,
    %751 := .value v751,
    %752 := .value v752,
    %753 := .value v753,
    %754 := .value v754,
    %755 := .value v755,
    %756 := .value v756,
    %757 := .value v757,
    %758 := .value v758,
    %759 := .value v759,
    %760 := .value v760,
    %761 := .value v761,
    %762 := .value v762,
    %763 := .value v763,
    %764 := .value v764,
    %765 := .value v765,
    %766 := .value v766,
    %767 := .value v767,
    %768 := .value v768,
    %769 := .value v769,
    %770 := .value v770,
    %771 := .value v771,
    %772 := .value v772,
    %773 := .value v773,
    %774 := .value v774,
    %775 := .value v775,
    %776 := .value v776,
    %777 := .value v777,
    %778 := .value v778,
    %779 := .value v779,
    %780 := .value v780,
    %781 := .value v781,
    %782 := .value v782,
    %783 := .value v783]

def fullOut18 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v745 := (w 3).rotateRight 1
  let v746 := (w 3).rotateRight 8
  let v747 := v745 ^^^ v746
  let v748 := (w 3) >>> 7
  let v749 := v747 ^^^ v748
  let v750 := (w 16).rotateRight 19
  let v751 := (w 16).rotateRight 61
  let v752 := v750 ^^^ v751
  let v753 := (w 16) >>> 6
  let v754 := v752 ^^^ v753
  let v755 := v749 + (w 2)
  let v756 := v755 + (w 11)
  let v757 := v756 + v754
  let v758 := s.e.rotateRight 14
  let v759 := s.e.rotateRight 18
  let v760 := v758 ^^^ v759
  let v761 := s.e.rotateRight 41
  let v762 := v760 ^^^ v761
  let v763 := s.e &&& s.f
  let v764 := s.e ^^^ (-1 : Word)
  let v765 := s.g &&& v764
  let v766 := v763 ||| v765
  let v767 := k
  let v768 := v767 + v757
  let v769 := v768 + s.h
  let v770 := v769 + v766
  let v771 := v770 + v762
  let v772 := s.a.rotateRight 28
  let v773 := s.a.rotateRight 34
  let v774 := v772 ^^^ v773
  let v775 := s.a.rotateRight 39
  let v776 := v774 ^^^ v775
  let v777 := s.a &&& s.b
  let v778 := s.b ^^^ s.c
  let v779 := s.a &&& v778
  let v780 := v779 ^^^ (s.b &&& s.c)
  let v781 := v776 + v780
  let v782 := v771 + s.d
  let v783 := v781 + v771
  ⟨v783, s.a, s.b, s.c, v782, s.e, s.f, s.g⟩

theorem fullOut18_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut18 s w k = Spec.round s (w 18) k := by
  have hw18 := hw 18 (by decide) (by decide)
  dsimp only [fullOut18, Spec.round]
  rw [hw18]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv18_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 745 E (fullEnv18 E s w k) := by
  unfold fullEnv18
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv18_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv18 E s w k) := by
  exact (fullEnv18_before E s w k).frame (by decide)

theorem full_body18 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready18 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 144#64) 64)
    (hk : state.mem.readAt (kp.add 144#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 545 |>.take 39) state =
      .value (fullEnv18 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv18, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k18, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready18 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready18 E s w) (hw : ScheduleReady w) :
    Ready19 (fullEnv18 E s w k) (Spec.round s (w 18) k) w := by
  have hb := fullEnv18_before E s w k
  have hout := fullOut18_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv18, fullOut18, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 744 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 705 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 666 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv18, fullOut18, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 743 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 704 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 665 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv18, Spec.round, mlir_env]
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
  · rw [hb.read_val 679 (by decide) (by rfl)]; exact h.w16
  · rw [hb.read_val 718 (by decide) (by rfl)]; exact h.w17
  · have hwr := hw 18 (by decide) (by decide)
    simp [fullEnv18, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step18 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready18 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 545 |>.take 39) state =
      .value (E', state) ∧
      Ready19 E' (Spec.round s (w 18) (constants.toList.getD 18 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 18 0
  have hf := fullEnv18_frame E s w k
  refine ⟨fullEnv18 E s w k,
    full_body18 E state s w kp k h hc (hk 18).1 (hk 18).2,
    full_ready18 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
