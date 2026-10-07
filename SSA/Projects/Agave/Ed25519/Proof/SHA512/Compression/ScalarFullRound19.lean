import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 584..622: round 19. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv19 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v784 := (w 4).rotateRight 1
  let v785 := (w 4).rotateRight 8
  let v786 := v784 ^^^ v785
  let v787 := (w 4) >>> 7
  let v788 := v786 ^^^ v787
  let v789 := (w 17).rotateRight 19
  let v790 := (w 17).rotateRight 61
  let v791 := v789 ^^^ v790
  let v792 := (w 17) >>> 6
  let v793 := v791 ^^^ v792
  let v794 := v788 + (w 3)
  let v795 := v794 + (w 12)
  let v796 := v795 + v793
  let v797 := s.e.rotateRight 14
  let v798 := s.e.rotateRight 18
  let v799 := v797 ^^^ v798
  let v800 := s.e.rotateRight 41
  let v801 := v799 ^^^ v800
  let v802 := s.e &&& s.f
  let v803 := s.e ^^^ (-1 : Word)
  let v804 := s.g &&& v803
  let v805 := v802 ||| v804
  let v806 := k
  let v807 := v806 + v796
  let v808 := v807 + s.h
  let v809 := v808 + v805
  let v810 := v809 + v801
  let v811 := s.a.rotateRight 28
  let v812 := s.a.rotateRight 34
  let v813 := v811 ^^^ v812
  let v814 := s.a.rotateRight 39
  let v815 := v813 ^^^ v814
  let v816 := s.a &&& s.b
  let v817 := s.b ^^^ s.c
  let v818 := s.a &&& v817
  let v819 := v818 ^^^ (s.b &&& s.c)
  let v820 := v815 + v819
  let v821 := v810 + s.d
  let v822 := v820 + v810
  E[%784 := .value v784,
    %785 := .value v785,
    %786 := .value v786,
    %787 := .value v787,
    %788 := .value v788,
    %789 := .value v789,
    %790 := .value v790,
    %791 := .value v791,
    %792 := .value v792,
    %793 := .value v793,
    %794 := .value v794,
    %795 := .value v795,
    %796 := .value v796,
    %797 := .value v797,
    %798 := .value v798,
    %799 := .value v799,
    %800 := .value v800,
    %801 := .value v801,
    %802 := .value v802,
    %803 := .value v803,
    %804 := .value v804,
    %805 := .value v805,
    %806 := .value v806,
    %807 := .value v807,
    %808 := .value v808,
    %809 := .value v809,
    %810 := .value v810,
    %811 := .value v811,
    %812 := .value v812,
    %813 := .value v813,
    %814 := .value v814,
    %815 := .value v815,
    %816 := .value v816,
    %817 := .value v817,
    %818 := .value v818,
    %819 := .value v819,
    %820 := .value v820,
    %821 := .value v821,
    %822 := .value v822]

def fullOut19 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v784 := (w 4).rotateRight 1
  let v785 := (w 4).rotateRight 8
  let v786 := v784 ^^^ v785
  let v787 := (w 4) >>> 7
  let v788 := v786 ^^^ v787
  let v789 := (w 17).rotateRight 19
  let v790 := (w 17).rotateRight 61
  let v791 := v789 ^^^ v790
  let v792 := (w 17) >>> 6
  let v793 := v791 ^^^ v792
  let v794 := v788 + (w 3)
  let v795 := v794 + (w 12)
  let v796 := v795 + v793
  let v797 := s.e.rotateRight 14
  let v798 := s.e.rotateRight 18
  let v799 := v797 ^^^ v798
  let v800 := s.e.rotateRight 41
  let v801 := v799 ^^^ v800
  let v802 := s.e &&& s.f
  let v803 := s.e ^^^ (-1 : Word)
  let v804 := s.g &&& v803
  let v805 := v802 ||| v804
  let v806 := k
  let v807 := v806 + v796
  let v808 := v807 + s.h
  let v809 := v808 + v805
  let v810 := v809 + v801
  let v811 := s.a.rotateRight 28
  let v812 := s.a.rotateRight 34
  let v813 := v811 ^^^ v812
  let v814 := s.a.rotateRight 39
  let v815 := v813 ^^^ v814
  let v816 := s.a &&& s.b
  let v817 := s.b ^^^ s.c
  let v818 := s.a &&& v817
  let v819 := v818 ^^^ (s.b &&& s.c)
  let v820 := v815 + v819
  let v821 := v810 + s.d
  let v822 := v820 + v810
  ⟨v822, s.a, s.b, s.c, v821, s.e, s.f, s.g⟩

theorem fullOut19_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut19 s w k = Spec.round s (w 19) k := by
  have hw19 := hw 19 (by decide) (by decide)
  dsimp only [fullOut19, Spec.round]
  rw [hw19]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv19_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 784 E (fullEnv19 E s w k) := by
  unfold fullEnv19
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv19_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv19 E s w k) := by
  exact (fullEnv19_before E s w k).frame (by decide)

theorem full_body19 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready19 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 152#64) 64)
    (hk : state.mem.readAt (kp.add 152#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 584 |>.take 39) state =
      .value (fullEnv19 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv19, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k19, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready19 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready19 E s w) (hw : ScheduleReady w) :
    Ready20 (fullEnv19 E s w k) (Spec.round s (w 19) k) w := by
  have hb := fullEnv19_before E s w k
  have hout := fullOut19_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv19, fullOut19, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 783 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 744 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 705 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv19, fullOut19, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 782 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 743 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 704 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv19, Spec.round, mlir_env]
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
  · rw [hb.read_val 757 (by decide) (by rfl)]; exact h.w18
  · have hwr := hw 19 (by decide) (by decide)
    simp [fullEnv19, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step19 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready19 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 584 |>.take 39) state =
      .value (E', state) ∧
      Ready20 E' (Spec.round s (w 19) (constants.toList.getD 19 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 19 0
  have hf := fullEnv19_frame E s w k
  refine ⟨fullEnv19 E s w k,
    full_body19 E state s w kp k h hc (hk 19).1 (hk 19).2,
    full_ready19 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
