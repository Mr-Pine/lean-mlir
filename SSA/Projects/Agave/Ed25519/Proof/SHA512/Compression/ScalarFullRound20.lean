import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 623..661: round 20. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv20 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v823 := (w 5).rotateRight 1
  let v824 := (w 5).rotateRight 8
  let v825 := v823 ^^^ v824
  let v826 := (w 5) >>> 7
  let v827 := v825 ^^^ v826
  let v828 := (w 18).rotateRight 19
  let v829 := (w 18).rotateRight 61
  let v830 := v828 ^^^ v829
  let v831 := (w 18) >>> 6
  let v832 := v830 ^^^ v831
  let v833 := v827 + (w 4)
  let v834 := v833 + (w 13)
  let v835 := v834 + v832
  let v836 := s.e.rotateRight 14
  let v837 := s.e.rotateRight 18
  let v838 := v836 ^^^ v837
  let v839 := s.e.rotateRight 41
  let v840 := v838 ^^^ v839
  let v841 := s.e &&& s.f
  let v842 := s.e ^^^ (-1 : Word)
  let v843 := s.g &&& v842
  let v844 := v841 ||| v843
  let v845 := k
  let v846 := v845 + v835
  let v847 := v846 + s.h
  let v848 := v847 + v844
  let v849 := v848 + v840
  let v850 := s.a.rotateRight 28
  let v851 := s.a.rotateRight 34
  let v852 := v850 ^^^ v851
  let v853 := s.a.rotateRight 39
  let v854 := v852 ^^^ v853
  let v855 := s.a &&& s.b
  let v856 := s.b ^^^ s.c
  let v857 := s.a &&& v856
  let v858 := v857 ^^^ (s.b &&& s.c)
  let v859 := v854 + v858
  let v860 := v849 + s.d
  let v861 := v859 + v849
  E[%823 := .value v823,
    %824 := .value v824,
    %825 := .value v825,
    %826 := .value v826,
    %827 := .value v827,
    %828 := .value v828,
    %829 := .value v829,
    %830 := .value v830,
    %831 := .value v831,
    %832 := .value v832,
    %833 := .value v833,
    %834 := .value v834,
    %835 := .value v835,
    %836 := .value v836,
    %837 := .value v837,
    %838 := .value v838,
    %839 := .value v839,
    %840 := .value v840,
    %841 := .value v841,
    %842 := .value v842,
    %843 := .value v843,
    %844 := .value v844,
    %845 := .value v845,
    %846 := .value v846,
    %847 := .value v847,
    %848 := .value v848,
    %849 := .value v849,
    %850 := .value v850,
    %851 := .value v851,
    %852 := .value v852,
    %853 := .value v853,
    %854 := .value v854,
    %855 := .value v855,
    %856 := .value v856,
    %857 := .value v857,
    %858 := .value v858,
    %859 := .value v859,
    %860 := .value v860,
    %861 := .value v861]

def fullOut20 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v823 := (w 5).rotateRight 1
  let v824 := (w 5).rotateRight 8
  let v825 := v823 ^^^ v824
  let v826 := (w 5) >>> 7
  let v827 := v825 ^^^ v826
  let v828 := (w 18).rotateRight 19
  let v829 := (w 18).rotateRight 61
  let v830 := v828 ^^^ v829
  let v831 := (w 18) >>> 6
  let v832 := v830 ^^^ v831
  let v833 := v827 + (w 4)
  let v834 := v833 + (w 13)
  let v835 := v834 + v832
  let v836 := s.e.rotateRight 14
  let v837 := s.e.rotateRight 18
  let v838 := v836 ^^^ v837
  let v839 := s.e.rotateRight 41
  let v840 := v838 ^^^ v839
  let v841 := s.e &&& s.f
  let v842 := s.e ^^^ (-1 : Word)
  let v843 := s.g &&& v842
  let v844 := v841 ||| v843
  let v845 := k
  let v846 := v845 + v835
  let v847 := v846 + s.h
  let v848 := v847 + v844
  let v849 := v848 + v840
  let v850 := s.a.rotateRight 28
  let v851 := s.a.rotateRight 34
  let v852 := v850 ^^^ v851
  let v853 := s.a.rotateRight 39
  let v854 := v852 ^^^ v853
  let v855 := s.a &&& s.b
  let v856 := s.b ^^^ s.c
  let v857 := s.a &&& v856
  let v858 := v857 ^^^ (s.b &&& s.c)
  let v859 := v854 + v858
  let v860 := v849 + s.d
  let v861 := v859 + v849
  ⟨v861, s.a, s.b, s.c, v860, s.e, s.f, s.g⟩

theorem fullOut20_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut20 s w k = Spec.round s (w 20) k := by
  have hw20 := hw 20 (by decide) (by decide)
  dsimp only [fullOut20, Spec.round]
  rw [hw20]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv20_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 823 E (fullEnv20 E s w k) := by
  unfold fullEnv20
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv20_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv20 E s w k) := by
  exact (fullEnv20_before E s w k).frame (by decide)

theorem full_body20 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready20 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 160#64) 64)
    (hk : state.mem.readAt (kp.add 160#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 623 |>.take 39) state =
      .value (fullEnv20 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv20, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k20, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready20 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready20 E s w) (hw : ScheduleReady w) :
    Ready21 (fullEnv20 E s w k) (Spec.round s (w 20) k) w := by
  have hb := fullEnv20_before E s w k
  have hout := fullOut20_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv20, fullOut20, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 822 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 783 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 744 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv20, fullOut20, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 821 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 782 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 743 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv20, Spec.round, mlir_env]
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
  · rw [hb.read_val 796 (by decide) (by rfl)]; exact h.w19
  · have hwr := hw 20 (by decide) (by decide)
    simp [fullEnv20, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step20 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready20 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 623 |>.take 39) state =
      .value (E', state) ∧
      Ready21 E' (Spec.round s (w 20) (constants.toList.getD 20 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 20 0
  have hf := fullEnv20_frame E s w k
  refine ⟨fullEnv20 E s w k,
    full_body20 E state s w kp k h hc (hk 20).1 (hk 20).2,
    full_ready20 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
