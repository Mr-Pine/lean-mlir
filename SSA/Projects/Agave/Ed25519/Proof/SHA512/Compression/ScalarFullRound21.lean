import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 662..700: round 21. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv21 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v862 := (w 6).rotateRight 1
  let v863 := (w 6).rotateRight 8
  let v864 := v862 ^^^ v863
  let v865 := (w 6) >>> 7
  let v866 := v864 ^^^ v865
  let v867 := (w 19).rotateRight 19
  let v868 := (w 19).rotateRight 61
  let v869 := v867 ^^^ v868
  let v870 := (w 19) >>> 6
  let v871 := v869 ^^^ v870
  let v872 := v866 + (w 5)
  let v873 := v872 + (w 14)
  let v874 := v873 + v871
  let v875 := s.e.rotateRight 14
  let v876 := s.e.rotateRight 18
  let v877 := v875 ^^^ v876
  let v878 := s.e.rotateRight 41
  let v879 := v877 ^^^ v878
  let v880 := s.e &&& s.f
  let v881 := s.e ^^^ (-1 : Word)
  let v882 := s.g &&& v881
  let v883 := v880 ||| v882
  let v884 := k
  let v885 := v884 + v874
  let v886 := v885 + s.h
  let v887 := v886 + v883
  let v888 := v887 + v879
  let v889 := s.a.rotateRight 28
  let v890 := s.a.rotateRight 34
  let v891 := v889 ^^^ v890
  let v892 := s.a.rotateRight 39
  let v893 := v891 ^^^ v892
  let v894 := s.a &&& s.b
  let v895 := s.b ^^^ s.c
  let v896 := s.a &&& v895
  let v897 := v896 ^^^ (s.b &&& s.c)
  let v898 := v893 + v897
  let v899 := v888 + s.d
  let v900 := v898 + v888
  E[%862 := .value v862,
    %863 := .value v863,
    %864 := .value v864,
    %865 := .value v865,
    %866 := .value v866,
    %867 := .value v867,
    %868 := .value v868,
    %869 := .value v869,
    %870 := .value v870,
    %871 := .value v871,
    %872 := .value v872,
    %873 := .value v873,
    %874 := .value v874,
    %875 := .value v875,
    %876 := .value v876,
    %877 := .value v877,
    %878 := .value v878,
    %879 := .value v879,
    %880 := .value v880,
    %881 := .value v881,
    %882 := .value v882,
    %883 := .value v883,
    %884 := .value v884,
    %885 := .value v885,
    %886 := .value v886,
    %887 := .value v887,
    %888 := .value v888,
    %889 := .value v889,
    %890 := .value v890,
    %891 := .value v891,
    %892 := .value v892,
    %893 := .value v893,
    %894 := .value v894,
    %895 := .value v895,
    %896 := .value v896,
    %897 := .value v897,
    %898 := .value v898,
    %899 := .value v899,
    %900 := .value v900]

def fullOut21 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v862 := (w 6).rotateRight 1
  let v863 := (w 6).rotateRight 8
  let v864 := v862 ^^^ v863
  let v865 := (w 6) >>> 7
  let v866 := v864 ^^^ v865
  let v867 := (w 19).rotateRight 19
  let v868 := (w 19).rotateRight 61
  let v869 := v867 ^^^ v868
  let v870 := (w 19) >>> 6
  let v871 := v869 ^^^ v870
  let v872 := v866 + (w 5)
  let v873 := v872 + (w 14)
  let v874 := v873 + v871
  let v875 := s.e.rotateRight 14
  let v876 := s.e.rotateRight 18
  let v877 := v875 ^^^ v876
  let v878 := s.e.rotateRight 41
  let v879 := v877 ^^^ v878
  let v880 := s.e &&& s.f
  let v881 := s.e ^^^ (-1 : Word)
  let v882 := s.g &&& v881
  let v883 := v880 ||| v882
  let v884 := k
  let v885 := v884 + v874
  let v886 := v885 + s.h
  let v887 := v886 + v883
  let v888 := v887 + v879
  let v889 := s.a.rotateRight 28
  let v890 := s.a.rotateRight 34
  let v891 := v889 ^^^ v890
  let v892 := s.a.rotateRight 39
  let v893 := v891 ^^^ v892
  let v894 := s.a &&& s.b
  let v895 := s.b ^^^ s.c
  let v896 := s.a &&& v895
  let v897 := v896 ^^^ (s.b &&& s.c)
  let v898 := v893 + v897
  let v899 := v888 + s.d
  let v900 := v898 + v888
  ⟨v900, s.a, s.b, s.c, v899, s.e, s.f, s.g⟩

theorem fullOut21_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut21 s w k = Spec.round s (w 21) k := by
  have hw21 := hw 21 (by decide) (by decide)
  dsimp only [fullOut21, Spec.round]
  rw [hw21]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv21_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 862 E (fullEnv21 E s w k) := by
  unfold fullEnv21
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv21_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv21 E s w k) := by
  exact (fullEnv21_before E s w k).frame (by decide)

theorem full_body21 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready21 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 168#64) 64)
    (hk : state.mem.readAt (kp.add 168#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 662 |>.take 39) state =
      .value (fullEnv21 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv21, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k21, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready21 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready21 E s w) (hw : ScheduleReady w) :
    Ready22 (fullEnv21 E s w k) (Spec.round s (w 21) k) w := by
  have hb := fullEnv21_before E s w k
  have hout := fullOut21_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv21, fullOut21, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 861 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 822 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 783 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv21, fullOut21, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 860 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 821 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 782 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv21, Spec.round, mlir_env]
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
  · rw [hb.read_val 835 (by decide) (by rfl)]; exact h.w20
  · have hwr := hw 21 (by decide) (by decide)
    simp [fullEnv21, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step21 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready21 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 662 |>.take 39) state =
      .value (E', state) ∧
      Ready22 E' (Spec.round s (w 21) (constants.toList.getD 21 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 21 0
  have hf := fullEnv21_frame E s w k
  refine ⟨fullEnv21 E s w k,
    full_body21 E state s w kp k h hc (hk 21).1 (hk 21).2,
    full_ready21 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
