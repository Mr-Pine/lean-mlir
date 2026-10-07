import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 701..739: round 22. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv22 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v901 := (w 7).rotateRight 1
  let v902 := (w 7).rotateRight 8
  let v903 := v901 ^^^ v902
  let v904 := (w 7) >>> 7
  let v905 := v903 ^^^ v904
  let v906 := (w 20).rotateRight 19
  let v907 := (w 20).rotateRight 61
  let v908 := v906 ^^^ v907
  let v909 := (w 20) >>> 6
  let v910 := v908 ^^^ v909
  let v911 := v905 + (w 6)
  let v912 := v911 + (w 15)
  let v913 := v912 + v910
  let v914 := s.e.rotateRight 14
  let v915 := s.e.rotateRight 18
  let v916 := v914 ^^^ v915
  let v917 := s.e.rotateRight 41
  let v918 := v916 ^^^ v917
  let v919 := s.e &&& s.f
  let v920 := s.e ^^^ (-1 : Word)
  let v921 := s.g &&& v920
  let v922 := v919 ||| v921
  let v923 := k
  let v924 := v923 + v913
  let v925 := v924 + s.h
  let v926 := v925 + v922
  let v927 := v926 + v918
  let v928 := s.a.rotateRight 28
  let v929 := s.a.rotateRight 34
  let v930 := v928 ^^^ v929
  let v931 := s.a.rotateRight 39
  let v932 := v930 ^^^ v931
  let v933 := s.a &&& s.b
  let v934 := s.b ^^^ s.c
  let v935 := s.a &&& v934
  let v936 := v935 ^^^ (s.b &&& s.c)
  let v937 := v932 + v936
  let v938 := v927 + s.d
  let v939 := v937 + v927
  E[%901 := .value v901,
    %902 := .value v902,
    %903 := .value v903,
    %904 := .value v904,
    %905 := .value v905,
    %906 := .value v906,
    %907 := .value v907,
    %908 := .value v908,
    %909 := .value v909,
    %910 := .value v910,
    %911 := .value v911,
    %912 := .value v912,
    %913 := .value v913,
    %914 := .value v914,
    %915 := .value v915,
    %916 := .value v916,
    %917 := .value v917,
    %918 := .value v918,
    %919 := .value v919,
    %920 := .value v920,
    %921 := .value v921,
    %922 := .value v922,
    %923 := .value v923,
    %924 := .value v924,
    %925 := .value v925,
    %926 := .value v926,
    %927 := .value v927,
    %928 := .value v928,
    %929 := .value v929,
    %930 := .value v930,
    %931 := .value v931,
    %932 := .value v932,
    %933 := .value v933,
    %934 := .value v934,
    %935 := .value v935,
    %936 := .value v936,
    %937 := .value v937,
    %938 := .value v938,
    %939 := .value v939]

def fullOut22 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v901 := (w 7).rotateRight 1
  let v902 := (w 7).rotateRight 8
  let v903 := v901 ^^^ v902
  let v904 := (w 7) >>> 7
  let v905 := v903 ^^^ v904
  let v906 := (w 20).rotateRight 19
  let v907 := (w 20).rotateRight 61
  let v908 := v906 ^^^ v907
  let v909 := (w 20) >>> 6
  let v910 := v908 ^^^ v909
  let v911 := v905 + (w 6)
  let v912 := v911 + (w 15)
  let v913 := v912 + v910
  let v914 := s.e.rotateRight 14
  let v915 := s.e.rotateRight 18
  let v916 := v914 ^^^ v915
  let v917 := s.e.rotateRight 41
  let v918 := v916 ^^^ v917
  let v919 := s.e &&& s.f
  let v920 := s.e ^^^ (-1 : Word)
  let v921 := s.g &&& v920
  let v922 := v919 ||| v921
  let v923 := k
  let v924 := v923 + v913
  let v925 := v924 + s.h
  let v926 := v925 + v922
  let v927 := v926 + v918
  let v928 := s.a.rotateRight 28
  let v929 := s.a.rotateRight 34
  let v930 := v928 ^^^ v929
  let v931 := s.a.rotateRight 39
  let v932 := v930 ^^^ v931
  let v933 := s.a &&& s.b
  let v934 := s.b ^^^ s.c
  let v935 := s.a &&& v934
  let v936 := v935 ^^^ (s.b &&& s.c)
  let v937 := v932 + v936
  let v938 := v927 + s.d
  let v939 := v937 + v927
  ⟨v939, s.a, s.b, s.c, v938, s.e, s.f, s.g⟩

theorem fullOut22_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut22 s w k = Spec.round s (w 22) k := by
  have hw22 := hw 22 (by decide) (by decide)
  dsimp only [fullOut22, Spec.round]
  rw [hw22]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv22_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 901 E (fullEnv22 E s w k) := by
  unfold fullEnv22
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv22_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv22 E s w k) := by
  exact (fullEnv22_before E s w k).frame (by decide)

theorem full_body22 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready22 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 176#64) 64)
    (hk : state.mem.readAt (kp.add 176#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 701 |>.take 39) state =
      .value (fullEnv22 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv22, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k22, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready22 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready22 E s w) (hw : ScheduleReady w) :
    Ready23 (fullEnv22 E s w k) (Spec.round s (w 22) k) w := by
  have hb := fullEnv22_before E s w k
  have hout := fullOut22_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv22, fullOut22, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 900 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 861 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 822 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv22, fullOut22, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 899 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 860 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 821 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv22, Spec.round, mlir_env]
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
  · rw [hb.read_val 874 (by decide) (by rfl)]; exact h.w21
  · have hwr := hw 22 (by decide) (by decide)
    simp [fullEnv22, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step22 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready22 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 701 |>.take 39) state =
      .value (E', state) ∧
      Ready23 E' (Spec.round s (w 22) (constants.toList.getD 22 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 22 0
  have hf := fullEnv22_frame E s w k
  refine ⟨fullEnv22 E s w k,
    full_body22 E state s w kp k h hc (hk 22).1 (hk 22).2,
    full_ready22 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
