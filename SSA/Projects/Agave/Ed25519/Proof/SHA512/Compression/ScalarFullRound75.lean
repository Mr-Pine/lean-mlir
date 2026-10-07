import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 2768..2806: round 75. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv75 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v2968 := (w 60).rotateRight 1
  let v2969 := (w 60).rotateRight 8
  let v2970 := v2968 ^^^ v2969
  let v2971 := (w 60) >>> 7
  let v2972 := v2970 ^^^ v2971
  let v2973 := (w 73).rotateRight 19
  let v2974 := (w 73).rotateRight 61
  let v2975 := v2973 ^^^ v2974
  let v2976 := (w 73) >>> 6
  let v2977 := v2975 ^^^ v2976
  let v2978 := v2972 + (w 59)
  let v2979 := v2978 + (w 68)
  let v2980 := v2979 + v2977
  let v2981 := s.e.rotateRight 14
  let v2982 := s.e.rotateRight 18
  let v2983 := v2981 ^^^ v2982
  let v2984 := s.e.rotateRight 41
  let v2985 := v2983 ^^^ v2984
  let v2986 := s.e &&& s.f
  let v2987 := s.e ^^^ (-1 : Word)
  let v2988 := s.g &&& v2987
  let v2989 := v2986 ||| v2988
  let v2990 := k
  let v2991 := v2980 + v2990
  let v2992 := v2991 + s.h
  let v2993 := v2992 + v2989
  let v2994 := v2993 + v2985
  let v2995 := s.a.rotateRight 28
  let v2996 := s.a.rotateRight 34
  let v2997 := v2995 ^^^ v2996
  let v2998 := s.a.rotateRight 39
  let v2999 := v2997 ^^^ v2998
  let v3000 := s.a &&& s.b
  let v3001 := s.b ^^^ s.c
  let v3002 := s.a &&& v3001
  let v3003 := v3002 ^^^ (s.b &&& s.c)
  let v3004 := v2999 + v3003
  let v3005 := v2994 + s.d
  let v3006 := v3004 + v2994
  E[%2968 := .value v2968,
    %2969 := .value v2969,
    %2970 := .value v2970,
    %2971 := .value v2971,
    %2972 := .value v2972,
    %2973 := .value v2973,
    %2974 := .value v2974,
    %2975 := .value v2975,
    %2976 := .value v2976,
    %2977 := .value v2977,
    %2978 := .value v2978,
    %2979 := .value v2979,
    %2980 := .value v2980,
    %2981 := .value v2981,
    %2982 := .value v2982,
    %2983 := .value v2983,
    %2984 := .value v2984,
    %2985 := .value v2985,
    %2986 := .value v2986,
    %2987 := .value v2987,
    %2988 := .value v2988,
    %2989 := .value v2989,
    %2990 := .value v2990,
    %2991 := .value v2991,
    %2992 := .value v2992,
    %2993 := .value v2993,
    %2994 := .value v2994,
    %2995 := .value v2995,
    %2996 := .value v2996,
    %2997 := .value v2997,
    %2998 := .value v2998,
    %2999 := .value v2999,
    %3000 := .value v3000,
    %3001 := .value v3001,
    %3002 := .value v3002,
    %3003 := .value v3003,
    %3004 := .value v3004,
    %3005 := .value v3005,
    %3006 := .value v3006]

def fullOut75 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v2968 := (w 60).rotateRight 1
  let v2969 := (w 60).rotateRight 8
  let v2970 := v2968 ^^^ v2969
  let v2971 := (w 60) >>> 7
  let v2972 := v2970 ^^^ v2971
  let v2973 := (w 73).rotateRight 19
  let v2974 := (w 73).rotateRight 61
  let v2975 := v2973 ^^^ v2974
  let v2976 := (w 73) >>> 6
  let v2977 := v2975 ^^^ v2976
  let v2978 := v2972 + (w 59)
  let v2979 := v2978 + (w 68)
  let v2980 := v2979 + v2977
  let v2981 := s.e.rotateRight 14
  let v2982 := s.e.rotateRight 18
  let v2983 := v2981 ^^^ v2982
  let v2984 := s.e.rotateRight 41
  let v2985 := v2983 ^^^ v2984
  let v2986 := s.e &&& s.f
  let v2987 := s.e ^^^ (-1 : Word)
  let v2988 := s.g &&& v2987
  let v2989 := v2986 ||| v2988
  let v2990 := k
  let v2991 := v2980 + v2990
  let v2992 := v2991 + s.h
  let v2993 := v2992 + v2989
  let v2994 := v2993 + v2985
  let v2995 := s.a.rotateRight 28
  let v2996 := s.a.rotateRight 34
  let v2997 := v2995 ^^^ v2996
  let v2998 := s.a.rotateRight 39
  let v2999 := v2997 ^^^ v2998
  let v3000 := s.a &&& s.b
  let v3001 := s.b ^^^ s.c
  let v3002 := s.a &&& v3001
  let v3003 := v3002 ^^^ (s.b &&& s.c)
  let v3004 := v2999 + v3003
  let v3005 := v2994 + s.d
  let v3006 := v3004 + v2994
  ⟨v3006, s.a, s.b, s.c, v3005, s.e, s.f, s.g⟩

theorem fullOut75_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut75 s w k = Spec.round s (w 75) k := by
  have hw75 := hw 75 (by decide) (by decide)
  dsimp only [fullOut75, Spec.round]
  rw [hw75]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv75_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 2968 E (fullEnv75 E s w k) := by
  unfold fullEnv75
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv75_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv75 E s w k) := by
  exact (fullEnv75_before E s w k).frame (by decide)

theorem full_body75 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready75 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 600#64) 64)
    (hk : state.mem.readAt (kp.add 600#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 2768 |>.take 39) state =
      .value (fullEnv75 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv75, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w59, h.w60, h.w61, h.w62, h.w63, h.w64, h.w68, h.w69, h.w70, h.w71, h.w72, h.w73, h.w74, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k75, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready75 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready75 E s w) (hw : ScheduleReady w) :
    Ready76 (fullEnv75 E s w k) (Spec.round s (w 75) k) w := by
  have hb := fullEnv75_before E s w k
  have hout := fullOut75_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv75, fullOut75, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 2967 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 2928 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 2889 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv75, fullOut75, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 2966 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 2927 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 2888 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv75, Spec.round, mlir_env]
  · rw [hb.read_val 2395 (by decide) (by rfl)]; exact h.w60
  · rw [hb.read_val 2434 (by decide) (by rfl)]; exact h.w61
  · rw [hb.read_val 2473 (by decide) (by rfl)]; exact h.w62
  · rw [hb.read_val 2512 (by decide) (by rfl)]; exact h.w63
  · rw [hb.read_val 2551 (by decide) (by rfl)]; exact h.w64
  · rw [hb.read_val 2746 (by decide) (by rfl)]; exact h.w69
  · rw [hb.read_val 2785 (by decide) (by rfl)]; exact h.w70
  · rw [hb.read_val 2824 (by decide) (by rfl)]; exact h.w71
  · rw [hb.read_val 2863 (by decide) (by rfl)]; exact h.w72
  · rw [hb.read_val 2941 (by decide) (by rfl)]; exact h.w74
  · have hwr := hw 75 (by decide) (by decide)
    simp [fullEnv75, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step75 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready75 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 2768 |>.take 39) state =
      .value (E', state) ∧
      Ready76 E' (Spec.round s (w 75) (constants.toList.getD 75 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 75 0
  have hf := fullEnv75_frame E s w k
  refine ⟨fullEnv75 E s w k,
    full_body75 E state s w kp k h hc (hk 75).1 (hk 75).2,
    full_ready75 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
