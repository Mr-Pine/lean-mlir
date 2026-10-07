import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 779..817: round 24. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv24 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v979 := (w 9).rotateRight 1
  let v980 := (w 9).rotateRight 8
  let v981 := v979 ^^^ v980
  let v982 := (w 9) >>> 7
  let v983 := v981 ^^^ v982
  let v984 := (w 22).rotateRight 19
  let v985 := (w 22).rotateRight 61
  let v986 := v984 ^^^ v985
  let v987 := (w 22) >>> 6
  let v988 := v986 ^^^ v987
  let v989 := v983 + (w 8)
  let v990 := v989 + (w 17)
  let v991 := v990 + v988
  let v992 := s.e.rotateRight 14
  let v993 := s.e.rotateRight 18
  let v994 := v992 ^^^ v993
  let v995 := s.e.rotateRight 41
  let v996 := v994 ^^^ v995
  let v997 := s.e &&& s.f
  let v998 := s.e ^^^ (-1 : Word)
  let v999 := s.g &&& v998
  let v1000 := v997 ||| v999
  let v1001 := k
  let v1002 := v1001 + v991
  let v1003 := v1002 + s.h
  let v1004 := v1003 + v1000
  let v1005 := v1004 + v996
  let v1006 := s.a.rotateRight 28
  let v1007 := s.a.rotateRight 34
  let v1008 := v1006 ^^^ v1007
  let v1009 := s.a.rotateRight 39
  let v1010 := v1008 ^^^ v1009
  let v1011 := s.a &&& s.b
  let v1012 := s.b ^^^ s.c
  let v1013 := s.a &&& v1012
  let v1014 := v1013 ^^^ (s.b &&& s.c)
  let v1015 := v1010 + v1014
  let v1016 := v1005 + s.d
  let v1017 := v1015 + v1005
  E[%979 := .value v979,
    %980 := .value v980,
    %981 := .value v981,
    %982 := .value v982,
    %983 := .value v983,
    %984 := .value v984,
    %985 := .value v985,
    %986 := .value v986,
    %987 := .value v987,
    %988 := .value v988,
    %989 := .value v989,
    %990 := .value v990,
    %991 := .value v991,
    %992 := .value v992,
    %993 := .value v993,
    %994 := .value v994,
    %995 := .value v995,
    %996 := .value v996,
    %997 := .value v997,
    %998 := .value v998,
    %999 := .value v999,
    %1000 := .value v1000,
    %1001 := .value v1001,
    %1002 := .value v1002,
    %1003 := .value v1003,
    %1004 := .value v1004,
    %1005 := .value v1005,
    %1006 := .value v1006,
    %1007 := .value v1007,
    %1008 := .value v1008,
    %1009 := .value v1009,
    %1010 := .value v1010,
    %1011 := .value v1011,
    %1012 := .value v1012,
    %1013 := .value v1013,
    %1014 := .value v1014,
    %1015 := .value v1015,
    %1016 := .value v1016,
    %1017 := .value v1017]

def fullOut24 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v979 := (w 9).rotateRight 1
  let v980 := (w 9).rotateRight 8
  let v981 := v979 ^^^ v980
  let v982 := (w 9) >>> 7
  let v983 := v981 ^^^ v982
  let v984 := (w 22).rotateRight 19
  let v985 := (w 22).rotateRight 61
  let v986 := v984 ^^^ v985
  let v987 := (w 22) >>> 6
  let v988 := v986 ^^^ v987
  let v989 := v983 + (w 8)
  let v990 := v989 + (w 17)
  let v991 := v990 + v988
  let v992 := s.e.rotateRight 14
  let v993 := s.e.rotateRight 18
  let v994 := v992 ^^^ v993
  let v995 := s.e.rotateRight 41
  let v996 := v994 ^^^ v995
  let v997 := s.e &&& s.f
  let v998 := s.e ^^^ (-1 : Word)
  let v999 := s.g &&& v998
  let v1000 := v997 ||| v999
  let v1001 := k
  let v1002 := v1001 + v991
  let v1003 := v1002 + s.h
  let v1004 := v1003 + v1000
  let v1005 := v1004 + v996
  let v1006 := s.a.rotateRight 28
  let v1007 := s.a.rotateRight 34
  let v1008 := v1006 ^^^ v1007
  let v1009 := s.a.rotateRight 39
  let v1010 := v1008 ^^^ v1009
  let v1011 := s.a &&& s.b
  let v1012 := s.b ^^^ s.c
  let v1013 := s.a &&& v1012
  let v1014 := v1013 ^^^ (s.b &&& s.c)
  let v1015 := v1010 + v1014
  let v1016 := v1005 + s.d
  let v1017 := v1015 + v1005
  ⟨v1017, s.a, s.b, s.c, v1016, s.e, s.f, s.g⟩

theorem fullOut24_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut24 s w k = Spec.round s (w 24) k := by
  have hw24 := hw 24 (by decide) (by decide)
  dsimp only [fullOut24, Spec.round]
  rw [hw24]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv24_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 979 E (fullEnv24 E s w k) := by
  unfold fullEnv24
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv24_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv24 E s w k) := by
  exact (fullEnv24_before E s w k).frame (by decide)

theorem full_body24 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready24 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 192#64) 64)
    (hk : state.mem.readAt (kp.add 192#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 779 |>.take 39) state =
      .value (fullEnv24 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv24, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k24, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready24 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready24 E s w) (hw : ScheduleReady w) :
    Ready25 (fullEnv24 E s w k) (Spec.round s (w 24) k) w := by
  have hb := fullEnv24_before E s w k
  have hout := fullOut24_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv24, fullOut24, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 978 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 939 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 900 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv24, fullOut24, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 977 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 938 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 899 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv24, Spec.round, mlir_env]
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
  · rw [hb.read_val 913 (by decide) (by rfl)]; exact h.w22
  · rw [hb.read_val 952 (by decide) (by rfl)]; exact h.w23
  · have hwr := hw 24 (by decide) (by decide)
    simp [fullEnv24, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step24 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready24 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 779 |>.take 39) state =
      .value (E', state) ∧
      Ready25 E' (Spec.round s (w 24) (constants.toList.getD 24 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 24 0
  have hf := fullEnv24_frame E s w k
  refine ⟨fullEnv24 E s w k,
    full_body24 E state s w kp k h hc (hk 24).1 (hk 24).2,
    full_ready24 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
