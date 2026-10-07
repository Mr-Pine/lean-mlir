import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 818..856: round 25. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv25 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v1018 := (w 10).rotateRight 1
  let v1019 := (w 10).rotateRight 8
  let v1020 := v1018 ^^^ v1019
  let v1021 := (w 10) >>> 7
  let v1022 := v1020 ^^^ v1021
  let v1023 := (w 23).rotateRight 19
  let v1024 := (w 23).rotateRight 61
  let v1025 := v1023 ^^^ v1024
  let v1026 := (w 23) >>> 6
  let v1027 := v1025 ^^^ v1026
  let v1028 := v1022 + (w 9)
  let v1029 := v1028 + (w 18)
  let v1030 := v1029 + v1027
  let v1031 := s.e.rotateRight 14
  let v1032 := s.e.rotateRight 18
  let v1033 := v1031 ^^^ v1032
  let v1034 := s.e.rotateRight 41
  let v1035 := v1033 ^^^ v1034
  let v1036 := s.e &&& s.f
  let v1037 := s.e ^^^ (-1 : Word)
  let v1038 := s.g &&& v1037
  let v1039 := v1036 ||| v1038
  let v1040 := k
  let v1041 := v1040 + v1030
  let v1042 := v1041 + s.h
  let v1043 := v1042 + v1039
  let v1044 := v1043 + v1035
  let v1045 := s.a.rotateRight 28
  let v1046 := s.a.rotateRight 34
  let v1047 := v1045 ^^^ v1046
  let v1048 := s.a.rotateRight 39
  let v1049 := v1047 ^^^ v1048
  let v1050 := s.a &&& s.b
  let v1051 := s.b ^^^ s.c
  let v1052 := s.a &&& v1051
  let v1053 := v1052 ^^^ (s.b &&& s.c)
  let v1054 := v1049 + v1053
  let v1055 := v1044 + s.d
  let v1056 := v1054 + v1044
  E[%1018 := .value v1018,
    %1019 := .value v1019,
    %1020 := .value v1020,
    %1021 := .value v1021,
    %1022 := .value v1022,
    %1023 := .value v1023,
    %1024 := .value v1024,
    %1025 := .value v1025,
    %1026 := .value v1026,
    %1027 := .value v1027,
    %1028 := .value v1028,
    %1029 := .value v1029,
    %1030 := .value v1030,
    %1031 := .value v1031,
    %1032 := .value v1032,
    %1033 := .value v1033,
    %1034 := .value v1034,
    %1035 := .value v1035,
    %1036 := .value v1036,
    %1037 := .value v1037,
    %1038 := .value v1038,
    %1039 := .value v1039,
    %1040 := .value v1040,
    %1041 := .value v1041,
    %1042 := .value v1042,
    %1043 := .value v1043,
    %1044 := .value v1044,
    %1045 := .value v1045,
    %1046 := .value v1046,
    %1047 := .value v1047,
    %1048 := .value v1048,
    %1049 := .value v1049,
    %1050 := .value v1050,
    %1051 := .value v1051,
    %1052 := .value v1052,
    %1053 := .value v1053,
    %1054 := .value v1054,
    %1055 := .value v1055,
    %1056 := .value v1056]

def fullOut25 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v1018 := (w 10).rotateRight 1
  let v1019 := (w 10).rotateRight 8
  let v1020 := v1018 ^^^ v1019
  let v1021 := (w 10) >>> 7
  let v1022 := v1020 ^^^ v1021
  let v1023 := (w 23).rotateRight 19
  let v1024 := (w 23).rotateRight 61
  let v1025 := v1023 ^^^ v1024
  let v1026 := (w 23) >>> 6
  let v1027 := v1025 ^^^ v1026
  let v1028 := v1022 + (w 9)
  let v1029 := v1028 + (w 18)
  let v1030 := v1029 + v1027
  let v1031 := s.e.rotateRight 14
  let v1032 := s.e.rotateRight 18
  let v1033 := v1031 ^^^ v1032
  let v1034 := s.e.rotateRight 41
  let v1035 := v1033 ^^^ v1034
  let v1036 := s.e &&& s.f
  let v1037 := s.e ^^^ (-1 : Word)
  let v1038 := s.g &&& v1037
  let v1039 := v1036 ||| v1038
  let v1040 := k
  let v1041 := v1040 + v1030
  let v1042 := v1041 + s.h
  let v1043 := v1042 + v1039
  let v1044 := v1043 + v1035
  let v1045 := s.a.rotateRight 28
  let v1046 := s.a.rotateRight 34
  let v1047 := v1045 ^^^ v1046
  let v1048 := s.a.rotateRight 39
  let v1049 := v1047 ^^^ v1048
  let v1050 := s.a &&& s.b
  let v1051 := s.b ^^^ s.c
  let v1052 := s.a &&& v1051
  let v1053 := v1052 ^^^ (s.b &&& s.c)
  let v1054 := v1049 + v1053
  let v1055 := v1044 + s.d
  let v1056 := v1054 + v1044
  ⟨v1056, s.a, s.b, s.c, v1055, s.e, s.f, s.g⟩

theorem fullOut25_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut25 s w k = Spec.round s (w 25) k := by
  have hw25 := hw 25 (by decide) (by decide)
  dsimp only [fullOut25, Spec.round]
  rw [hw25]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv25_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 1018 E (fullEnv25 E s w k) := by
  unfold fullEnv25
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv25_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv25 E s w k) := by
  exact (fullEnv25_before E s w k).frame (by decide)

theorem full_body25 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready25 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 200#64) 64)
    (hk : state.mem.readAt (kp.add 200#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 818 |>.take 39) state =
      .value (fullEnv25 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv25, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, h.w23, h.w24, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k25, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready25 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready25 E s w) (hw : ScheduleReady w) :
    Ready26 (fullEnv25 E s w k) (Spec.round s (w 25) k) w := by
  have hb := fullEnv25_before E s w k
  have hout := fullOut25_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv25, fullOut25, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 1017 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 978 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 939 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv25, fullOut25, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 1016 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 977 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 938 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv25, Spec.round, mlir_env]
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
  · rw [hb.read_val 991 (by decide) (by rfl)]; exact h.w24
  · have hwr := hw 25 (by decide) (by decide)
    simp [fullEnv25, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step25 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready25 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 818 |>.take 39) state =
      .value (E', state) ∧
      Ready26 E' (Spec.round s (w 25) (constants.toList.getD 25 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 25 0
  have hf := fullEnv25_frame E s w k
  refine ⟨fullEnv25 E s w k,
    full_body25 E state s w kp k h hc (hk 25).1 (hk 25).2,
    full_ready25 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
