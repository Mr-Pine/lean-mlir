import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 740..778: round 23. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv23 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v940 := (w 8).rotateRight 1
  let v941 := (w 8).rotateRight 8
  let v942 := v940 ^^^ v941
  let v943 := (w 8) >>> 7
  let v944 := v942 ^^^ v943
  let v945 := (w 21).rotateRight 19
  let v946 := (w 21).rotateRight 61
  let v947 := v945 ^^^ v946
  let v948 := (w 21) >>> 6
  let v949 := v947 ^^^ v948
  let v950 := v944 + (w 7)
  let v951 := v950 + (w 16)
  let v952 := v951 + v949
  let v953 := s.e.rotateRight 14
  let v954 := s.e.rotateRight 18
  let v955 := v953 ^^^ v954
  let v956 := s.e.rotateRight 41
  let v957 := v955 ^^^ v956
  let v958 := s.e &&& s.f
  let v959 := s.e ^^^ (-1 : Word)
  let v960 := s.g &&& v959
  let v961 := v958 ||| v960
  let v962 := k
  let v963 := v962 + v952
  let v964 := v963 + s.h
  let v965 := v964 + v961
  let v966 := v965 + v957
  let v967 := s.a.rotateRight 28
  let v968 := s.a.rotateRight 34
  let v969 := v967 ^^^ v968
  let v970 := s.a.rotateRight 39
  let v971 := v969 ^^^ v970
  let v972 := s.a &&& s.b
  let v973 := s.b ^^^ s.c
  let v974 := s.a &&& v973
  let v975 := v974 ^^^ (s.b &&& s.c)
  let v976 := v971 + v975
  let v977 := v966 + s.d
  let v978 := v976 + v966
  E[%940 := .value v940,
    %941 := .value v941,
    %942 := .value v942,
    %943 := .value v943,
    %944 := .value v944,
    %945 := .value v945,
    %946 := .value v946,
    %947 := .value v947,
    %948 := .value v948,
    %949 := .value v949,
    %950 := .value v950,
    %951 := .value v951,
    %952 := .value v952,
    %953 := .value v953,
    %954 := .value v954,
    %955 := .value v955,
    %956 := .value v956,
    %957 := .value v957,
    %958 := .value v958,
    %959 := .value v959,
    %960 := .value v960,
    %961 := .value v961,
    %962 := .value v962,
    %963 := .value v963,
    %964 := .value v964,
    %965 := .value v965,
    %966 := .value v966,
    %967 := .value v967,
    %968 := .value v968,
    %969 := .value v969,
    %970 := .value v970,
    %971 := .value v971,
    %972 := .value v972,
    %973 := .value v973,
    %974 := .value v974,
    %975 := .value v975,
    %976 := .value v976,
    %977 := .value v977,
    %978 := .value v978]

def fullOut23 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v940 := (w 8).rotateRight 1
  let v941 := (w 8).rotateRight 8
  let v942 := v940 ^^^ v941
  let v943 := (w 8) >>> 7
  let v944 := v942 ^^^ v943
  let v945 := (w 21).rotateRight 19
  let v946 := (w 21).rotateRight 61
  let v947 := v945 ^^^ v946
  let v948 := (w 21) >>> 6
  let v949 := v947 ^^^ v948
  let v950 := v944 + (w 7)
  let v951 := v950 + (w 16)
  let v952 := v951 + v949
  let v953 := s.e.rotateRight 14
  let v954 := s.e.rotateRight 18
  let v955 := v953 ^^^ v954
  let v956 := s.e.rotateRight 41
  let v957 := v955 ^^^ v956
  let v958 := s.e &&& s.f
  let v959 := s.e ^^^ (-1 : Word)
  let v960 := s.g &&& v959
  let v961 := v958 ||| v960
  let v962 := k
  let v963 := v962 + v952
  let v964 := v963 + s.h
  let v965 := v964 + v961
  let v966 := v965 + v957
  let v967 := s.a.rotateRight 28
  let v968 := s.a.rotateRight 34
  let v969 := v967 ^^^ v968
  let v970 := s.a.rotateRight 39
  let v971 := v969 ^^^ v970
  let v972 := s.a &&& s.b
  let v973 := s.b ^^^ s.c
  let v974 := s.a &&& v973
  let v975 := v974 ^^^ (s.b &&& s.c)
  let v976 := v971 + v975
  let v977 := v966 + s.d
  let v978 := v976 + v966
  ⟨v978, s.a, s.b, s.c, v977, s.e, s.f, s.g⟩

theorem fullOut23_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut23 s w k = Spec.round s (w 23) k := by
  have hw23 := hw 23 (by decide) (by decide)
  dsimp only [fullOut23, Spec.round]
  rw [hw23]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv23_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 940 E (fullEnv23 E s w k) := by
  unfold fullEnv23
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv23_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv23 E s w k) := by
  exact (fullEnv23_before E s w k).frame (by decide)

theorem full_body23 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready23 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 184#64) 64)
    (hk : state.mem.readAt (kp.add 184#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 740 |>.take 39) state =
      .value (fullEnv23 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv23, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, h.w16, h.w17, h.w18, h.w19, h.w20, h.w21, h.w22, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k23, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready23 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready23 E s w) (hw : ScheduleReady w) :
    Ready24 (fullEnv23 E s w k) (Spec.round s (w 23) k) w := by
  have hb := fullEnv23_before E s w k
  have hout := fullOut23_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv23, fullOut23, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 939 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 900 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 861 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv23, fullOut23, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 938 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 899 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 860 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv23, Spec.round, mlir_env]
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
  · rw [hb.read_val 913 (by decide) (by rfl)]; exact h.w22
  · have hwr := hw 23 (by decide) (by decide)
    simp [fullEnv23, mlir_env]
    rw [hwr]
    simp only [Nat.reduceSub, smallSigma0, smallSigma1]
    ac_rfl

theorem full_step23 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready23 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 740 |>.take 39) state =
      .value (E', state) ∧
      Ready24 E' (Spec.round s (w 23) (constants.toList.getD 23 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 23 0
  have hf := fullEnv23_frame E s w k
  refine ⟨fullEnv23 E s w k,
    full_body23 E state s w kp k h hc (hk 23).1 (hk 23).2,
    full_ready23 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
