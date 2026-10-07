import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 311..336: round 10. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv10 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v511 := s.e.rotateRight 14
  let v512 := s.e.rotateRight 18
  let v513 := v511 ^^^ v512
  let v514 := s.e.rotateRight 41
  let v515 := v513 ^^^ v514
  let v516 := s.e &&& s.f
  let v517 := s.e ^^^ (-1 : Word)
  let v518 := s.g &&& v517
  let v519 := k
  let v520 := v519 + (w 10)
  let v521 := v520 + s.h
  let v522 := v521 + v518
  let v523 := v522 + v516
  let v524 := v523 + v515
  let v525 := s.a.rotateRight 28
  let v526 := s.a.rotateRight 34
  let v527 := v525 ^^^ v526
  let v528 := s.a.rotateRight 39
  let v529 := v527 ^^^ v528
  let v530 := s.a &&& s.b
  let v531 := s.b ^^^ s.c
  let v532 := s.a &&& v531
  let v533 := v532 ^^^ (s.b &&& s.c)
  let v534 := v529 + v533
  let v535 := v524 + s.d
  let v536 := v534 + v524
  E[%511 := .value v511,
    %512 := .value v512,
    %513 := .value v513,
    %514 := .value v514,
    %515 := .value v515,
    %516 := .value v516,
    %517 := .value v517,
    %518 := .value v518,
    %519 := .value v519,
    %520 := .value v520,
    %521 := .value v521,
    %522 := .value v522,
    %523 := .value v523,
    %524 := .value v524,
    %525 := .value v525,
    %526 := .value v526,
    %527 := .value v527,
    %528 := .value v528,
    %529 := .value v529,
    %530 := .value v530,
    %531 := .value v531,
    %532 := .value v532,
    %533 := .value v533,
    %534 := .value v534,
    %535 := .value v535,
    %536 := .value v536]

def fullOut10 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v511 := s.e.rotateRight 14
  let v512 := s.e.rotateRight 18
  let v513 := v511 ^^^ v512
  let v514 := s.e.rotateRight 41
  let v515 := v513 ^^^ v514
  let v516 := s.e &&& s.f
  let v517 := s.e ^^^ (-1 : Word)
  let v518 := s.g &&& v517
  let v519 := k
  let v520 := v519 + (w 10)
  let v521 := v520 + s.h
  let v522 := v521 + v518
  let v523 := v522 + v516
  let v524 := v523 + v515
  let v525 := s.a.rotateRight 28
  let v526 := s.a.rotateRight 34
  let v527 := v525 ^^^ v526
  let v528 := s.a.rotateRight 39
  let v529 := v527 ^^^ v528
  let v530 := s.a &&& s.b
  let v531 := s.b ^^^ s.c
  let v532 := s.a &&& v531
  let v533 := v532 ^^^ (s.b &&& s.c)
  let v534 := v529 + v533
  let v535 := v524 + s.d
  let v536 := v534 + v524
  ⟨v536, s.a, s.b, s.c, v535, s.e, s.f, s.g⟩

theorem fullOut10_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut10 s w k = Spec.round s (w 10) k := by
  dsimp only [fullOut10, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv10_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 511 E (fullEnv10 E s w k) := by
  unfold fullEnv10
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv10_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv10 E s w k) := by
  exact (fullEnv10_before E s w k).frame (by decide)

theorem full_body10 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready10 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 80#64) 64)
    (hk : state.mem.readAt (kp.add 80#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 311 |>.take 26) state =
      .value (fullEnv10 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv10, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k10, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready10 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready10 E s w) (hw : ScheduleReady w) :
    Ready11 (fullEnv10 E s w k) (Spec.round s (w 10) k) w := by
  have hb := fullEnv10_before E s w k
  have hout := fullOut10_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv10, fullOut10, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 510 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 484 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 458 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv10, fullOut10, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 509 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 483 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 457 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv10, Spec.round, mlir_env]
  · rw [hb.read_val 204 (by decide) (by rfl)]; exact h.w0
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

theorem full_step10 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready10 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 311 |>.take 26) state =
      .value (E', state) ∧
      Ready11 E' (Spec.round s (w 10) (constants.toList.getD 10 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 10 0
  have hf := fullEnv10_frame E s w k
  refine ⟨fullEnv10 E s w k,
    full_body10 E state s w kp k h hc (hk 10).1 (hk 10).2,
    full_ready10 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
