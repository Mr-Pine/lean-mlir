import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullRegisters
import SSA.Projects.Agave.Ed25519.Proof.SHA512.Compression.ScalarFullPreservation

/-! Exact original scalar bb4 instructions 337..362: round 11. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
open LeanMLIR.RIR
open Agave.Ed25519.Reduce64.Execution
open Agave.Ed25519.SHA512.Compression.Avx2ExecutionArithmetic
open Spec

def fullEnv11 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) : Env program.Γ :=
  let v537 := s.e.rotateRight 14
  let v538 := s.e.rotateRight 18
  let v539 := v537 ^^^ v538
  let v540 := s.e.rotateRight 41
  let v541 := v539 ^^^ v540
  let v542 := s.e &&& s.f
  let v543 := s.e ^^^ (-1 : Word)
  let v544 := s.g &&& v543
  let v545 := k
  let v546 := v545 + (w 11)
  let v547 := v546 + s.h
  let v548 := v547 + v544
  let v549 := v548 + v542
  let v550 := v549 + v541
  let v551 := s.a.rotateRight 28
  let v552 := s.a.rotateRight 34
  let v553 := v551 ^^^ v552
  let v554 := s.a.rotateRight 39
  let v555 := v553 ^^^ v554
  let v556 := s.a &&& s.b
  let v557 := s.b ^^^ s.c
  let v558 := s.a &&& v557
  let v559 := v558 ^^^ (s.b &&& s.c)
  let v560 := v555 + v559
  let v561 := v550 + s.d
  let v562 := v560 + v550
  E[%537 := .value v537,
    %538 := .value v538,
    %539 := .value v539,
    %540 := .value v540,
    %541 := .value v541,
    %542 := .value v542,
    %543 := .value v543,
    %544 := .value v544,
    %545 := .value v545,
    %546 := .value v546,
    %547 := .value v547,
    %548 := .value v548,
    %549 := .value v549,
    %550 := .value v550,
    %551 := .value v551,
    %552 := .value v552,
    %553 := .value v553,
    %554 := .value v554,
    %555 := .value v555,
    %556 := .value v556,
    %557 := .value v557,
    %558 := .value v558,
    %559 := .value v559,
    %560 := .value v560,
    %561 := .value v561,
    %562 := .value v562]

def fullOut11 (s : Spec.State) (w : Nat → Word) (k : Word) : Spec.State :=
  let v537 := s.e.rotateRight 14
  let v538 := s.e.rotateRight 18
  let v539 := v537 ^^^ v538
  let v540 := s.e.rotateRight 41
  let v541 := v539 ^^^ v540
  let v542 := s.e &&& s.f
  let v543 := s.e ^^^ (-1 : Word)
  let v544 := s.g &&& v543
  let v545 := k
  let v546 := v545 + (w 11)
  let v547 := v546 + s.h
  let v548 := v547 + v544
  let v549 := v548 + v542
  let v550 := v549 + v541
  let v551 := s.a.rotateRight 28
  let v552 := s.a.rotateRight 34
  let v553 := v551 ^^^ v552
  let v554 := s.a.rotateRight 39
  let v555 := v553 ^^^ v554
  let v556 := s.a &&& s.b
  let v557 := s.b ^^^ s.c
  let v558 := s.a &&& v557
  let v559 := v558 ^^^ (s.b &&& s.c)
  let v560 := v555 + v559
  let v561 := v550 + s.d
  let v562 := v560 + v550
  ⟨v562, s.a, s.b, s.c, v561, s.e, s.f, s.g⟩

theorem fullOut11_eq (s : Spec.State) (w : Nat → Word) (k : Word)
    (hw : ScheduleReady w) : fullOut11 s w k = Spec.round s (w 11) k := by
  dsimp only [fullOut11, Spec.round]
  simp only [Nat.reduceSub, bigSigma0, bigSigma1, smallSigma0, smallSigma1, scalar_choice_or, scalar_majority, ← scalar_choose_add]
  congr 1 <;> ac_rfl

theorem fullEnv11_before (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Before 537 E (fullEnv11 E s w k) := by
  unfold fullEnv11
  repeat' (apply Before.write <;> try decide)
  exact Before.refl E _

theorem fullEnv11_frame (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word) :
    Frame E (fullEnv11 E s w k) := by
  exact (fullEnv11_before E s w k).frame (by decide)

theorem full_body11 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer) (k : Word)
    (h : Ready11 E s w) (hc : Constants E kp)
    (hf : Fits state.mem (kp.add 88#64) 64)
    (hk : state.mem.readAt (kp.add 88#64) 64 = k) :
    List.foldlM Instr.run E (program.bb4.body.drop 337 |>.take 26) state =
      .value (fullEnv11 E s w k, state) := by
  try simp only [Pointer.add_zero] at hf hk
  have hadd (a b : Word) : Operation.add {} (.value a) (.value b) = .value (a + b) := by
    simp [Operation.add]
  simp [program.bb4, List.foldlM_cons, List.foldlM_nil, Instr.run,
    fullEnv11, h.a, h.b, h.c, h.d, h.e, h.f, h.g, h.h, h.bc, h.w0, h.w1, h.w2, h.w3, h.w4, h.w5, h.w6, h.w7, h.w8, h.w9, h.w10, h.w11, h.w12, h.w13, h.w14, h.w15, hc.v1, hc.v9, hc.v19, hc.v20, hc.v21, hc.v22, hc.v24, hc.v25, hc.v26, hc.v42, hc.v43, hc.v44, hc.v45, hc.k11, hf, hk,
    Operation.load, Operation.and, Operation.xor, Operation.or, Operation.lshr, hadd,
    fshl50_rotateRight, fshl46_rotateRight, fshl23_rotateRight,
    fshl36_rotateRight, fshl30_rotateRight, fshl25_rotateRight,
    fshl63_rotateRight, fshl56_rotateRight, fshl45_rotateRight, fshl3_rotateRight,
    BinOp.compute, TernOp.compute,
    EffectM.bind_eq, EffectM.pure_eq, mlir_env, mlir_effect, throwUBIf]

theorem full_ready11 (E : Env program.Γ) (s : Spec.State) (w : Nat → Word) (k : Word)
    (h : Ready11 E s w) (hw : ScheduleReady w) :
    Ready12 (fullEnv11 E s w k) (Spec.round s (w 11) k) w := by
  have hb := fullEnv11_before E s w k
  have hout := fullOut11_eq s w k hw
  have ha := congrArg Spec.State.a hout
  have he := congrArg Spec.State.e hout
  constructor
  · simpa [fullEnv11, fullOut11, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value ha
  · rw [hb.read_val 536 (by decide) (by rfl)]; exact h.a
  · rw [hb.read_val 510 (by decide) (by rfl)]; exact h.b
  · rw [hb.read_val 484 (by decide) (by rfl)]; exact h.c
  · simpa [fullEnv11, fullOut11, mlir_env] using congrArg LeanMLIR.RIR.PoisonOr.value he
  · rw [hb.read_val 535 (by decide) (by rfl)]; exact h.e
  · rw [hb.read_val 509 (by decide) (by rfl)]; exact h.f
  · rw [hb.read_val 483 (by decide) (by rfl)]; exact h.g
  · simp [fullEnv11, Spec.round, mlir_env]
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

theorem full_step11 (E : Env program.Γ) (state : GlobalState)
    (s : Spec.State) (w : Nat → Word) (kp : Pointer)
    (h : Ready11 E s w) (hc : Constants E kp)
    (hw : ScheduleReady w) (hk : KRead state.mem kp) :
    ∃ E', List.foldlM Instr.run E (program.bb4.body.drop 337 |>.take 26) state =
      .value (E', state) ∧
      Ready12 E' (Spec.round s (w 11) (constants.toList.getD 11 0)) w ∧
      Constants E' kp ∧ Frame E E' := by
  let k := constants.toList.getD 11 0
  have hf := fullEnv11_frame E s w k
  refine ⟨fullEnv11 E s w k,
    full_body11 E state s w kp k h hc (hk 11).1 (hk 11).2,
    full_ready11 E s w k h hw, hc.of_frame hf, hf⟩

end Agave.Ed25519.SHA512.Execution.Dispatch.ScalarFull
